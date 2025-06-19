import json
import uuid
import asyncio
from typing import Dict, Any
from dataclasses import dataclass
from contextlib import asynccontextmanager
from concurrent.futures import ThreadPoolExecutor, Future

import click
from fastapi import FastAPI, HTTPException, BackgroundTasks
from fastapi.responses import JSONResponse
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel

from .config import SchedulerConfig, TimeSlotConfig
from .scheduler import Scheduler
from .logging import logger

# Lock for generator initialization
generator_locks: Dict[str, asyncio.Lock] = {}


# Data models for API requests/responses
class SubmitRequest(BaseModel):
    config: Dict[str, Any]
    time_slot_config: Dict[str, Any]
    limit: int = 10
    optimize: bool = True


class ScheduleResponse(BaseModel):
    schedule_id: str
    schedule: list[Dict[str, Any]]
    index: int
    total_generated: int


class ScheduleDetails(BaseModel):
    schedule_id: str
    config: Dict[str, Any]
    time_slot_config: Dict[str, Any]
    limit: int
    optimize: bool
    total_generated: int


class ErrorResponse(BaseModel):
    error: str
    message: str


@dataclass
class ScheduleSession:
    """Represents an active schedule generation session."""

    scheduler: None | Scheduler
    scheduler_future: None | Future[Scheduler]
    generator: None | Any
    config: Dict[str, Any]
    time_slot_config: Dict[str, Any]
    limit: int
    optimize: bool
    generated_schedules: list[list[Dict[str, Any]]]
    current_index: int = 0


# Global storage for active sessions
schedule_sessions: Dict[str, ScheduleSession] = {}


def cleanup_session(schedule_id: str):
    """Remove a session from memory."""
    if schedule_id in schedule_sessions:
        del schedule_sessions[schedule_id]
        # Clean up the lock too
        if schedule_id in generator_locks:
            del generator_locks[schedule_id]
        logger.info(f"Cleaned up session {schedule_id}")


async def ensure_scheduler_initialized(session_id: str, session: ScheduleSession):
    """Ensure the scheduler is initialized for a session."""
    if session.scheduler is not None:
        return

    # Wrap the Future in an asyncio.Future so it can be awaited
    session.scheduler = await asyncio.wrap_future(session.scheduler_future)


async def ensure_generator_initialized(session_id: str, session: ScheduleSession):
    """Ensure the generator is initialized for a session."""
    if session.generator is not None:
        return

    # Create lock for this session if it doesn't exist
    if session_id not in generator_locks:
        generator_locks[session_id] = asyncio.Lock()

    async with generator_locks[session_id]:
        # Double-check after acquiring lock
        if session.generator is not None:
            return

        # Initialize generator in thread pool
        try:
            session.generator = await asyncio.wrap_future(
                z3_executor.submit(
                    session.scheduler.get_models,
                    limit=session.limit,
                    optimize=session.optimize,
                )
            )
            logger.info(f"Initialized generator for session {session_id}")
        except asyncio.CancelledError:
            logger.warning(
                f"Generator initialization was cancelled for session {session_id}"
            )
            raise HTTPException(status_code=408, detail="Request timeout")
        except Exception as e:
            logger.error(
                f"Failed to initialize generator for session {session_id}: {e}"
            )
            raise HTTPException(
                status_code=500, detail=f"Generator initialization failed: {str(e)}"
            )


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Application lifespan manager for cleanup."""
    yield
    # Cleanup all sessions on shutdown
    for session_id in list(schedule_sessions.keys()):
        cleanup_session(session_id)
    # Shutdown thread pool
    z3_executor.shutdown(wait=True)


app = FastAPI(
    title="Course Scheduler API",
    description="HTTP API for generating course schedules using constraint satisfaction solving",
    version="1.0.0",
    lifespan=lifespan,
)

# Add CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # Allows all origins
    allow_credentials=True,
    allow_methods=["*"],  # Allows all methods
    allow_headers=["*"],  # Allows all headers
)


@app.post("/submit", response_model=Dict[str, str])
async def submit_schedule(request: SubmitRequest):
    """Submit a new schedule generation request."""
    try:
        # Parse configurations
        config = SchedulerConfig(**request.config)
        time_slot_config = TimeSlotConfig(**request.time_slot_config)

        # Create scheduler in thread pool to avoid blocking
        try:
            scheduler_future = z3_executor.submit(Scheduler, config, time_slot_config)
        except Exception as e:
            logger.error(f"Failed to create scheduler: {e}")
            raise HTTPException(
                status_code=500, detail=f"Scheduler creation failed: {str(e)}"
            )

        # Generate unique ID for this session
        schedule_id = str(uuid.uuid4())

        # Store session
        schedule_sessions[schedule_id] = ScheduleSession(
            scheduler=None,
            scheduler_future=scheduler_future,
            generator=None,
            config=request.config,
            time_slot_config=request.time_slot_config,
            limit=request.limit,
            optimize=request.optimize,
            generated_schedules=[],
        )

        logger.info(f"Created new schedule session {schedule_id}")

        return {"schedule_id": schedule_id, "endpoint": f"/schedules/{schedule_id}"}

    except HTTPException:
        # Re-raise HTTP exceptions
        raise
    except Exception as e:
        logger.error(f"Error creating schedule session: {e}")
        raise HTTPException(status_code=400, detail=f"Invalid configuration: {str(e)}")


@app.get("/schedules/{schedule_id}/details", response_model=ScheduleDetails)
async def get_schedule_details(schedule_id: str):
    """Get details about a schedule session."""
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]

    await ensure_scheduler_initialized(schedule_id, session)

    return ScheduleDetails(
        schedule_id=schedule_id,
        config=session.config,
        time_slot_config=session.time_slot_config,
        limit=session.limit,
        optimize=session.optimize,
        total_generated=len(session.generated_schedules),
    )


@app.post("/schedules/{schedule_id}/next", response_model=ScheduleResponse)
async def get_next_schedule(schedule_id: str):
    """Get the next generated schedule."""
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]

    await ensure_scheduler_initialized(schedule_id, session)
    await ensure_generator_initialized(schedule_id, session)

    # Check if we've already generated all schedules
    if len(session.generated_schedules) >= session.limit:
        raise HTTPException(
            status_code=400, detail=f"All {session.limit} schedules have been generated"
        )

    try:
        # Get the next model from the scheduler in thread pool
        try:
            model = await asyncio.wrap_future(
                z3_executor.submit(lambda: next(session.generator))
            )
        except asyncio.CancelledError:
            logger.warning(
                f"Schedule generation was cancelled for session {schedule_id}"
            )
            raise HTTPException(status_code=408, detail="Request timeout")
        except StopIteration:
            logger.info(f"No more schedules available for session {schedule_id}")
            raise HTTPException(status_code=400, detail="No more schedules available")
        except Exception as e:
            # Check if this is a StopIteration that was wrapped by the thread pool
            if "StopIteration" in str(e):
                logger.info(f"No more schedules available for session {schedule_id}")
                raise HTTPException(
                    status_code=400, detail="No more schedules available"
                )
            logger.error(f"Failed to generate schedule for session {schedule_id}: {e}")
            raise HTTPException(
                status_code=500, detail=f"Schedule generation failed: {str(e)}"
            )

        # Convert model to JSON format with transformation
        schedule_data = [
            c.instance(model).__json__() for c in session.scheduler.courses
        ]

        # Store the generated schedule
        session.generated_schedules.append(schedule_data)
        current_index = len(session.generated_schedules) - 1

        logger.info(f"Generated schedule {current_index + 1} for session {schedule_id}")

        return ScheduleResponse(
            schedule_id=schedule_id,
            schedule=schedule_data,
            index=current_index,
            total_generated=len(session.generated_schedules),
        )

    except HTTPException:
        # Re-raise HTTP exceptions
        raise
    except Exception as e:
        logger.error(f"Error generating next schedule for {schedule_id}: {e}")
        raise HTTPException(
            status_code=500, detail=f"Error generating schedule: {str(e)}"
        )


@app.get("/schedules/{schedule_id}/index/{index}", response_model=ScheduleResponse)
async def get_schedule_by_index(schedule_id: str, index: int):
    """Get a previously generated schedule by index."""
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]

    if index < 0 or index >= len(session.generated_schedules):
        raise HTTPException(
            status_code=404,
            detail=f"Schedule index {index} not found. Available indices: 0-{len(session.generated_schedules) - 1}",
        )

    return ScheduleResponse(
        schedule_id=schedule_id,
        schedule=session.generated_schedules[index],
        index=index,
        total_generated=len(session.generated_schedules),
    )


@app.delete("/schedules/{schedule_id}/delete")
async def delete_schedule_session(schedule_id: str, background_tasks: BackgroundTasks):
    """Delete a schedule session."""
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    # Schedule cleanup in background
    background_tasks.add_task(cleanup_session, schedule_id)

    logger.info(f"Marked session {schedule_id} for deletion")
    return {"message": f"Schedule session {schedule_id} marked for deletion"}


@app.get("/health")
async def health_check():
    """Health check endpoint."""
    return {"status": "healthy", "active_sessions": len(schedule_sessions)}


@click.command()
@click.option("--port", "-p", default=8000, help="Port to run the server on", type=int)
@click.option(
    "--log-level",
    "-l",
    default="info",
    type=click.Choice(["debug", "info", "warning", "error", "critical"]),
    help="Log level for the server",
)
@click.option("--host", "-h", default="0.0.0.0", help="Host to bind the server to")
@click.option("--workers", "-w", default=16, help="Number of worker threads", type=int)
def main(port: int, log_level: str, host: str, workers: int):
    """Run the Course Scheduler HTTP API server."""
    import uvicorn

    # Update thread pool size
    global z3_executor
    z3_executor = ThreadPoolExecutor(
        max_workers=workers, thread_name_prefix="z3-solver"
    )

    logger.info(
        f"Starting server on {host}:{port} with log level {log_level} and {workers} Z3 workers"
    )

    uvicorn.run(app, host=host, port=port, log_level=log_level, reload=False)


if __name__ == "__main__":
    main()
