import asyncio
import uuid
from collections.abc import Generator
from concurrent.futures import Future, ThreadPoolExecutor
from contextlib import asynccontextmanager
from dataclasses import dataclass, field

import click
from fastapi import BackgroundTasks, FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel

from .config import CombinedConfig
from .logging import logger
from .scheduler import CourseInstance, Scheduler

# Lock for generator initialization
generator_locks: dict[str, asyncio.Lock] = {}

# Global thread pool executor for Z3 operations
z3_executor: ThreadPoolExecutor = ThreadPoolExecutor(max_workers=16, thread_name_prefix="z3-solver")


# Data models for API requests/responses
SubmitRequest = CombinedConfig


class HealthCheck(BaseModel):
    """
    Health check response model.

    **Fields:**
    - status: Health status of the service
    - active_sessions: Number of active schedule generation sessions
    """

    status: str
    active_sessions: int


class SubmitResponse(BaseModel):
    """
    Response model for schedule submission requests.

    **Fields:**
    - schedule_id: Unique identifier for the generated schedule session
    - endpoint: URL endpoint to access the schedule
    """

    schedule_id: str
    endpoint: str


class MessageResponse(BaseModel):
    """
    Generic message response model.

    **Fields:**
    - message: Response message text
    """

    message: str


class GenerateAllResponse(BaseModel):
    """
    Response model for generate-all schedule requests.

    **Fields:**
    - message: Status message about the generation process
    - current_count: Number of schedules already generated
    - target_count: Target number of schedules to generate
    """

    message: str
    current_count: int
    target_count: int


class ScheduleResponse(BaseModel):
    """
    Response model for schedule retrieval requests.

    **Fields:**
    - schedule_id: Unique identifier for the schedule session
    - schedule: The generated schedule as a list of course instances
    - index: Index of this schedule in the generation sequence
    - total_generated: Total number of schedules generated so far
    """

    schedule_id: str
    schedule: list[dict]
    index: int
    total_generated: int


class ScheduleDetailsResponse(CombinedConfig):
    """
    Response model for schedule details requests.

    Inherits all fields from CombinedConfig and adds:

    **Fields:**
    - schedule_id: Unique identifier for the schedule session
    - total_generated: Total number of schedules generated
    """

    schedule_id: str
    total_generated: int


class ScheduleCountResponse(BaseModel):
    """
    Response model for schedule count requests.

    **Fields:**
    - schedule_id: Unique identifier for the schedule session
    - current_count: Number of schedules currently generated
    - limit: Maximum number of schedules to generate
    - is_complete: Whether all schedules have been generated
    """

    schedule_id: str
    current_count: int
    limit: int
    is_complete: bool


class ErrorResponse(BaseModel):
    """
    Error response model for API errors.

    **Fields:**
    - error: Error type or code
    - message: Detailed error message
    """

    error: str
    message: str


@dataclass
class ScheduleSession:
    """Represents an active schedule generation session."""

    scheduler: Scheduler | None
    scheduler_future: Future[Scheduler | None] | None
    generator: Generator[list[CourseInstance], None, None] | None
    full_config: CombinedConfig
    generated_schedules: list[list[dict]]
    current_index: int = 0
    background_tasks: list[asyncio.Task] = field(default_factory=list)


# Global storage for active sessions
schedule_sessions: dict[str, ScheduleSession] = {}


def cleanup_session(schedule_id: str):
    """
    Remove a session from memory and clean up associated resources.

    **Args:**
    - schedule_id: Unique identifier for the schedule session to clean up
    """
    logger.debug(f"Cleaning up session {schedule_id}")
    logger.debug(f"Active sessions before cleanup: {list(schedule_sessions.keys())}")

    if schedule_id in schedule_sessions:
        session = schedule_sessions[schedule_id]

        assert session.background_tasks is not None

        # Cancel all background tasks
        for task in session.background_tasks:
            if not task.done():
                task.cancel()
                logger.debug(f"Cancelled background task for session {schedule_id}")

        del schedule_sessions[schedule_id]
        logger.debug(f"Removed session {schedule_id} from schedule_sessions")
    else:
        logger.warning(f"Session {schedule_id} not found in schedule_sessions during cleanup")

    # Clean up the lock too
    if schedule_id in generator_locks:
        del generator_locks[schedule_id]
        logger.debug(f"Removed lock for session {schedule_id}")

    logger.debug(f"Active sessions after cleanup: {list(schedule_sessions.keys())}")
    logger.info(f"Cleaned up session {schedule_id}")


async def ensure_scheduler_initialized(session_id: str, session: ScheduleSession):
    """
    Ensure the scheduler is initialized for a session.

    **Args:**
    - session_id: Unique identifier for the schedule session
    - session: The ScheduleSession object to initialize
    """
    if session.scheduler is not None:
        return
    assert session.scheduler_future is not None
    # Wrap the Future in an asyncio.Future so it can be awaited
    session.scheduler = await asyncio.wrap_future(session.scheduler_future)


async def ensure_generator_initialized(session_id: str, session: ScheduleSession):
    """
    Ensure the generator is initialized for a session.

    **Args:**
    - session_id: Unique identifier for the schedule session
    - session: The ScheduleSession object to initialize the generator for

    **Raises:**
    - HTTPException: If generator initialization fails or times out
    """
    if session.generator is not None:
        return
    if session.scheduler is None:
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
            session.generator = await asyncio.wrap_future(z3_executor.submit(session.scheduler.get_models))
            logger.debug(f"Initialized generator for session {session_id}")
        except asyncio.CancelledError:
            logger.warning(f"Generator initialization was cancelled for session {session_id}")
            raise HTTPException(status_code=408, detail="Request timeout")
        except Exception as e:
            logger.error(f"Failed to initialize generator for session {session_id}: {e}")
            raise HTTPException(status_code=500, detail=f"Generator initialization failed: {str(e)}")


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


@app.post("/submit", response_model=SubmitResponse)
async def submit_schedule(request: SubmitRequest):
    """Submit a new schedule generation request."""
    try:
        # Create scheduler in thread pool to avoid blocking
        try:
            scheduler_future = z3_executor.submit(Scheduler, request)
        except Exception as e:
            logger.error(f"Failed to create scheduler: {e}")
            raise HTTPException(status_code=500, detail=f"Scheduler creation failed: {str(e)}")

        # Generate unique ID for this session
        schedule_id = str(uuid.uuid4())

        # Store session
        schedule_sessions[schedule_id] = ScheduleSession(
            scheduler=None,
            scheduler_future=scheduler_future,  # type: ignore
            generator=None,
            full_config=request,
            generated_schedules=[],
        )

        logger.debug(f"Created new schedule session {schedule_id}")

        return SubmitResponse(schedule_id=schedule_id, endpoint=f"/schedules/{schedule_id}")

    except HTTPException:
        # Re-raise HTTP exceptions
        raise
    except Exception as e:
        logger.error(f"Error creating schedule session: {e}")
        raise HTTPException(status_code=400, detail=f"Invalid configuration: {str(e)}")


@app.get("/schedules/{schedule_id}/details", response_model=ScheduleDetailsResponse)
async def get_schedule_details(schedule_id: str):
    """Get details about a schedule session."""
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]

    await ensure_scheduler_initialized(schedule_id, session)

    return ScheduleDetailsResponse(
        schedule_id=schedule_id,
        **session.full_config.model_dump(),
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
    if len(session.generated_schedules) >= session.full_config.limit:
        raise HTTPException(status_code=400, detail=f"All {session.full_config.limit} schedules have been generated")

    try:
        # Get the next model from the scheduler in thread pool
        try:
            assert session.generator is not None
            generator = session.generator
            model = await asyncio.wrap_future(z3_executor.submit(lambda: next(generator)))
        except asyncio.CancelledError:
            logger.warning(f"Schedule generation was cancelled for session {schedule_id}")
            raise HTTPException(status_code=408, detail="Request timeout")
        except StopIteration:
            logger.info(f"No more schedules available for session {schedule_id}")
            raise HTTPException(status_code=400, detail="No more schedules available")
        except Exception as e:
            # Check if this is a StopIteration that was wrapped by the thread pool
            if "StopIteration" in str(e):
                logger.info(f"No more schedules available for session {schedule_id}")
                raise HTTPException(status_code=400, detail="No more schedules available")
            logger.error(f"Failed to generate schedule for session {schedule_id}: {e}")
            raise HTTPException(status_code=500, detail=f"Schedule generation failed: {str(e)}")

        # Convert model to JSON format with transformation
        schedule_data = [course_instance.model_dump(by_alias=True, exclude_none=True) for course_instance in model]

        # Store the generated schedule
        session.generated_schedules.append(schedule_data)
        current_index = len(session.generated_schedules) - 1

        logger.debug(f"Generated schedule {current_index + 1} for session {schedule_id}")

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
        raise HTTPException(status_code=500, detail=f"Error generating schedule: {str(e)}")


@app.post("/schedules/{schedule_id}/generate_all", response_model=GenerateAllResponse)
async def generate_all_schedules(schedule_id: str):
    """Generate all remaining schedules for a session asynchronously."""
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]

    await ensure_scheduler_initialized(schedule_id, session)
    await ensure_generator_initialized(schedule_id, session)

    # Check if we've already generated all schedules
    if len(session.generated_schedules) >= session.full_config.limit:
        raise HTTPException(
            status_code=400,
            detail=f"All {session.full_config.limit} schedules have already been generated",
        )

    # Start background task to generate all remaining schedules
    async def generate_all_background():
        try:
            remaining = session.full_config.limit - len(session.generated_schedules)
            logger.info(f"Starting background generation of {remaining} schedules for session {schedule_id}")

            for i in range(remaining):
                try:
                    current_task = asyncio.current_task()
                    # Check if we've been cancelled
                    if current_task is not None and current_task.cancelled():
                        logger.debug(f"Background generation cancelled for session {schedule_id}")
                        return

                    assert session.generator is not None
                    generator = session.generator
                    model = await asyncio.wrap_future(z3_executor.submit(lambda: next(generator)))

                    # Convert model to JSON format with transformation
                    schedule_data = []
                    for course_instance in model:
                        schedule_data.append(course_instance.model_dump(by_alias=True, exclude_none=True))

                    # Store the generated schedule immediately
                    session.generated_schedules.append(schedule_data)
                    n = len(session.generated_schedules)
                    logger.debug(f"Generated schedule {n} for session {schedule_id}")

                except StopIteration:
                    logger.info(f"No more schedules available for session {schedule_id}")
                    session.full_config.limit = len(session.generated_schedules)
                    break
                except asyncio.CancelledError:
                    logger.debug(f"Background generation cancelled for session {schedule_id}")
                    return
                except Exception as e:
                    count = len(session.generated_schedules) + 1
                    logger.error(f"Failed to generate schedule {count} for session {schedule_id}: {e}")
                    break
            n = len(session.generated_schedules)
            logger.info(f"Completed background generation for session {schedule_id}. Total generated: {n}")

        except asyncio.CancelledError:
            logger.debug(f"Background generation cancelled for session {schedule_id}")
        except Exception as e:
            logger.error(f"Background generation failed for session {schedule_id}: {e}")

    # Start the background task and store it
    background_task = asyncio.create_task(generate_all_background())
    session.background_tasks.append(background_task)

    return GenerateAllResponse(
        message=f"Started generating all remaining schedules for session {schedule_id}",
        current_count=len(session.generated_schedules),
        target_count=session.full_config.limit,
    )


@app.get("/schedules/{schedule_id}/count", response_model=ScheduleCountResponse)
async def get_schedule_count(schedule_id: str):
    """Get the current count of generated schedules for a session."""
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]

    return ScheduleCountResponse(
        schedule_id=schedule_id,
        current_count=len(session.generated_schedules),
        limit=session.full_config.limit,
        is_complete=len(session.generated_schedules) >= session.full_config.limit,
    )


@app.get("/schedules/{schedule_id}/index/{index}", response_model=ScheduleResponse)
async def get_schedule_by_index(schedule_id: str, index: int):
    """Get a previously generated schedule by index."""
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]
    n = len(session.generated_schedules)
    if index < 0 or index >= n:
        raise HTTPException(
            status_code=404,
            detail=f"Schedule index {index} not found. Available indices: 0-{n - 1}",
        )

    return ScheduleResponse(
        schedule_id=schedule_id,
        schedule=session.generated_schedules[index],
        index=index,
        total_generated=len(session.generated_schedules),
    )


@app.delete("/schedules/{schedule_id}/delete", response_model=MessageResponse)
async def delete_schedule_session(schedule_id: str, background_tasks: BackgroundTasks):
    """Delete a schedule session."""
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    # Schedule cleanup in background
    background_tasks.add_task(cleanup_session, schedule_id)

    return MessageResponse(message=f"Schedule session {schedule_id} marked for deletion")


@app.post("/schedules/{schedule_id}/cleanup", response_model=MessageResponse)
async def cleanup_schedule_session(schedule_id: str):
    """Immediate cleanup of a schedule session."""
    if schedule_id in schedule_sessions:
        cleanup_session(schedule_id)

    return MessageResponse(message=f"Schedule session {schedule_id} cleaned up")


@app.get("/health", response_model=HealthCheck)
async def health_check():
    """Health check endpoint."""
    return HealthCheck(status="healthy", active_sessions=len(schedule_sessions))


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

    # Update thread pool size if different from default
    global z3_executor
    if workers != 16:
        z3_executor.shutdown(wait=True)
        z3_executor = ThreadPoolExecutor(max_workers=workers, thread_name_prefix="z3-solver")

    logger.info(f"Starting server on {host}:{port} with log level {log_level} and {workers} Z3 workers")

    uvicorn.run(app, host=host, port=port, log_level=log_level, reload=False)


if __name__ == "__main__":
    main()
