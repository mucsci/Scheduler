"""HTTP-level ASGI integration tests for session safety and serialization."""

import asyncio
import threading
import time
from concurrent.futures import ThreadPoolExecutor

import httpx
import pytest

from scheduler import CombinedConfig, Scheduler
from scheduler import server as server_module
from scheduler.server import ApiLimits, ScheduleSession, app, cleanup_session
from tests.scenario_builders import config_from, minimal_config_data, two_course_config_data

pytestmark = pytest.mark.integration


@pytest.fixture(autouse=True)
def clean_api_sessions():
    for schedule_id in list(server_module.schedule_sessions):
        cleanup_session(schedule_id)
    yield
    for schedule_id in list(server_module.schedule_sessions):
        cleanup_session(schedule_id)


def _run(coro):
    return asyncio.run(coro)


def _client() -> httpx.AsyncClient:
    return httpx.AsyncClient(
        transport=httpx.ASGITransport(app=app, raise_app_exceptions=False),
        base_url="http://scheduler.test",
    )


def test_http_session_workflow_covers_details_generation_audit_and_cleanup(
    minimal_combined_config: CombinedConfig,
) -> None:
    async def workflow() -> None:
        async with _client() as client:
            submitted = await client.post("/submit", json=minimal_combined_config.model_dump(mode="json"))
            assert submitted.status_code == 200
            schedule_id = submitted.json()["schedule_id"]

            details = await client.get(f"/schedules/{schedule_id}/details")
            assert details.status_code == 200
            assert details.json()["schedule_id"] == schedule_id

            generated = await client.post(f"/schedules/{schedule_id}/next")
            assert generated.status_code == 200
            assert generated.json()["index"] == 0

            count = await client.get(f"/schedules/{schedule_id}/count")
            indexed = await client.get(f"/schedules/{schedule_id}/index/0")
            audited = await client.get(f"/schedules/{schedule_id}/audit/0")
            status = await client.get(f"/schedules/{schedule_id}/status")
            assert count.json()["current_count"] == 1
            assert indexed.json()["schedule"] == generated.json()["schedule"]
            assert audited.json()["is_valid"] is True
            assert status.json()["known_distinct_schedules"] == 1

            deleted = await client.delete(f"/schedules/{schedule_id}/delete")
            assert deleted.status_code == 200
            assert schedule_id not in server_module.schedule_sessions

    _run(workflow())


def test_http_concurrent_next_requests_are_serialized() -> None:
    config = config_from(two_course_config_data())

    async def workflow() -> None:
        async with _client() as client:
            submitted = await client.post("/submit", json=config.model_dump(mode="json"))
            schedule_id = submitted.json()["schedule_id"]
            responses = await asyncio.gather(
                client.post(f"/schedules/{schedule_id}/next"),
                client.post(f"/schedules/{schedule_id}/next"),
            )
            assert [response.status_code for response in responses] == [200, 200]
            assert {response.json()["index"] for response in responses} == {0, 1}
            assert len(server_module.schedule_sessions[schedule_id].generated_schedules) == 2

    _run(workflow())


def test_cancelled_advance_finishes_atomic_storage_before_releasing_lock() -> None:
    config = config_from(two_course_config_data())
    scheduler = Scheduler(config)
    model = next(scheduler.get_models())
    started = threading.Event()
    release = threading.Event()

    def slow_generator():
        started.set()
        release.wait(timeout=5)
        yield model
        yield model

    session = ScheduleSession(
        scheduler=scheduler,
        scheduler_future=None,
        generator=slow_generator(),
        full_config=config,
        generated_schedules=[],
    )

    async def workflow() -> None:
        advance = asyncio.create_task(server_module._advance_session("cancelled", session))
        while not started.is_set():
            await asyncio.sleep(0)
        advance.cancel()
        release.set()
        with pytest.raises(asyncio.CancelledError):
            await advance

        assert not session.generation_lock.locked()
        assert len(session.generated_schedules) == 1
        assert len(session.generated_models) == 1
        second = await server_module._advance_session("cancelled", session)
        assert second.index == 1

    _run(workflow())


def test_http_background_generation_conflicts_with_next_and_generate_all(monkeypatch) -> None:
    config = config_from(two_course_config_data())
    started = asyncio.Event()
    release = asyncio.Event()
    real_advance = server_module._advance_session

    async def slow_advance(schedule_id, session, **kwargs):
        started.set()
        await release.wait()
        return await real_advance(schedule_id, session, **kwargs)

    monkeypatch.setattr(server_module, "_advance_session", slow_advance)

    async def workflow() -> None:
        async with _client() as client:
            submitted = await client.post("/submit", json=config.model_dump(mode="json"))
            schedule_id = submitted.json()["schedule_id"]
            background = await client.post(f"/schedules/{schedule_id}/generate_all")
            assert background.status_code == 200
            await asyncio.wait_for(started.wait(), timeout=2)

            next_response, competing_background = await asyncio.gather(
                client.post(f"/schedules/{schedule_id}/next"),
                client.post(f"/schedules/{schedule_id}/generate_all"),
            )
            assert next_response.status_code == 409
            assert competing_background.status_code == 409

            release.set()
            task = server_module.schedule_sessions[schedule_id].background_task
            assert task is not None
            await task

    _run(workflow())


def test_http_exhaustion_is_safe_and_generate_all_rejects_terminal_session() -> None:
    data = minimal_config_data()
    data["limit"] = 2
    data["time_slot_config"]["classes"][0]["start_time"] = "08:00"
    config = config_from(data)

    async def workflow() -> None:
        async with _client() as client:
            submitted = await client.post("/submit", json=config.model_dump(mode="json"))
            schedule_id = submitted.json()["schedule_id"]
            assert (await client.post(f"/schedules/{schedule_id}/next")).status_code == 200
            exhausted = await client.post(f"/schedules/{schedule_id}/next")
            assert exhausted.status_code == 400
            status = (await client.get(f"/schedules/{schedule_id}/status")).json()
            assert status["completion_reason"] == "solution_space_exhausted"
            assert status["enumeration_scope"] == "exhausted"
            assert (await client.post(f"/schedules/{schedule_id}/generate_all")).status_code == 400

    _run(workflow())


def test_foreground_next_rechecks_background_conflict_after_lock_wait() -> None:
    config = config_from(two_course_config_data())

    async def workflow() -> None:
        submitted = await server_module.submit_schedule(config)
        session = server_module.schedule_sessions[submitted.schedule_id]
        await server_module.ensure_scheduler_initialized(submitted.schedule_id, session)
        await server_module.ensure_generator_initialized(submitted.schedule_id, session)
        await session.generation_lock.acquire()
        foreground = asyncio.create_task(server_module.get_next_schedule(submitted.schedule_id))
        await asyncio.sleep(0)
        await server_module.generate_all_schedules(submitted.schedule_id)
        session.generation_lock.release()
        result = await asyncio.gather(foreground, return_exceptions=True)
        assert isinstance(result[0], server_module.HTTPException)
        assert result[0].status_code == 409
        assert session.background_task is not None
        await session.background_task

    _run(workflow())


def test_session_reports_solver_timeout_as_indeterminate() -> None:
    scheduler = Scheduler(config_from(minimal_config_data()))
    scheduler._solver._enumeration_completion_reason = "solver_timeout"

    def empty_generator():
        if False:
            yield []

    session = ScheduleSession(
        scheduler=scheduler,
        scheduler_future=None,
        generator=empty_generator(),
        full_config=config_from(minimal_config_data()),
        generated_schedules=[],
    )

    async def workflow() -> None:
        with pytest.raises(server_module.HTTPException) as error:
            await server_module._advance_session("timed-out", session)
        assert error.value.status_code == 400

    _run(workflow())
    response = server_module._session_diagnostic_response("timed-out", session)
    assert response.completion_reason == "solver_timeout"
    assert response.enumeration_scope == "indeterminate"


def test_http_cleanup_cancels_queued_scheduler_initialization(monkeypatch) -> None:
    custom_executor = ThreadPoolExecutor(max_workers=1)
    blocker_started = threading.Event()
    release_blocker = threading.Event()

    def block_worker() -> None:
        blocker_started.set()
        release_blocker.wait(timeout=5)

    custom_executor.submit(block_worker)
    assert blocker_started.wait(timeout=2)
    monkeypatch.setattr(server_module, "z3_executor", custom_executor)

    async def workflow() -> None:
        async with _client() as client:
            submitted = await client.post("/submit", json=config_from(minimal_config_data()).model_dump(mode="json"))
            schedule_id = submitted.json()["schedule_id"]
            future = server_module.schedule_sessions[schedule_id].scheduler_future
            assert future is not None and not future.running()

            cleaned = await client.post(f"/schedules/{schedule_id}/cleanup")
            assert cleaned.status_code == 200
            assert future.cancelled()
            assert schedule_id not in server_module.schedule_sessions

    try:
        _run(workflow())
    finally:
        release_blocker.set()
        custom_executor.shutdown(wait=True)


def test_cancelled_initialization_wait_does_not_poison_session(monkeypatch) -> None:
    custom_executor = ThreadPoolExecutor(max_workers=1)
    blocker_started = threading.Event()
    release_blocker = threading.Event()

    def block_worker() -> None:
        blocker_started.set()
        release_blocker.wait(timeout=5)

    custom_executor.submit(block_worker)
    assert blocker_started.wait(timeout=2)
    monkeypatch.setattr(server_module, "z3_executor", custom_executor)
    config = config_from(minimal_config_data())
    scheduler_future = custom_executor.submit(Scheduler, config)
    session = ScheduleSession(
        scheduler=None,
        scheduler_future=scheduler_future,
        generator=None,
        full_config=config,
        generated_schedules=[],
    )

    async def workflow() -> None:
        initializing = asyncio.create_task(server_module.ensure_scheduler_initialized("shielded", session))
        await asyncio.sleep(0)
        initializing.cancel()
        with pytest.raises(asyncio.CancelledError):
            await initializing
        assert not scheduler_future.cancelled()

        release_blocker.set()
        await server_module.ensure_scheduler_initialized("shielded", session)
        assert session.scheduler is not None

    try:
        _run(workflow())
    finally:
        release_blocker.set()
        custom_executor.shutdown(wait=True)


def test_http_failed_scheduler_initialization_removes_session(monkeypatch) -> None:
    def fail_scheduler(*args, **kwargs):
        raise RuntimeError("intentional initialization failure")

    monkeypatch.setattr(server_module, "Scheduler", fail_scheduler)

    async def workflow() -> None:
        async with _client() as client:
            submitted = await client.post("/submit", json=config_from(minimal_config_data()).model_dump(mode="json"))
            schedule_id = submitted.json()["schedule_id"]
            details = await client.get(f"/schedules/{schedule_id}/details")
            assert details.status_code == 422
            assert "intentional initialization failure" in details.json()["detail"]
            assert schedule_id not in server_module.schedule_sessions

    _run(workflow())


def test_lifespan_reaper_removes_expired_idle_session(monkeypatch) -> None:
    custom_executor = ThreadPoolExecutor(max_workers=1)
    monkeypatch.setattr(server_module, "z3_executor", custom_executor)
    monkeypatch.setattr(server_module, "API_LIMITS", ApiLimits(session_ttl_seconds=1))
    config = config_from(minimal_config_data())
    schedule_id = "expired-session"
    server_module.schedule_sessions[schedule_id] = ScheduleSession(
        scheduler=None,
        scheduler_future=None,
        generator=None,
        full_config=config,
        generated_schedules=[],
        last_accessed_at=time.monotonic() - 2,
    )

    async def workflow() -> None:
        async with server_module.lifespan(app):
            await asyncio.sleep(1.1)
            assert schedule_id not in server_module.schedule_sessions

    _run(workflow())


def test_expiry_preserves_foreground_generation_lock(monkeypatch) -> None:
    monkeypatch.setattr(server_module, "API_LIMITS", ApiLimits(session_ttl_seconds=1))
    config = config_from(minimal_config_data())
    schedule_id = "active-foreground-session"
    session = ScheduleSession(
        scheduler=None,
        scheduler_future=None,
        generator=None,
        full_config=config,
        generated_schedules=[],
        last_accessed_at=time.monotonic() - 2,
    )
    server_module.schedule_sessions[schedule_id] = session

    async def workflow() -> None:
        await session.generation_lock.acquire()
        try:
            server_module.cleanup_expired_sessions()
            assert schedule_id in server_module.schedule_sessions
        finally:
            session.generation_lock.release()
        server_module.cleanup_expired_sessions()
        assert schedule_id not in server_module.schedule_sessions

    _run(workflow())


def test_http_submission_limits_accept_boundary_and_reject_boundary_plus_one(monkeypatch) -> None:
    one_course = config_from(minimal_config_data())
    two_courses = config_from(two_course_config_data())
    estimate = server_module._estimate_candidate_slots(one_course, 1_000_000)

    async def submit(config: CombinedConfig, limits: ApiLimits) -> int:
        monkeypatch.setattr(server_module, "API_LIMITS", limits)
        async with _client() as client:
            response = await client.post("/submit", json=config.model_dump(mode="json"))
            if response.status_code == 200:
                cleanup_session(response.json()["schedule_id"])
            return response.status_code

    assert _run(submit(one_course, ApiLimits(max_courses=1))) == 200
    assert _run(submit(two_courses, ApiLimits(max_courses=1))) == 422
    assert _run(submit(one_course, ApiLimits(max_schedules_per_session=1))) == 200
    assert _run(submit(one_course.model_copy(update={"limit": 2}), ApiLimits(max_schedules_per_session=1))) == 422
    assert _run(submit(one_course, ApiLimits(max_candidate_slots=estimate))) == 200
    assert _run(submit(one_course, ApiLimits(max_candidate_slots=estimate - 1))) == 422


def test_http_active_session_limit_boundary(monkeypatch) -> None:
    monkeypatch.setattr(server_module, "API_LIMITS", ApiLimits(max_active_sessions=1))
    config = config_from(minimal_config_data())

    async def workflow() -> None:
        async with _client() as client:
            first = await client.post("/submit", json=config.model_dump(mode="json"))
            second = await client.post("/submit", json=config.model_dump(mode="json"))
            assert first.status_code == 200
            assert second.status_code == 422

    _run(workflow())
