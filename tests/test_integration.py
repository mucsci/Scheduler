"""Integration tests: scheduler, CLI, and HTTP API."""

import itertools
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

import pytest
from fastapi.testclient import TestClient

from scheduler import CombinedConfig, Scheduler, load_config_from_file
from scheduler.config import CourseConfig
from scheduler.models import CourseInstance
from scheduler.scheduler import get_faculty_availability
from scheduler.server import app, cleanup_session


def _course_key_from_instance(ci: CourseInstance) -> str:
    """Base course id without section (matches config conflict keys)."""
    return ci.course.course_id


def _assert_faculty_availability(model: list[CourseInstance], cfg: CombinedConfig) -> None:
    faculty_by_name = {f.name: f for f in cfg.config.faculty}
    for ci in model:
        fac = faculty_by_name[ci.faculty]
        ranges = get_faculty_availability(fac)
        assert ci.time.in_time_ranges(ranges), f"{ci.faculty} not available for slot {ci.time}"


def _assert_conflicts_respected(model: list[CourseInstance], cfg: CombinedConfig) -> None:
    conflicts_map: dict[str, set[str]] = defaultdict(set)
    for c in cfg.config.courses:
        conflicts_map[c.course_id].update(c.conflicts)
    by_id: dict[str, list[CourseInstance]] = defaultdict(list)
    for ci in model:
        by_id[_course_key_from_instance(ci)].append(ci)
    for a, b in itertools.combinations(model, 2):
        id_a, id_b = _course_key_from_instance(a), _course_key_from_instance(b)
        if id_b in conflicts_map[id_a] or id_a in conflicts_map[id_b]:
            assert not a.time.overlaps(b.time), f"Conflict overlap {id_a} vs {id_b}"


def _assert_room_lab_allowed(model: list[CourseInstance], cfg: CombinedConfig) -> None:
    by_course_id: dict[str, CourseConfig] = {}
    for c in cfg.config.courses:
        if c.course_id not in by_course_id:
            by_course_id[c.course_id] = c
    for ci in model:
        spec = by_course_id[ci.course.course_id]
        assert ci.room in spec.room
        if ci.lab is not None:
            assert ci.lab in spec.lab


def test_scheduler_produces_schedule(minimal_combined_config: CombinedConfig) -> None:
    sched = Scheduler(minimal_combined_config)
    model = next(sched.get_models(), None)
    assert model is not None
    assert len(model) >= 1


def test_schedule_respects_faculty_availability(minimal_combined_config: CombinedConfig) -> None:
    sched = Scheduler(minimal_combined_config)
    model = next(sched.get_models())
    _assert_faculty_availability(model, minimal_combined_config)


def test_schedule_respects_conflicts(two_course_combined_config: CombinedConfig) -> None:
    sched = Scheduler(two_course_combined_config)
    model = next(sched.get_models(), None)
    assert model is not None
    _assert_conflicts_respected(model, two_course_combined_config)


def test_schedule_respects_room_lab(minimal_combined_config: CombinedConfig) -> None:
    sched = Scheduler(minimal_combined_config)
    model = next(sched.get_models())
    _assert_room_lab_allowed(model, minimal_combined_config)


def test_schedule_respects_limit(minimal_config_path: Path, tmp_path: Path) -> None:
    data = json.loads(minimal_config_path.read_text(encoding="utf-8"))
    data["limit"] = 2
    cfg = CombinedConfig(**data)
    sched = Scheduler(cfg)
    models = list(itertools.islice(sched.get_models(), 3))
    assert len(models) <= 2


def test_unsatisfiable_config_yields_no_models(unsatisfiable_combined_config: CombinedConfig) -> None:
    sched = Scheduler(unsatisfiable_combined_config)
    assert next(sched.get_models(), None) is None


@pytest.mark.slow
def test_example_json_produces_schedules(example_json_path: Path) -> None:
    if not example_json_path.is_file():
        pytest.skip("example.json not present")
    cfg = load_config_from_file(CombinedConfig, str(example_json_path))
    sched = Scheduler(cfg)
    model = next(sched.get_models(), None)
    assert model is not None


def test_cli_generates_csv(minimal_config_path: Path, tmp_path: Path) -> None:
    out_base = tmp_path / "sched_out"
    result = subprocess.run(
        [sys.executable, "-m", "scheduler.main", str(minimal_config_path), "-l", "1", "-f", "csv", "-o", str(out_base)],
        cwd=Path(__file__).resolve().parent.parent,
        capture_output=True,
        text=True,
        timeout=120,
        env={**__import__("os").environ, "PYTHONPATH": "src"},
    )
    assert result.returncode == 0, result.stderr + result.stdout
    csv_path = Path(str(out_base) + ".csv")
    assert csv_path.is_file()
    assert csv_path.read_text(encoding="utf-8").strip()


def test_cli_invalid_config_path_exits_nonzero(tmp_path: Path) -> None:
    missing = tmp_path / "nope.json"
    result = subprocess.run(
        [sys.executable, "-m", "scheduler.main", str(missing), "-l", "1", "-o", str(tmp_path / "x"), "-f", "csv"],
        cwd=Path(__file__).resolve().parent.parent,
        capture_output=True,
        text=True,
        timeout=30,
        env={**__import__("os").environ, "PYTHONPATH": "src"},
    )
    assert result.returncode != 0


@pytest.fixture
def client():
    return TestClient(app)


def test_server_health(client: TestClient) -> None:
    r = client.get("/health")
    assert r.status_code == 200
    data = r.json()
    assert data["status"] == "healthy"
    assert "active_sessions" in data


def test_server_submit_and_next_schedule(client: TestClient, minimal_combined_config: CombinedConfig) -> None:
    submit = client.post("/submit", json=minimal_combined_config.model_dump(mode="json"))
    assert submit.status_code == 200, submit.text
    schedule_id = submit.json()["schedule_id"]
    try:
        nxt = client.post(f"/schedules/{schedule_id}/next")
        assert nxt.status_code == 200, nxt.text
        body = nxt.json()
        assert body["schedule_id"] == schedule_id
        assert isinstance(body["schedule"], list)
        assert len(body["schedule"]) >= 1
    finally:
        cleanup_session(schedule_id)


def test_server_submit_invalid_body(client: TestClient) -> None:
    r = client.post("/submit", json={"not": "a combined config"})
    assert r.status_code == 422


def test_server_cleanup_unknown_session_no_crash(client: TestClient) -> None:
    r = client.post("/schedules/00000000-0000-0000-0000-000000000000/cleanup")
    assert r.status_code == 200
