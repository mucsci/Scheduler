"""Integration tests: scheduler, CLI, and HTTP API."""

import asyncio
import itertools
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

import pytest
from _pytest.outcomes import Skipped
from click.testing import CliRunner
from fastapi import HTTPException
from fastapi.testclient import TestClient

from scheduler import CombinedConfig, Scheduler, load_config_from_file, validate_combined_config_data
from scheduler import server as server_module
from scheduler.config import CourseConfig
from scheduler.main import main as scheduler_cli
from scheduler.models import CourseInstance
from scheduler.scheduler import get_faculty_availability
from scheduler.server import (
    ApiLimits,
    ScheduleResponse,
    app,
    cleanup_expired_sessions,
    cleanup_session,
    generate_all_schedules,
    get_next_schedule,
    submit_schedule,
)
from scheduler.server import main as server_cli

pytestmark = pytest.mark.integration


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
    diagnosis = sched.diagnose()
    assert diagnosis.status == "unsatisfiable"
    assert diagnosis.conflicting_constraints[0].kind == "faculty_credit_range"
    assert diagnosis.conflicting_constraints[0].code == "SCHED.FACULTY.CREDIT.RANGE"
    assert diagnosis.conflicting_constraints[0].locations == ("/config/faculty/0",)
    assert diagnosis.configuration_fingerprint
    assert diagnosis.core_is_minimal is True
    assert diagnosis.alternative_cores_complete is True
    assert diagnosis.diagnostic_completeness == "bounded_unsat_cores"
    assert diagnosis.candidate_domains[0].locations == ("/config/courses/0",)
    assert diagnosis.candidate_domains[0].availability_by_faculty[0].kind == "faculty_candidate_availability"
    assert any(item.kind == "faculty_forced_credit_load" for item in diagnosis.capacity_analysis)
    assert any(item.kind == "capacity_shortfall" for item in diagnosis.preflight_findings)
    assert any(edge.relationship == "contributes_to_unsat_core" for edge in diagnosis.provenance)
    assert diagnosis.repair_sets
    assert diagnosis.repair_sets[0].verified is True
    assert diagnosis.repair_sets[0].relaxed_constraints[0].kind == "faculty_credit_range"
    assert {fact.kind for fact in diagnosis.supporting_facts} >= {
        "forced_course_faculty",
        "faculty_workload_contribution",
        "forced_course_room",
        "forced_course_lab",
    }
    assert diagnosis.relaxation_suggestions[0].kind == "increase_faculty_maximum_credits"


def test_unassigned_faculty_minimum_credits_makes_schedule_unsatisfiable(
    minimal_config_path: Path,
) -> None:
    data = json.loads(minimal_config_path.read_text(encoding="utf-8"))
    data["config"]["faculty"].append(
        {
            "name": "F2",
            "maximum_credits": 4,
            "minimum_credits": 4,
            "unique_course_limit": 1,
            "times": {"MON": ["08:00-20:00"]},
        }
    )
    config = CombinedConfig(**data)
    assert next(Scheduler(config).get_models(), None) is None


def test_structured_validation_diagnostics_include_json_pointer() -> None:
    result = validate_combined_config_data({"not": "a combined config"})
    assert result.is_valid is False
    assert result.diagnostics
    assert result.diagnostics[0].code.startswith("SCHED.CONFIG.")
    assert result.diagnostics[0].path.startswith("/")


def test_capacity_schema_validation_reports_exact_resource_and_section_paths(minimal_config_path: Path) -> None:
    data = json.loads(minimal_config_path.read_text(encoding="utf-8"))
    data["config"]["rooms"] = ["R1"]
    del data["config"]["courses"][0]["capacity"]

    result = validate_combined_config_data(data)

    assert result.is_valid is False
    assert {item.path for item in result.diagnostics} >= {
        "/config/rooms/0",
        "/config/courses/0/capacity",
    }


def test_diagnosis_finds_an_alternative_independent_core(minimal_config_path: Path) -> None:
    data = json.loads(minimal_config_path.read_text(encoding="utf-8"))
    for name in ("F2", "F3"):
        data["config"]["faculty"].append(
            {
                "name": name,
                "maximum_credits": 4,
                "minimum_credits": 4,
                "unique_course_limit": 1,
                "times": {"MON": ["08:00-20:00"]},
            }
        )
    diagnosis = Scheduler(CombinedConfig(**data)).diagnose()
    assert diagnosis.status == "unsatisfiable"
    assert diagnosis.alternative_conflict_sets
    assert diagnosis.conflicting_constraints != diagnosis.alternative_conflict_sets[0]
    assert diagnosis.alternative_conflict_sets[0][0].kind == "faculty_credit_range"


def test_diagnosis_explains_mandatory_day_pattern_gap(minimal_config_path: Path) -> None:
    data = json.loads(minimal_config_path.read_text(encoding="utf-8"))
    data["time_slot_config"]["classes"][0]["meetings"][0]["day"] = "TUE"
    data["time_slot_config"]["classes"][0]["meetings"][1]["day"] = "THU"
    data["config"]["faculty"][0]["mandatory_days"] = ["MON"]
    diagnosis = Scheduler(CombinedConfig(**data)).diagnose()
    assert diagnosis.status == "unsatisfiable"
    assert {fact.kind for fact in diagnosis.supporting_facts} >= {
        "faculty_day_availability",
        "course_day_pattern_gap",
    }
    coverage = next(
        item for item in diagnosis.capacity_analysis if item.kind == "faculty_mandatory_day_pattern_coverage"
    )
    assert coverage.subjects == ("F1", "MON")
    assert coverage.available == 0
    monday = next(item for item in diagnosis.day_feasibility if item.faculty == "F1" and item.day == "MON")
    assert monday.is_mandatory is True
    assert monday.available_pattern_count == 0
    assert any(item.kind == "capacity_shortfall" for item in diagnosis.preflight_findings)


def test_diagnosis_reports_unknown_solver_result(
    minimal_combined_config: CombinedConfig, monkeypatch: pytest.MonkeyPatch
) -> None:
    scheduler = Scheduler(minimal_combined_config, solver_timeout_ms=1)
    monkeypatch.setattr(
        scheduler._diagnostics,
        "_diagnostic_core",
        lambda: ("unknown", (), frozenset(), "timeout"),
    )
    diagnosis = scheduler.diagnose()
    assert diagnosis.status == "unknown"
    assert diagnosis.reason == "timeout"
    assert diagnosis.solver_timeout_ms == 1


def test_null_course_faculty_derives_candidates_from_preferences(minimal_config_path: Path) -> None:
    data = json.loads(minimal_config_path.read_text(encoding="utf-8"))
    data["config"]["courses"][0]["faculty"] = None
    data["config"]["faculty"][0]["course_preferences"] = {"CS101": 10}
    config = CombinedConfig(**data)
    schedule = next(Scheduler(config).get_models())
    assert schedule[0].faculty == "F1"


def test_schedule_audit_reports_hard_rule_compliance_and_workload(
    minimal_combined_config: CombinedConfig,
) -> None:
    scheduler = Scheduler(minimal_combined_config)
    schedule = next(scheduler.get_models())
    audit = scheduler.audit_schedule(schedule)
    assert audit.is_valid is True
    assert audit.constraint_violations == ()
    workload = audit.faculty_workloads[0]
    assert workload.faculty == "F1"
    assert workload.credits == 4
    assert workload.mandatory_days_satisfied is True
    assert {item.resource for item in audit.resource_usage} == {"R1", "L1"}


def test_schedule_audit_explains_enabled_preference_objectives(minimal_config_path: Path) -> None:
    data = json.loads(minimal_config_path.read_text(encoding="utf-8"))
    data["optimizer_flags"] = ["faculty_course", "faculty_room", "faculty_lab"]
    data["config"]["faculty"][0].update(
        {
            "course_preferences": {"CS101": 7},
            "room_preferences": {"R1": 5},
            "lab_preferences": {"L1": 3},
        }
    )
    scheduler = Scheduler(CombinedConfig(**data))
    audit = scheduler.audit_schedule(next(scheduler.get_models()))
    assert {item.objective for item in audit.objective_scores} == {
        "faculty_course",
        "faculty_room",
        "faculty_lab",
    }
    assert all(item.score == item.independent_upper_bound for item in audit.objective_scores)
    assert audit.preference_outcomes == ()


def test_no_lab_schedule_uses_internal_no_lab_value(minimal_config_path: Path) -> None:
    data = json.loads(minimal_config_path.read_text(encoding="utf-8"))
    data["config"]["labs"] = []
    data["config"]["courses"][0]["lab"] = []
    data["time_slot_config"]["classes"][0]["meetings"][0]["lab"] = False
    config = CombinedConfig(**data)
    schedule = next(Scheduler(config).get_models())
    assert schedule[0].lab is None
    assert schedule[0].lab_index is None


def test_z3_symbol_generation_accepts_colliding_display_names(minimal_config_path: Path) -> None:
    data = json.loads(minimal_config_path.read_text(encoding="utf-8"))
    data["config"]["rooms"] = [
        {"name": "A B", "capacity": 30},
        {"name": "A_B", "capacity": 30},
    ]
    data["config"]["courses"][0]["room"] = ["A B"]
    config = CombinedConfig(**data)
    assert next(Scheduler(config).get_models()) is not None


@pytest.mark.slow
def test_example_json_produces_schedules(example_json_path: Path) -> None:
    if not example_json_path.is_file():
        raise Skipped("example.json not present")
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


def test_cli_accepts_optimizer_flags_and_rejects_nonpositive_limit(minimal_config_path: Path, tmp_path: Path) -> None:
    output = tmp_path / "optimized"
    valid = CliRunner().invoke(
        scheduler_cli,
        [
            str(minimal_config_path),
            "--limit",
            "1",
            "--format",
            "json",
            "--output",
            str(output),
            "-O",
            "faculty_course",
        ],
    )
    invalid = CliRunner().invoke(scheduler_cli, [str(minimal_config_path), "--limit", "0"])

    assert valid.exit_code == 0, valid.output
    assert output.with_suffix(".json").is_file()
    assert invalid.exit_code == 2


@pytest.mark.parametrize("args", [["--workers", "0"], ["--port", "0"], ["--port", "65536"]])
def test_server_cli_rejects_invalid_numeric_bounds(args: list[str]) -> None:
    result = CliRunner().invoke(server_cli, args)

    assert result.exit_code == 2


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
        audit = client.get(f"/schedules/{schedule_id}/audit/{body['index']}")
        assert audit.status_code == 200, audit.text
        audit_body = audit.json()
        assert audit_body["is_valid"] is True
        assert audit_body["faculty_workloads"][0]["faculty"] == "F1"
        assert audit_body["resource_usage"]
        assert audit_body["resource_usage"][0]["capacity"] == 30
        assert audit_body["resource_usage"][0]["maximum_assigned_section_capacity"] == 30
        assert audit_body["resource_usage"][0]["capacity_violations"] == []
        status = client.get(f"/schedules/{schedule_id}/status")
        assert status.status_code == 200, status.text
        status_body = status.json()
        assert status_body["state"] in {"ready", "complete"}
        assert status_body["solver_timeout_ms"] > 0
        assert status_body["max_candidate_slots"] > 0
        assert status_body["enumeration_scope"] in {
            "exhausted",
            "bounded_by_requested_limit",
            "indeterminate",
        }
    finally:
        cleanup_session(schedule_id)


def test_server_reports_unsatisfiable_constraint_groups(
    client: TestClient, unsatisfiable_combined_config: CombinedConfig
) -> None:
    submit = client.post("/submit", json=unsatisfiable_combined_config.model_dump(mode="json"))
    assert submit.status_code == 200, submit.text
    schedule_id = submit.json()["schedule_id"]
    try:
        diagnosis = client.get(f"/schedules/{schedule_id}/diagnosis")
        assert diagnosis.status_code == 200, diagnosis.text
        body = diagnosis.json()
        assert body["schedule_id"] == schedule_id
        assert body["status"] == "unsatisfiable"
        assert body["conflicting_constraints"][0]["kind"] == "faculty_credit_range"
        assert body["conflicting_constraints"][0]["code"] == "SCHED.FACULTY.CREDIT.RANGE"
        assert body["conflicting_constraints"][0]["locations"] == ["/config/faculty/0"]
        assert body["configuration_fingerprint"]
        assert body["candidate_domains"][0]["locations"] == ["/config/courses/0"]
        assert body["candidate_domains"][0]["section_capacity"] == 30
        assert body["candidate_domains"][0]["capacity_compatible_room_candidates"] == ["R1"]
        assert body["candidate_domains"][0]["capacity_compatible_lab_candidates"] == ["L1"]
        assert body["capacity_analysis"]
        assert body["day_feasibility"]
        assert body["preflight_findings"]
        assert body["provenance"]
        assert body["repair_sets"][0]["verified"] is True
        assert body["repair_sets"][0]["relaxed_constraints"][0]["kind"] == "faculty_credit_range"
        assert body["relaxation_suggestions"][0]["kind"] == "increase_faculty_maximum_credits"
        assert body["elapsed_ms"] >= 0
    finally:
        cleanup_session(schedule_id)


def test_server_submit_invalid_body(client: TestClient) -> None:
    r = client.post("/submit", json={"not": "a combined config"})
    assert r.status_code == 422


def test_server_validate_returns_structured_validation_diagnostics(client: TestClient) -> None:
    response = client.post("/validate", json={"not": "a combined config"})
    assert response.status_code == 200, response.text
    body = response.json()
    assert body["is_valid"] is False
    assert body["diagnostics"][0]["code"].startswith("SCHED.CONFIG.")
    assert body["diagnostics"][0]["path"].startswith("/")


def test_server_cleanup_unknown_session_no_crash(client: TestClient) -> None:
    r = client.post("/schedules/00000000-0000-0000-0000-000000000000/cleanup")
    assert r.status_code == 200


def test_server_serializes_concurrent_next_requests(minimal_combined_config: CombinedConfig) -> None:
    config = minimal_combined_config.model_copy(update={"limit": 2})

    async def generate_two() -> tuple[ScheduleResponse | BaseException, ScheduleResponse | BaseException]:
        submitted = await submit_schedule(config)
        try:
            return await asyncio.gather(
                get_next_schedule(submitted.schedule_id),
                get_next_schedule(submitted.schedule_id),
                return_exceptions=True,
            )
        finally:
            cleanup_session(submitted.schedule_id)

    results = asyncio.run(generate_two())
    assert not any(isinstance(result, HTTPException) and result.status_code == 500 for result in results)
    successful = [result for result in results if isinstance(result, ScheduleResponse)]
    assert {result.index for result in successful} == set(range(len(successful)))


def test_server_rejects_competing_background_generation(minimal_combined_config: CombinedConfig) -> None:
    config = minimal_combined_config.model_copy(update={"limit": 2})

    async def start_twice() -> None:
        submitted = await submit_schedule(config)
        try:
            await generate_all_schedules(submitted.schedule_id)
            with pytest.raises(HTTPException) as error:
                await generate_all_schedules(submitted.schedule_id)
            assert error.value.status_code == 409
        finally:
            cleanup_session(submitted.schedule_id)

    asyncio.run(start_twice())


def test_server_enforces_submission_limits(
    minimal_combined_config: CombinedConfig, monkeypatch: pytest.MonkeyPatch
) -> None:
    async def submit_with(limits: ApiLimits, config: CombinedConfig) -> HTTPException:
        monkeypatch.setattr(server_module, "API_LIMITS", limits)
        with pytest.raises(HTTPException) as error:
            await submit_schedule(config)
        return error.value

    too_many_courses = minimal_combined_config.model_copy(deep=True)
    duplicate = too_many_courses.config.courses[0].model_copy(update={"course_id": "CS102"})
    too_many_courses.config.courses.append(duplicate)
    error = asyncio.run(
        submit_with(
            ApiLimits(max_courses=1),
            too_many_courses,
        )
    )
    assert error.status_code == 422

    error = asyncio.run(
        submit_with(
            ApiLimits(max_schedules_per_session=1),
            minimal_combined_config.model_copy(update={"limit": 2}),
        )
    )
    assert error.status_code == 422

    error = asyncio.run(submit_with(ApiLimits(max_candidate_slots=1), minimal_combined_config))
    assert error.status_code == 422


def test_server_enforces_active_session_limit(
    minimal_combined_config: CombinedConfig, monkeypatch: pytest.MonkeyPatch
) -> None:
    async def submit_twice() -> HTTPException:
        monkeypatch.setattr(server_module, "API_LIMITS", ApiLimits(max_active_sessions=1))
        first = await submit_schedule(minimal_combined_config)
        try:
            with pytest.raises(HTTPException) as error:
                await submit_schedule(minimal_combined_config)
            return error.value
        finally:
            cleanup_session(first.schedule_id)

    assert asyncio.run(submit_twice()).status_code == 422


def test_server_expires_idle_sessions(minimal_combined_config: CombinedConfig, monkeypatch: pytest.MonkeyPatch) -> None:
    async def create_and_expire() -> str:
        monkeypatch.setattr(server_module, "API_LIMITS", ApiLimits(session_ttl_seconds=1))
        submitted = await submit_schedule(minimal_combined_config)
        session = server_module.schedule_sessions[submitted.schedule_id]
        assert session.scheduler_future is not None
        session.scheduler = await asyncio.wrap_future(session.scheduler_future)
        session.last_accessed_at -= 2
        cleanup_expired_sessions()
        return submitted.schedule_id

    schedule_id = asyncio.run(create_and_expire())
    assert schedule_id not in server_module.schedule_sessions
