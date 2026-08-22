"""Golden behavioral contracts protecting the public refactor boundary."""

import json
from pathlib import Path

import pytest

from scheduler import CombinedConfig, Scheduler
from scheduler.server import _schedule_response_rows
from tests.scenario_builders import schedule_signature, stable_payload

GOLDENS = Path(__file__).resolve().parent / "fixtures" / "characterization"
pytestmark = [pytest.mark.integration, pytest.mark.characterization]


def _golden(name: str):
    return json.loads((GOLDENS / name).read_text(encoding="utf-8"))


def test_minimal_schedule_and_api_serialization_are_semantically_valid(
    minimal_combined_config: CombinedConfig,
) -> None:
    scheduler = Scheduler(minimal_combined_config)
    schedule = next(scheduler.get_models())

    assert [(item.course_str, item.faculty, item.room, item.lab) for item in schedule] == [
        ("CS101.01", "F1", "R1", "L1"),
    ]
    assert scheduler.audit_schedule(schedule).constraint_violations == ()

    rows = [row.model_dump(mode="json", exclude_none=True) for row in _schedule_response_rows(schedule)]
    assert [(row["course"], row["faculty"], row["room"], row["lab"]) for row in rows] == [
        ("CS101.01", "F1", "R1", "L1"),
    ]
    assert [(slot["day"], slot["duration"], slot["delivery"]) for slot in rows[0]["times"]] == [
        (1, 110, "in_person"),
        (3, 110, "in_person"),
    ]


def test_minimal_audit_matches_golden(minimal_combined_config: CombinedConfig) -> None:
    scheduler = Scheduler(minimal_combined_config)
    audit = scheduler.audit_schedule(next(scheduler.get_models()))

    assert stable_payload(audit) == _golden("minimal_audit.json")


def test_unsatisfiable_diagnosis_matches_golden(
    unsatisfiable_combined_config: CombinedConfig,
) -> None:
    diagnosis = Scheduler(unsatisfiable_combined_config).diagnose()

    assert stable_payload(diagnosis) == _golden("unsatisfiable_diagnosis.json")


def test_model_blocking_enumerates_distinct_valid_schedules(two_course_combined_config: CombinedConfig) -> None:
    scheduler = Scheduler(two_course_combined_config)
    schedules = list(scheduler.get_models())

    assert len(schedules) == two_course_combined_config.limit
    assert len({tuple(schedule_signature(schedule)) for schedule in schedules}) == len(schedules)
    for schedule in schedules:
        assert {item.course_str for item in schedule} == {"CS101.01", "CS102.01"}
        assert scheduler.audit_schedule(schedule).constraint_violations == ()
