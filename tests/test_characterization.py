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


def test_minimal_schedule_and_api_serialization_match_golden(
    minimal_combined_config: CombinedConfig,
) -> None:
    schedule = next(Scheduler(minimal_combined_config).get_models())

    assert schedule_signature(schedule) == _golden("minimal_schedule.json")
    rows = [row.model_dump(mode="json", exclude_none=True) for row in _schedule_response_rows(schedule)]
    assert rows == _golden("minimal_api_schedule.json")


def test_minimal_audit_matches_golden(minimal_combined_config: CombinedConfig) -> None:
    scheduler = Scheduler(minimal_combined_config)
    audit = scheduler.audit_schedule(next(scheduler.get_models()))

    assert stable_payload(audit) == _golden("minimal_audit.json")


def test_unsatisfiable_diagnosis_matches_golden(
    unsatisfiable_combined_config: CombinedConfig,
) -> None:
    diagnosis = Scheduler(unsatisfiable_combined_config).diagnose()

    assert stable_payload(diagnosis) == _golden("unsatisfiable_diagnosis.json")


def test_model_blocking_order_matches_golden(two_course_combined_config: CombinedConfig) -> None:
    schedules = [schedule_signature(schedule) for schedule in Scheduler(two_course_combined_config).get_models()]

    assert schedules == _golden("two_course_schedules.json")
