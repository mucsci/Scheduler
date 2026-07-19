"""Unit tests for independent schedule auditing."""

from scheduler import CombinedConfig
from scheduler.audit import ScheduleAuditor
from scheduler.problem import SchedulingProblem
from scheduler.solver import SolverEngine


def test_auditor_validates_a_decoded_schedule_without_a_model(
    minimal_combined_config: CombinedConfig,
) -> None:
    problem = SchedulingProblem.from_config(minimal_combined_config)
    schedule = next(SolverEngine(problem).get_models())
    auditor = ScheduleAuditor(problem)

    assert auditor.audit_schedule(schedule).is_valid is True

    schedule[0].room = "not-eligible"
    invalid = auditor.audit_schedule(schedule)
    assert invalid.is_valid is False
    assert any(item.kind == "course_room_eligibility" for item in invalid.constraint_violations)
