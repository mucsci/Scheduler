"""Unit tests for solver-independent problem normalization."""

from scheduler import CombinedConfig
from scheduler.problem import SchedulingProblem


def test_problem_normalizes_null_faculty_from_preferences(
    minimal_combined_config: CombinedConfig,
) -> None:
    config = minimal_combined_config.model_copy(deep=True)
    config.config.courses[0].faculty = None
    config.config.faculty[0].course_preferences = {"CS101": 7}

    problem = SchedulingProblem.from_config(config)

    assert problem.courses[0].faculties == ["F1"]
    assert problem.course_faculty_origins["CS101.01"] == "derived_from_preferences"
    assert problem.course_policies["CS101.01"].faculties == ("F1",)
    assert problem.course_policies["CS101.01"].faculty_origin == "derived_from_preferences"


def test_problem_caches_compatible_slot_domains(
    minimal_combined_config: CombinedConfig,
) -> None:
    problem = SchedulingProblem.from_config(minimal_combined_config)
    course = problem.courses[0]

    first = problem.compatible_slots(course)
    second = problem.compatible_slots(course)

    assert first is second
    assert first
    assert all(slot.has_lab() for slot in first)
    assert len(problem.configuration_fingerprint()) == 64
