"""Unit tests for Z3 solver ownership and compatibility mirrors."""

import pytest

from scheduler import CombinedConfig
from scheduler.problem import SchedulingProblem
from scheduler.solver import SolverEngine


def test_solver_artifacts_are_read_only_and_courses_keep_variable_mirrors(
    minimal_combined_config: CombinedConfig,
) -> None:
    problem = SchedulingProblem.from_config(minimal_combined_config)
    engine = SolverEngine(problem)
    course = problem.courses[0]
    variables = engine.artifacts.course_variables[str(course)]

    assert course.time is variables.time
    assert course.faculty is variables.faculty
    assert course.room is variables.room
    assert course.lab is variables.lab
    assert engine.artifacts.constraints
    assert engine.artifacts.diagnostic_constraints
    with pytest.raises(TypeError):
        engine.artifacts.course_variables[str(course)] = variables  # ty: ignore[invalid-assignment]


def test_solver_engine_enumerates_models_directly(
    minimal_combined_config: CombinedConfig,
) -> None:
    engine = SolverEngine(SchedulingProblem.from_config(minimal_combined_config))

    schedule = next(engine.get_models())

    assert [str(instance.course) for instance in schedule] == ["CS101.01"]
