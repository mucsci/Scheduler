"""Unit tests for diagnostics independent of the public façade."""

from scheduler import CombinedConfig
from scheduler.diagnostics import DiagnosticEngine
from scheduler.problem import SchedulingProblem
from scheduler.solver import SolverEngine


def test_diagnostic_engine_consumes_solver_artifacts(
    unsatisfiable_combined_config: CombinedConfig,
) -> None:
    problem = SchedulingProblem.from_config(unsatisfiable_combined_config)
    solver = SolverEngine(problem)
    diagnostics = DiagnosticEngine(problem, solver.artifacts)

    result = diagnostics.diagnose()

    assert result.status == "unsatisfiable"
    assert result.core_is_minimal is True
    assert result.conflicting_constraints
    assert result.configuration_fingerprint == problem.configuration_fingerprint()
