"""Unit tests for diagnostics independent of the public façade."""

from scheduler import CombinedConfig
from scheduler.diagnostics import DiagnosticEngine
from scheduler.problem import SchedulingProblem
from scheduler.solver import SolverEngine
from tests.scenario_builders import config_from, minimal_config_data


def _engines(config: CombinedConfig) -> tuple[SchedulingProblem, SolverEngine, DiagnosticEngine]:
    problem = SchedulingProblem.from_config(config)
    solver = SolverEngine(problem)
    return problem, solver, DiagnosticEngine(problem, solver.artifacts)


def test_diagnostic_engine_consumes_solver_artifacts(
    unsatisfiable_combined_config: CombinedConfig,
) -> None:
    problem, _solver, diagnostics = _engines(unsatisfiable_combined_config)

    result = diagnostics.diagnose()

    assert result.status == "unsatisfiable"
    assert result.core_is_minimal is True
    assert result.conflicting_constraints
    assert result.configuration_fingerprint == problem.configuration_fingerprint()


def test_diagnostic_engine_reports_satisfiable_preflight(
    minimal_combined_config: CombinedConfig,
) -> None:
    problem, _solver, diagnostics = _engines(minimal_combined_config)

    result = diagnostics.diagnose()

    assert result.status == "satisfiable"
    assert result.conflicting_constraints == ()
    assert result.diagnostic_completeness == "hard_constraint_feasibility"
    assert result.candidate_domains[0].compatible_time_patterns
    assert result.configuration_fingerprint == problem.configuration_fingerprint()


def test_diagnostic_engine_preserves_unknown_reason_and_timeout(
    minimal_combined_config: CombinedConfig, monkeypatch
) -> None:
    problem = SchedulingProblem.from_config(minimal_combined_config)
    solver = SolverEngine(problem, solver_timeout_ms=17)
    diagnostics = DiagnosticEngine(problem, solver.artifacts, solver_timeout_ms=17)
    monkeypatch.setattr(
        diagnostics,
        "_diagnostic_core",
        lambda *args, **kwargs: ("unknown", (), frozenset(), "timeout"),
    )

    result = diagnostics.diagnose()

    assert result.status == "unknown"
    assert result.reason == "timeout"
    assert result.solver_timeout_ms == 17
    assert result.diagnostic_completeness == "preflight_only"


def test_diagnostic_engine_enumerates_independent_cores_and_verified_repairs() -> None:
    data = minimal_config_data()
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
    _problem, _solver, diagnostics = _engines(config_from(data))

    result = diagnostics.diagnose()

    assert result.status == "unsatisfiable"
    assert result.alternative_conflict_sets
    assert all(repair.verified for repair in result.repair_sets)
    assert result.core_is_minimal
    assert isinstance(result.repair_sets_complete, bool)
    assert any(edge.relationship == "contributes_to_unsat_core" for edge in result.provenance)


def test_diagnostic_bounds_report_incomplete_search(
    unsatisfiable_combined_config: CombinedConfig,
) -> None:
    _problem, _solver, diagnostics = _engines(unsatisfiable_combined_config)
    status, _conflicts, indexes, _reason = diagnostics._diagnostic_core()
    assert status == "unsatisfiable"
    _conflicts, indexes = diagnostics._minimize_core(indexes)

    _alternatives, alternatives_complete = diagnostics._alternative_cores(
        indexes,
        max_alternatives=1,
        max_solver_checks=0,
    )
    _repairs, repairs_complete = diagnostics._repair_sets(max_repair_sets=1, max_solver_checks=0)

    assert alternatives_complete is False
    assert repairs_complete is False


def test_diagnostic_fingerprint_is_stable_and_input_sensitive(
    minimal_combined_config: CombinedConfig,
) -> None:
    first_problem, _solver, first = _engines(minimal_combined_config)
    second_problem, _solver, second = _engines(minimal_combined_config.model_copy(deep=True))
    changed = minimal_combined_config.model_copy(deep=True)
    changed.limit = 2
    changed_problem, _solver, third = _engines(changed)

    assert first.diagnose().configuration_fingerprint == second.diagnose().configuration_fingerprint
    assert first_problem.configuration_fingerprint() != changed_problem.configuration_fingerprint()
    assert third.diagnose().configuration_fingerprint == changed_problem.configuration_fingerprint()
