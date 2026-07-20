"""Unit tests for diagnostics independent of the public façade."""

import time

import pytest

from scheduler import CombinedConfig
from scheduler import diagnostics as diagnostics_module
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


def test_diagnostic_elapsed_time_includes_post_solver_analysis(
    minimal_combined_config: CombinedConfig, monkeypatch: pytest.MonkeyPatch
) -> None:
    _problem, _solver, diagnostics = _engines(minimal_combined_config)
    real_candidate_domains = diagnostics._candidate_domains

    def delayed_candidate_domains():
        time.sleep(0.02)
        return real_candidate_domains()

    monkeypatch.setattr(diagnostics, "_candidate_domains", delayed_candidate_domains)

    assert diagnostics.diagnose().elapsed_ms >= 15


def test_pattern_pair_scan_reports_false_when_exactly_at_cap(monkeypatch: pytest.MonkeyPatch) -> None:
    slot = SchedulingProblem.from_config(config_from(minimal_config_data())).slots[0]
    monkeypatch.setattr(diagnostics_module, "MAX_PAIR_PATTERN_COMPARISONS", 1)

    assert DiagnosticEngine._any_pattern_pair((slot,), (slot,), lambda _left, _right: False) is False
    assert DiagnosticEngine._any_pattern_pair((slot,), (slot, slot), lambda _left, _right: False) is None


def test_core_minimization_does_not_claim_minimality_after_unknown(
    unsatisfiable_combined_config: CombinedConfig,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _problem, _solver, diagnostics = _engines(unsatisfiable_combined_config)
    monkeypatch.setattr(
        diagnostics,
        "_diagnostic_core",
        lambda *args, **kwargs: ("unknown", (), frozenset(), "timeout"),
    )

    _conflicts, indexes, complete = diagnostics._minimize_core(frozenset({0}))

    assert indexes == frozenset({0})
    assert complete is False


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
    _conflicts, indexes, minimized = diagnostics._minimize_core(indexes)
    assert minimized is True

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


@pytest.mark.parametrize("resource_kind", ["room", "lab"])
def test_diagnostics_explain_resource_capacity_shortfalls(resource_kind: str) -> None:
    data = minimal_config_data()
    data["config"]["courses"][0]["capacity"] = 31
    if resource_kind == "room":
        data["config"]["labs"][0]["capacity"] = 31
    else:
        data["config"]["rooms"][0]["capacity"] = 31
    _problem, _solver, diagnostics = _engines(config_from(data))

    result = diagnostics.diagnose()
    domain = result.candidate_domains[0]

    assert result.status == "unsatisfiable"
    assert any(item.kind == f"course_{resource_kind}_capacity" for item in result.conflicting_constraints)
    assert any(item.kind == f"course_{resource_kind}_capacity_shortfall" for item in result.preflight_findings)
    assert any(item.kind == f"course_{resource_kind}_capacity_coverage" for item in result.capacity_analysis)
    assert any(
        suggestion.kind == f"add_capacity_compatible_{resource_kind}_candidate"
        for suggestion in result.relaxation_suggestions
    )
    assert result.repair_sets and all(repair.verified for repair in result.repair_sets)
    assert any(edge.relationship == "below_section_capacity" for edge in result.provenance)
    assert domain.section_capacity == 31
    assert getattr(domain, f"capacity_compatible_{resource_kind}_candidates") == ()
    assert getattr(domain, f"{resource_kind}_capacity_rejection_count") == 1
    assert getattr(domain, f"{resource_kind}_capacity_rejections")
