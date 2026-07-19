"""Dependency and delegation contracts for the refactored architecture."""

import ast
import inspect
from dataclasses import fields
from pathlib import Path

from scheduler import CombinedConfig
from scheduler import scheduler as facade_module
from scheduler.contracts import ConstraintDiagnostic, ScheduleDiagnosis

SOURCE = Path(__file__).resolve().parents[1] / "src" / "scheduler"


def _imports(module: str) -> set[str]:
    tree = ast.parse((SOURCE / f"{module}.py").read_text(encoding="utf-8"))
    imported: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported.add(node.module)
    return imported


def test_solver_independent_layers_do_not_import_z3() -> None:
    for module in ("contracts", "configuration", "problem", "audit", "scheduler"):
        assert "z3" not in _imports(module), module


def test_scheduler_facade_exposes_only_orchestration_methods() -> None:
    methods = {
        name
        for name, value in vars(facade_module.Scheduler).items()
        if inspect.isfunction(value) and not name.startswith("__")
    }
    assert methods == {"get_models", "diagnose", "audit_schedule"}


def test_scheduler_facade_delegates_to_injected_components(
    minimal_combined_config: CombinedConfig,
    monkeypatch,
) -> None:
    calls: list[object] = []
    problem = object()
    artifacts = object()
    schedule = [object()]
    diagnosis = object()
    audit = object()

    class ProblemFactory:
        @classmethod
        def from_config(cls, config):
            calls.append(("problem", config))
            return problem

    class FakeSolver:
        def __init__(self, received_problem, *, solver_timeout_ms=None):
            calls.append(("solver", received_problem, solver_timeout_ms))
            self.artifacts = artifacts

        def get_models(self):
            calls.append("models")
            yield schedule

    class FakeDiagnostics:
        def __init__(self, received_problem, received_artifacts, *, solver_timeout_ms=None):
            calls.append(("diagnostics", received_problem, received_artifacts, solver_timeout_ms))

        def diagnose(self):
            calls.append("diagnose")
            return diagnosis

    class FakeAuditor:
        def __init__(self, received_problem):
            calls.append(("auditor", received_problem))

        def audit_schedule(self, received_schedule):
            calls.append(("audit", received_schedule))
            return audit

    monkeypatch.setattr(facade_module, "SchedulingProblem", ProblemFactory)
    monkeypatch.setattr(facade_module, "SolverEngine", FakeSolver)
    monkeypatch.setattr(facade_module, "DiagnosticEngine", FakeDiagnostics)
    monkeypatch.setattr(facade_module, "ScheduleAuditor", FakeAuditor)

    scheduler = facade_module.Scheduler(minimal_combined_config, solver_timeout_ms=23)

    assert next(scheduler.get_models()) is schedule
    assert scheduler.diagnose() is diagnosis
    assert scheduler.audit_schedule(schedule) is audit
    assert calls == [
        ("problem", minimal_combined_config),
        ("solver", problem, 23),
        ("diagnostics", problem, artifacts, 23),
        ("auditor", problem),
        "models",
        "diagnose",
        ("audit", schedule),
    ]


def test_diagnostic_contract_field_order_and_equality_are_stable() -> None:
    assert [field.name for field in fields(ScheduleDiagnosis)] == [
        "status",
        "conflicting_constraints",
        "alternative_conflict_sets",
        "supporting_facts",
        "relaxation_suggestions",
        "repair_sets",
        "candidate_domains",
        "capacity_analysis",
        "day_feasibility",
        "preflight_findings",
        "provenance",
        "configuration_fingerprint",
        "core_is_minimal",
        "alternative_cores_complete",
        "repair_sets_complete",
        "diagnostic_completeness",
        "diagnostic_version",
        "elapsed_ms",
        "solver_timeout_ms",
        "reason",
    ]
    diagnostic = ConstraintDiagnostic(kind="example", subjects=("one",), message="message")
    assert diagnostic == ConstraintDiagnostic(kind="example", subjects=("one",), message="message")
    assert diagnostic != ConstraintDiagnostic(kind="other", subjects=("one",), message="message")
