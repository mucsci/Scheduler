"""Public scheduler façade and compatibility re-exports."""

from collections.abc import Generator

from .audit import ScheduleAuditor
from .config import CombinedConfig
from .configuration import load_config_from_file, validate_combined_config_data
from .contracts import (
    CandidateDomainDiagnostic,
    CapacityDiagnostic,
    ConfigurationDiagnostic,
    ConfigurationValidationResult,
    ConstraintDiagnostic,
    DayFeasibilityDiagnostic,
    FacultyWorkloadDiagnostic,
    ObjectiveScoreDiagnostic,
    ProvenanceEdge,
    RelaxationSuggestion,
    RepairSetDiagnostic,
    ResourceUsageDiagnostic,
    ScheduleAudit,
    ScheduleDiagnosis,
)
from .diagnostics import DiagnosticEngine
from .models import CourseInstance
from .problem import SchedulingProblem, get_faculty_availability
from .solver import SolverEngine

__all__ = [
    "CandidateDomainDiagnostic",
    "CapacityDiagnostic",
    "ConfigurationDiagnostic",
    "ConfigurationValidationResult",
    "ConstraintDiagnostic",
    "DayFeasibilityDiagnostic",
    "FacultyWorkloadDiagnostic",
    "ObjectiveScoreDiagnostic",
    "ProvenanceEdge",
    "RelaxationSuggestion",
    "RepairSetDiagnostic",
    "ResourceUsageDiagnostic",
    "ScheduleAudit",
    "ScheduleDiagnosis",
    "Scheduler",
    "get_faculty_availability",
    "load_config_from_file",
    "validate_combined_config_data",
]


class Scheduler:
    """Stable public façade over problem, solver, diagnostics, and auditing."""

    def __init__(self, full_config: CombinedConfig, *, solver_timeout_ms: int | None = None):
        self._problem = SchedulingProblem.from_config(full_config)
        self._solver = SolverEngine(self._problem, solver_timeout_ms=solver_timeout_ms)
        self._diagnostics = DiagnosticEngine(
            self._problem,
            self._solver.artifacts,
            solver_timeout_ms=solver_timeout_ms,
        )
        self._auditor = ScheduleAuditor(self._problem)

    def get_models(self) -> Generator[list[CourseInstance], None, None]:
        return self._solver.get_models()

    def diagnose(self) -> ScheduleDiagnosis:
        return self._diagnostics.diagnose()

    def audit_schedule(self, schedule: list["CourseInstance"]) -> ScheduleAudit:
        return self._auditor.audit_schedule(schedule)
