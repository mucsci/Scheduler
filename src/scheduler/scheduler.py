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
        """Enumerate optimized schedules through the owned solver engine.

        Args:
            None.

        Returns:
            A lazy generator yielding decoded course assignments in deterministic
            model-blocking order, bounded by the configured schedule limit.

        Raises:
            z3.Z3Exception: If Z3 rejects solver construction or optimization state.

        Behavior:
            Delegates directly to :class:`SolverEngine`; schedules are generated
            only as the caller advances the returned generator.
        """
        return self._solver.get_models()

    @property
    def _enumeration_completion_reason(self) -> str | None:
        """Expose solver termination metadata to the REST session adapter."""
        return self._solver.enumeration_completion_reason

    def diagnose(self) -> ScheduleDiagnosis:
        """Explain hard-constraint feasibility without changing model enumeration.

        Args:
            None.

        Returns:
            Structured feasibility, core, repair, provenance, and preflight data.

        Raises:
            z3.Z3Exception: If Z3 cannot execute a diagnostic feasibility check.

        Behavior:
            Delegates to the diagnostic engine, which uses immutable solver artifacts
            and does not run or mutate soft optimization objectives.
        """
        return self._diagnostics.diagnose()

    def audit_schedule(self, schedule: list["CourseInstance"]) -> ScheduleAudit:
        """Independently validate and score one decoded schedule.

        Args:
            schedule: Course assignments to validate against normalized policies.

        Returns:
            Hard-rule findings, workload/resource summaries, and objective scores.

        Raises:
            None.

        Behavior:
            Delegates to the Z3-independent auditor and never trusts or queries the
            solver model that originally produced the supplied assignments.
        """
        return self._auditor.audit_schedule(schedule)
