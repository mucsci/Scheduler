"""Public, solver-independent diagnostic result contracts."""

from dataclasses import dataclass


@dataclass(frozen=True)
class ConfigurationDiagnostic:
    """One schema or cross-reference validation error with a JSON Pointer path."""

    code: str
    path: str
    message: str
    value: str | None = None
    related_paths: tuple[str, ...] = ()


@dataclass(frozen=True)
class ConfigurationValidationResult:
    """Structured result of validating an untrusted scheduler configuration payload."""

    is_valid: bool
    diagnostics: tuple[ConfigurationDiagnostic, ...] = ()
    configuration_fingerprint: str | None = None


@dataclass(frozen=True)
class ProvenanceEdge:
    """A directed explanation edge from input data to a derived diagnostic fact."""

    source: str
    target: str
    relationship: str
    subjects: tuple[str, ...] = ()


@dataclass(frozen=True)
class ScheduleDiagnosis:
    """Result of checking the hard scheduling constraints without optimization."""

    status: str
    conflicting_constraints: tuple["ConstraintDiagnostic", ...] = ()
    alternative_conflict_sets: tuple[tuple["ConstraintDiagnostic", ...], ...] = ()
    supporting_facts: tuple["ConstraintDiagnostic", ...] = ()
    relaxation_suggestions: tuple["RelaxationSuggestion", ...] = ()
    repair_sets: tuple["RepairSetDiagnostic", ...] = ()
    candidate_domains: tuple["CandidateDomainDiagnostic", ...] = ()
    capacity_analysis: tuple["CapacityDiagnostic", ...] = ()
    day_feasibility: tuple["DayFeasibilityDiagnostic", ...] = ()
    preflight_findings: tuple["ConstraintDiagnostic", ...] = ()
    provenance: tuple[ProvenanceEdge, ...] = ()
    configuration_fingerprint: str | None = None
    core_is_minimal: bool | None = None
    alternative_cores_complete: bool | None = None
    repair_sets_complete: bool | None = None
    diagnostic_completeness: str = "partial"
    diagnostic_version: str = "1"
    elapsed_ms: int = 0
    solver_timeout_ms: int | None = None
    reason: str | None = None


@dataclass(frozen=True)
class ConstraintDiagnostic:
    """One business rule participating in an unsatisfiable core."""

    kind: str
    subjects: tuple[str, ...]
    message: str
    code: str | None = None
    locations: tuple[str, ...] = ()


@dataclass(frozen=True)
class CandidateDomainDiagnostic:
    """The remaining candidate domain for one course after static filtering."""

    course: str
    locations: tuple[str, ...]
    faculty_candidates: tuple[str, ...]
    faculty_origin: str
    room_candidates: tuple[str, ...]
    lab_candidates: tuple[str, ...]
    compatible_time_patterns: tuple[str, ...]
    availability_by_faculty: tuple[ConstraintDiagnostic, ...]
    rejected_patterns: tuple[ConstraintDiagnostic, ...]
    rejected_pattern_count: int
    rejected_patterns_truncated: bool


@dataclass(frozen=True)
class CapacityDiagnostic:
    """A necessary-condition capacity check, independent of solver search."""

    kind: str
    subjects: tuple[str, ...]
    message: str
    required: int
    available: int
    locations: tuple[str, ...] = ()


@dataclass(frozen=True)
class DayFeasibilityDiagnostic:
    """One cell of the faculty/day availability and pattern-feasibility matrix."""

    faculty: str
    day: str
    availability_windows: tuple[str, ...]
    eligible_courses: tuple[str, ...]
    compatible_pattern_count: int
    available_pattern_count: int
    is_mandatory: bool
    locations: tuple[str, ...]


@dataclass(frozen=True)
class RepairSetDiagnostic:
    """A verified minimal set of business rules whose relaxation restores feasibility."""

    relaxed_constraints: tuple[ConstraintDiagnostic, ...]
    verified: bool
    message: str


@dataclass(frozen=True)
class FacultyWorkloadDiagnostic:
    """A faculty member's assigned load with its configured bounds."""

    faculty: str
    credits: int
    minimum_credits: int
    maximum_credits: int
    teaching_days: tuple[str, ...]
    maximum_days: int
    distinct_courses: int
    unique_course_limit: int
    mandatory_days_satisfied: bool
    locations: tuple[str, ...]


@dataclass(frozen=True)
class ResourceUsageDiagnostic:
    """One resource's assignments and any detected collisions."""

    kind: str
    resource: str
    assignments: tuple[str, ...]
    collisions: tuple[ConstraintDiagnostic, ...] = ()


@dataclass(frozen=True)
class ObjectiveScoreDiagnostic:
    """Score and independent upper bound for one enabled soft objective."""

    objective: str
    score: int
    independent_upper_bound: int
    message: str


@dataclass(frozen=True)
class ScheduleAudit:
    """Independent post-generation hard-rule and objective audit."""

    is_valid: bool
    constraint_violations: tuple[ConstraintDiagnostic, ...]
    faculty_workloads: tuple[FacultyWorkloadDiagnostic, ...]
    resource_usage: tuple[ResourceUsageDiagnostic, ...]
    objective_scores: tuple[ObjectiveScoreDiagnostic, ...]
    preference_outcomes: tuple[ConstraintDiagnostic, ...]


@dataclass(frozen=True)
class RelaxationSuggestion:
    """A targeted configuration change that may restore feasibility."""

    kind: str
    subjects: tuple[str, ...]
    message: str
    priority: int = 1
