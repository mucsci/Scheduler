"""Public, solver-independent diagnostic result contracts."""

from dataclasses import dataclass
from typing import Literal


@dataclass(frozen=True)
class ConfigurationDiagnostic:
    """One schema or cross-reference validation error with a JSON Pointer path.

    Fields:
        code: Stable machine-readable configuration error code.
        path: JSON Pointer locating the invalid input.
        message: Human-readable explanation of the validation failure.
        value: Optional printable representation of the rejected value.
        related_paths: Other JSON Pointers participating in the same failure.
    """

    code: str
    path: str
    message: str
    value: str | None = None
    related_paths: tuple[str, ...] = ()


@dataclass(frozen=True)
class ConfigurationValidationResult:
    """Structured result of validating an untrusted scheduler configuration payload.

    Fields:
        is_valid: Whether the complete payload passed validation.
        diagnostics: Ordered validation failures; empty for valid input.
        configuration_fingerprint: Stable canonical-input hash for valid input.
    """

    is_valid: bool
    diagnostics: tuple[ConfigurationDiagnostic, ...] = ()
    configuration_fingerprint: str | None = None


@dataclass(frozen=True)
class ProvenanceEdge:
    """A directed explanation edge from input data to a derived diagnostic fact.

    Fields:
        source: Identifier of the originating configuration fact.
        target: Identifier of the diagnostic fact produced from the source.
        relationship: Machine-readable description of how source affects target.
        subjects: Courses, faculty, or resources involved in the relationship.
    """

    source: str
    target: str
    relationship: str
    subjects: tuple[str, ...] = ()


@dataclass(frozen=True)
class ScheduleDiagnosis:
    """Result of checking the hard scheduling constraints without optimization.

    Fields:
        status: Solver status: ``satisfiable``, ``unsatisfiable``, or ``unknown``.
        conflicting_constraints: Primary unsatisfiable rule set, subset-minimized
            when ``core_is_minimal`` is true.
        alternative_conflict_sets: Additional bounded subset-minimal rule sets.
        supporting_facts: Derived facts needed to interpret the primary conflict.
        relaxation_suggestions: Ranked configuration changes suggested by conflicts.
        repair_sets: Solver-verified rule relaxations that restore feasibility.
        candidate_domains: Static candidate-domain analysis for every course.
        capacity_analysis: Necessary-condition capacity checks.
        day_feasibility: Faculty/day availability and meeting-pattern matrix.
        preflight_findings: Actionable failures found without solver search.
        provenance: Directed explanation links from inputs to findings.
        configuration_fingerprint: Stable hash identifying the diagnosed input.
        core_is_minimal: Whether the primary core was subset-minimized.
        alternative_cores_complete: Whether bounded alternative-core search exhausted its frontier.
        repair_sets_complete: Whether bounded repair search exhausted its frontier.
        diagnostic_completeness: Machine-readable scope of completed analysis.
        diagnostic_version: Version of the diagnostic payload contract.
        elapsed_ms: Wall-clock diagnostic duration in milliseconds.
        solver_timeout_ms: Per-check timeout applied during diagnosis, when configured.
        reason: Solver-provided explanation when status is ``unknown``.
    """

    status: Literal["satisfiable", "unsatisfiable", "unknown"]
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
    diagnostic_version: str = "3"
    elapsed_ms: int = 0
    solver_timeout_ms: int | None = None
    reason: str | None = None


@dataclass(frozen=True)
class ConstraintDiagnostic:
    """One scheduling-rule finding or unsatisfiable-core member.

    Fields:
        kind: Stable machine-readable rule family.
        subjects: Courses, faculty, days, or resources involved in the rule.
        message: Human-readable explanation of the finding.
        code: Optional stable external diagnostic code.
        locations: JSON Pointers to relevant configuration values.
    """

    kind: str
    subjects: tuple[str, ...]
    message: str
    code: str | None = None
    locations: tuple[str, ...] = ()


@dataclass(frozen=True)
class CandidateDomainDiagnostic:
    """The remaining candidate domain for one course after static filtering.

    Fields:
        course: Display identifier for the course section.
        locations: JSON Pointers defining the course domain.
        faculty_candidates: Eligible faculty after normalization.
        faculty_origin: Whether faculty were configured or derived from preferences.
        room_candidates: Eligible room labels.
        lab_candidates: Eligible lab labels.
        section_capacity: Expected enrollment that resources must accommodate.
        capacity_compatible_room_candidates: Allowed rooms large enough for the section.
        capacity_compatible_lab_candidates: Allowed labs large enough for the section.
        room_capacity_rejections: Bounded explanations for undersized allowed rooms.
        room_capacity_rejection_count: Total undersized allowed-room count.
        room_capacity_rejections_truncated: Whether room rejection details were capped.
        lab_capacity_rejections: Bounded explanations for undersized allowed labs.
        lab_capacity_rejection_count: Total undersized allowed-lab count.
        lab_capacity_rejections_truncated: Whether lab rejection details were capped.
        compatible_time_patterns: Meeting patterns matching credits and lab semantics.
        availability_by_faculty: Per-faculty availability summaries.
        rejected_patterns: Bounded explanations for excluded patterns.
        rejected_pattern_count: Total excluded patterns before truncation.
        rejected_patterns_truncated: Whether the rejected-pattern list is incomplete.
        modality: Required delivery composition for compatible meeting patterns.
        required_room_features: Feature tags required on the lecture room.
        required_lab_features: Feature tags required on every lab.
        feature_compatible_room_candidates: Allowed rooms providing all required features.
        feature_compatible_lab_candidates: Allowed labs providing all required features.
        reserve_room_during_lab: Whether lab meetings also consume the lecture room.
    """

    course: str
    locations: tuple[str, ...]
    faculty_candidates: tuple[str, ...]
    faculty_origin: str
    room_candidates: tuple[str, ...]
    lab_candidates: tuple[str, ...]
    section_capacity: int
    capacity_compatible_room_candidates: tuple[str, ...]
    capacity_compatible_lab_candidates: tuple[str, ...]
    room_capacity_rejections: tuple[ConstraintDiagnostic, ...]
    room_capacity_rejection_count: int
    room_capacity_rejections_truncated: bool
    lab_capacity_rejections: tuple[ConstraintDiagnostic, ...]
    lab_capacity_rejection_count: int
    lab_capacity_rejections_truncated: bool
    compatible_time_patterns: tuple[str, ...]
    availability_by_faculty: tuple[ConstraintDiagnostic, ...]
    rejected_patterns: tuple[ConstraintDiagnostic, ...]
    rejected_pattern_count: int
    rejected_patterns_truncated: bool
    modality: str = "in_person"
    required_room_features: tuple[str, ...] = ()
    required_lab_features: tuple[str, ...] = ()
    feature_compatible_room_candidates: tuple[str, ...] = ()
    feature_compatible_lab_candidates: tuple[str, ...] = ()
    reserve_room_during_lab: bool = True


@dataclass(frozen=True)
class CapacityDiagnostic:
    """A necessary-condition capacity check independent of solver search.

    Fields:
        kind: Stable machine-readable capacity-check family.
        subjects: Faculty, courses, days, or resources included in the check.
        message: Human-readable explanation of the compared quantities.
        required: Required capacity or candidate count.
        available: Available capacity or candidate count.
        locations: JSON Pointers controlling the compared quantities.
    """

    kind: str
    subjects: tuple[str, ...]
    message: str
    required: int
    available: int
    locations: tuple[str, ...] = ()


@dataclass(frozen=True)
class DayFeasibilityDiagnostic:
    """One cell of the faculty/day availability and pattern-feasibility matrix.

    Fields:
        faculty: Faculty member represented by this matrix cell.
        day: Weekday name represented by this matrix cell.
        availability_windows: Configured availability windows on the day.
        eligible_courses: Courses this faculty could teach.
        compatible_pattern_count: Eligible patterns containing the day.
        available_pattern_count: Compatible patterns inside faculty availability.
        is_mandatory: Whether the faculty must teach on this day.
        locations: JSON Pointers relevant to this matrix cell.
    """

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
    """A verified rule set whose relaxation restores feasibility.

    Fields:
        relaxed_constraints: Business rules excluded during the verification check.
        verified: Whether the solver confirmed the remaining rules are satisfiable.
        message: Human-readable guidance for translating relaxations into edits.
    """

    relaxed_constraints: tuple[ConstraintDiagnostic, ...]
    verified: bool
    message: str


@dataclass(frozen=True)
class FacultyWorkloadDiagnostic:
    """A faculty member's assigned load with its configured bounds.

    Fields:
        faculty: Faculty member summarized by this record.
        credits: Total assigned course credits.
        minimum_credits: Configured minimum credit load.
        maximum_credits: Configured maximum credit load.
        teaching_days: Sorted weekday names containing assignments.
        maximum_days: Configured maximum teaching-day count.
        distinct_courses: Number of distinct assigned course identifiers.
        unique_course_limit: Configured distinct-course limit.
        mandatory_days_satisfied: Whether every mandatory day is represented.
        locations: JSON Pointers defining this faculty policy.
    """

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
    """One resource's assignments and any detected collisions.

    Fields:
        kind: Resource kind, currently ``room`` or ``lab``.
        resource: Configured resource label.
        assignments: Course sections assigned to the resource.
        collisions: Independent overlap findings for those assignments.
        capacity: Configured student capacity, or ``None`` for an unknown resource in a mutated schedule.
        maximum_assigned_section_capacity: Largest assigned section using the resource.
        capacity_violations: Assignments whose section capacity exceeds the resource.
    """

    kind: str
    resource: str
    assignments: tuple[str, ...]
    capacity: int | None
    maximum_assigned_section_capacity: int
    collisions: tuple[ConstraintDiagnostic, ...] = ()
    capacity_violations: tuple[ConstraintDiagnostic, ...] = ()


@dataclass(frozen=True)
class ObjectiveScoreDiagnostic:
    """Score and independent upper bound for one enabled soft objective.

    Fields:
        objective: Stable optimizer objective name.
        score: Score achieved by the audited schedule.
        independent_upper_bound: Per-item upper bound ignoring competing constraints.
        message: Human-readable score summary.
    """

    objective: str
    score: int
    independent_upper_bound: int
    message: str


@dataclass(frozen=True)
class ScheduleAudit:
    """Independent post-generation hard-rule and objective audit.

    Fields:
        is_valid: Whether no independent hard-rule violations were found.
        constraint_violations: Ordered hard-rule findings.
        faculty_workloads: Workload summary for every configured faculty member.
        resource_usage: Usage and collision summaries for assigned rooms and labs.
        objective_scores: Scores for every enabled optimization objective.
        preference_outcomes: Explanations for available objective points not selected.
    """

    is_valid: bool
    constraint_violations: tuple[ConstraintDiagnostic, ...]
    faculty_workloads: tuple[FacultyWorkloadDiagnostic, ...]
    resource_usage: tuple[ResourceUsageDiagnostic, ...]
    objective_scores: tuple[ObjectiveScoreDiagnostic, ...]
    preference_outcomes: tuple[ConstraintDiagnostic, ...]


@dataclass(frozen=True)
class RelaxationSuggestion:
    """A targeted configuration change that may restore feasibility.

    Fields:
        kind: Stable machine-readable suggested edit family.
        subjects: Courses, faculty, days, or resources affected by the edit.
        message: Human-readable description of the candidate change.
        priority: One-based recommendation order within the diagnosis.
    """

    kind: str
    subjects: tuple[str, ...]
    message: str
    priority: int = 1
