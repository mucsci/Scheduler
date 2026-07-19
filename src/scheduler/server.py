import asyncio
import os
import time
import uuid
from collections.abc import Generator
from concurrent.futures import Future, ThreadPoolExecutor
from contextlib import asynccontextmanager
from dataclasses import dataclass, field
from typing import Any, cast

import click
from fastapi import BackgroundTasks, FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, ConfigDict, Field

from .config import CombinedConfig
from .logging import configure_logging, logger
from .scheduler import (
    CandidateDomainDiagnostic,
    CapacityDiagnostic,
    ConfigurationDiagnostic,
    ConstraintDiagnostic,
    CourseInstance,
    DayFeasibilityDiagnostic,
    ProvenanceEdge,
    RepairSetDiagnostic,
    ScheduleAudit,
    ScheduleDiagnosis,
    Scheduler,
    validate_combined_config_data,
)

# Global thread pool executor for Z3 operations
z3_executor: ThreadPoolExecutor = ThreadPoolExecutor(max_workers=16, thread_name_prefix="z3-solver")


@dataclass(frozen=True)
class ApiLimits:
    """
    Runtime safeguards applied only to HTTP schedule-generation requests.

    Fields:
        max_active_sessions: Maximum number of sessions retained concurrently.
        max_courses: Maximum courses accepted in one submitted configuration.
        max_schedules_per_session: Maximum requested enumeration limit per session.
        max_candidate_slots: Maximum arithmetic preflight estimate of candidate slots.
        solver_timeout_ms: Per-check Z3 timeout passed to each API scheduler.
        session_ttl_seconds: Idle duration after which inactive sessions are reaped.
    """

    max_active_sessions: int = 16
    max_courses: int = 100
    max_schedules_per_session: int = 100
    max_candidate_slots: int = 10_000
    solver_timeout_ms: int = 30_000
    session_ttl_seconds: int = 1_800


def _positive_env(name: str, default: int) -> int:
    """Read one positive integer environment setting, falling back safely."""
    try:
        value = int(os.getenv(name, str(default)))
    except ValueError:
        return default
    return value if value > 0 else default


def _load_api_limits() -> ApiLimits:
    return ApiLimits(
        max_active_sessions=_positive_env("SCHEDULER_API_MAX_ACTIVE_SESSIONS", 16),
        max_courses=_positive_env("SCHEDULER_API_MAX_COURSES", 100),
        max_schedules_per_session=_positive_env("SCHEDULER_API_MAX_SCHEDULES", 100),
        max_candidate_slots=_positive_env("SCHEDULER_API_MAX_CANDIDATE_SLOTS", 10_000),
        solver_timeout_ms=_positive_env("SCHEDULER_API_SOLVER_TIMEOUT_MS", 30_000),
        session_ttl_seconds=_positive_env("SCHEDULER_API_SESSION_TTL_SECONDS", 1_800),
    )


API_LIMITS = _load_api_limits()


# Data models for API requests/responses
SubmitRequest = CombinedConfig


class TimeInstanceResponse(BaseModel):
    """One meeting time block within a scheduled course (JSON shape)."""

    model_config = ConfigDict(extra="forbid")

    day: int = Field(description="Weekday as `Day` enum value (1=Monday … 5=Friday).")
    start: int = Field(description="Start time in minutes since midnight.")
    duration: int = Field(description="Duration in minutes.")


class CourseInstanceResponse(BaseModel):
    """
    One course assignment in the JSON representation of a generated schedule.

    Fields:
        course: Course identifier including its generated section suffix.
        faculty: Faculty member assigned to teach the course.
        times: Ordered lecture and optional lab meeting instances.
        room: Assigned lecture room, or null when absent.
        lab: Assigned lab resource, or null for a no-lab course.
        lab_index: Index of the lab meeting in ``times``, or null for no lab.
    """

    model_config = ConfigDict(extra="forbid")

    course: str = Field(description='Course id with section, e.g. `"CS101.01"`.')
    faculty: str
    times: list[TimeInstanceResponse]
    room: str | None = Field(default=None, description="Assigned room when present.")
    lab: str | None = Field(default=None, description="Assigned lab when present.")
    lab_index: int | None = Field(
        default=None,
        description="When `lab` is set, index into `times` for the lab meeting.",
    )


def _schedule_response_rows(courses: list[CourseInstance]) -> list[CourseInstanceResponse]:
    return [CourseInstanceResponse.model_validate(c.model_dump(by_alias=True, exclude_none=True)) for c in courses]


class HealthCheck(BaseModel):
    """
    Health check response model.

    **Usage:**
    ```python
    HealthCheck(status="healthy", active_sessions=0)
    ```

    **Fields:**
    - status: Health status of the service
    - active_sessions: Number of active schedule generation sessions
    """

    status: str
    active_sessions: int


class SubmitResponse(BaseModel):
    """
    Response model for schedule submission requests.

    **Usage:**
    ```python
    SubmitResponse(schedule_id="...", endpoint="/schedules/...")
    ```

    **Fields:**
    - schedule_id: Unique identifier for the generated schedule session
    - endpoint: URL endpoint to access the schedule
    """

    schedule_id: str
    endpoint: str


class MessageResponse(BaseModel):
    """
    Generic message response model.

    **Usage:**
    ```python
    MessageResponse(message="ok")
    ```

    **Fields:**
    - message: Response message text
    """

    message: str


class GenerateAllResponse(BaseModel):
    """
    Response model for generate-all schedule requests.

    **Usage:**
    ```python
    GenerateAllResponse(message='...', current_count=1, target_count=10)
    ```

    **Fields:**
    - message: Status message about the generation process
    - current_count: Number of schedules already generated
    - target_count: Target number of schedules to generate
    """

    message: str
    current_count: int
    target_count: int


class ScheduleResponse(BaseModel):
    """
    Response model for schedule retrieval requests.

    **Usage:**
    ```python
    ScheduleResponse(schedule_id='...', schedule=[...], index=0, total_generated=1)
    ```

    **Fields:**
    - schedule_id: Unique identifier for the schedule session
    - schedule: Generated schedule as `list[CourseInstanceResponse]` (typed JSON rows)
    - index: Index of this schedule in the generation sequence
    - total_generated: Total number of schedules generated so far
    """

    schedule_id: str
    schedule: list[CourseInstanceResponse]
    index: int
    total_generated: int


class ScheduleDetailsResponse(CombinedConfig):
    """
    Response model for schedule details requests.

    Inherits all fields from CombinedConfig and adds:

    **Usage:**
    ```python
    ScheduleDetailsResponse(schedule_id='...', total_generated=0, **combined.model_dump())
    ```

    **Fields:**
    - schedule_id: Unique identifier for the schedule session
    - total_generated: Total number of schedules generated
    """

    schedule_id: str
    total_generated: int


class ScheduleCountResponse(BaseModel):
    """
    Response model for schedule count requests.

    **Usage:**
    ```python
    ScheduleCountResponse(schedule_id='...', current_count=2, limit=10, is_complete=False)
    ```

    **Fields:**
    - schedule_id: Unique identifier for the schedule session
    - current_count: Number of schedules currently generated
    - limit: Maximum number of schedules to generate
    - is_complete: Whether all schedules have been generated
    """

    schedule_id: str
    current_count: int
    limit: int
    is_complete: bool


class SessionDiagnosticResponse(BaseModel):
    """
    Operational state, resource safeguards, and completion metadata for a session.

    Fields:
        schedule_id: Unique identifier for the generation session.
        state: Overall state: initializing, generating, complete, or ready.
        background_state: Lifecycle state of the generate-all background task.
        background_error: Last background failure text, if generation failed.
        completion_reason: Machine-oriented explanation for terminal generation.
        generated_schedules: Number of schedules currently retained.
        requested_schedule_limit: Client-requested maximum enumeration count.
        enumeration_scope: Whether results exhausted the space or stopped at a bound.
        known_distinct_schedules: Distinct schedules observed in this session.
        idle_seconds: Rounded seconds since the session was last accessed.
        session_ttl_seconds: Configured idle expiry threshold.
        solver_timeout_ms: Configured timeout for each solver check.
        max_courses: Configured course-count submission limit.
        max_candidate_slots: Configured candidate-slot estimate limit.
        max_schedules_per_session: Configured per-session enumeration limit.
    """

    schedule_id: str
    state: str
    background_state: str
    background_error: str | None
    completion_reason: str | None
    generated_schedules: int
    requested_schedule_limit: int
    enumeration_scope: str
    known_distinct_schedules: int
    idle_seconds: int
    session_ttl_seconds: int
    solver_timeout_ms: int
    max_courses: int
    max_candidate_slots: int
    max_schedules_per_session: int


class ScheduleDiagnosisResponse(BaseModel):
    """
    Structured hard-constraint feasibility analysis for a schedule session.

    Fields:
        schedule_id: Session whose configuration was diagnosed.
        status: Solver feasibility status such as sat, unsat, or unknown.
        conflicting_constraints: Minimal primary set of conflicting hard rules.
        alternative_conflict_sets: Other independently discovered conflict cores.
        supporting_facts: Relevant non-core facts that explain the conflict.
        relaxation_suggestions: Ranked configuration changes derived from findings.
        repair_sets: Solver-verified combinations of relaxations.
        candidate_domains: Per-course candidate resources and eliminations.
        capacity_analysis: Necessary resource and workload capacity calculations.
        day_feasibility: Per-faculty, per-day availability feasibility facts.
        preflight_findings: Static contradictions found before core extraction.
        provenance: Edges linking facts, configuration, and conclusions.
        configuration_fingerprint: Stable digest of the diagnosed configuration.
        core_is_minimal: Whether the primary conflict core was proven minimal.
        alternative_cores_complete: Whether alternative-core enumeration completed.
        repair_sets_complete: Whether repair-set enumeration completed.
        diagnostic_completeness: Overall completeness classification.
        diagnostic_version: Version of the diagnostic response semantics.
        elapsed_ms: Total diagnostic execution time in milliseconds.
        solver_timeout_ms: Solver timeout used, or null when no timeout was set.
        reason: Solver or diagnostic explanation for an indeterminate result.
    """

    schedule_id: str
    status: str
    conflicting_constraints: list["ConstraintDiagnosticResponse"]
    alternative_conflict_sets: list[list["ConstraintDiagnosticResponse"]]
    supporting_facts: list["ConstraintDiagnosticResponse"]
    relaxation_suggestions: list["RelaxationSuggestionResponse"]
    repair_sets: list["RepairSetDiagnosticResponse"]
    candidate_domains: list["CandidateDomainDiagnosticResponse"]
    capacity_analysis: list["CapacityDiagnosticResponse"]
    day_feasibility: list["DayFeasibilityDiagnosticResponse"]
    preflight_findings: list["ConstraintDiagnosticResponse"]
    provenance: list["ProvenanceEdgeResponse"]
    configuration_fingerprint: str | None
    core_is_minimal: bool | None
    alternative_cores_complete: bool | None
    repair_sets_complete: bool | None
    diagnostic_completeness: str
    diagnostic_version: str
    elapsed_ms: int
    solver_timeout_ms: int | None
    reason: str | None


class ConstraintDiagnosticResponse(BaseModel):
    """
    One user-facing hard rule, finding, or supporting diagnostic fact.

    Fields:
        kind: Stable category of the diagnostic rule.
        subjects: Course, faculty, day, or resource identifiers involved.
        message: Human-readable explanation of the rule or finding.
        code: Stable machine-readable diagnostic code when available.
        locations: Source configuration paths contributing to the finding.
    """

    kind: str
    subjects: list[str]
    message: str
    code: str | None = None
    locations: list[str] = []


class CandidateDomainDiagnosticResponse(BaseModel):
    """
    Static resource and time-domain analysis for one configured course.

    Fields:
        course: Course identifier being analyzed.
        locations: Source paths that define the course domain.
        faculty_candidates: Faculty eligible to teach the course.
        faculty_origin: Whether eligibility was explicit or preference-derived.
        room_candidates: Rooms eligible for the course.
        lab_candidates: Labs eligible for the course, empty for no-lab courses.
        compatible_time_patterns: Time-slot patterns compatible with course semantics.
        availability_by_faculty: Availability findings for each candidate faculty.
        rejected_patterns: Detailed reasons sampled from rejected patterns.
        rejected_pattern_count: Total number of rejected patterns.
        rejected_patterns_truncated: Whether detailed rejection output was capped.
    """

    course: str
    locations: list[str]
    faculty_candidates: list[str]
    faculty_origin: str
    room_candidates: list[str]
    lab_candidates: list[str]
    compatible_time_patterns: list[str]
    availability_by_faculty: list[ConstraintDiagnosticResponse]
    rejected_patterns: list[ConstraintDiagnosticResponse]
    rejected_pattern_count: int
    rejected_patterns_truncated: bool


class ProvenanceEdgeResponse(BaseModel):
    """
    Directed relationship connecting two diagnostic facts or configuration values.

    Fields:
        source: Identifier of the source fact or configuration node.
        target: Identifier of the conclusion or dependent fact.
        relationship: Semantic label describing how source affects target.
        subjects: Domain identifiers shared by the relationship.
    """

    source: str
    target: str
    relationship: str
    subjects: list[str]


class CapacityDiagnosticResponse(BaseModel):
    """
    Necessary-condition comparison between required and available capacity.

    Fields:
        kind: Capacity category such as faculty credits or resource slots.
        subjects: Domain identifiers participating in the calculation.
        message: Human-readable interpretation of the comparison.
        required: Minimum capacity demanded by the configuration.
        available: Capacity available under the analyzed restrictions.
        locations: Configuration paths supporting the calculation.
    """

    kind: str
    subjects: list[str]
    message: str
    required: int
    available: int
    locations: list[str]


class DayFeasibilityDiagnosticResponse(BaseModel):
    """
    Feasibility summary for one faculty member on one teaching day.

    Fields:
        faculty: Faculty member whose day is analyzed.
        day: Weekday name under consideration.
        availability_windows: Configured time windows on that day.
        eligible_courses: Courses the faculty member may teach.
        compatible_pattern_count: Patterns compatible before availability filtering.
        available_pattern_count: Compatible patterns fitting availability windows.
        is_mandatory: Whether faculty policy requires teaching on this day.
        locations: Configuration paths supporting the analysis.
    """

    faculty: str
    day: str
    availability_windows: list[str]
    eligible_courses: list[str]
    compatible_pattern_count: int
    available_pattern_count: int
    is_mandatory: bool
    locations: list[str]


class RepairSetDiagnosticResponse(BaseModel):
    """
    A combination of hard-rule relaxations tested for restored feasibility.

    Fields:
        relaxed_constraints: Rules omitted together during repair verification.
        verified: Whether the solver confirmed feasibility under those relaxations.
        message: Human-readable explanation of the repair result.
    """

    relaxed_constraints: list[ConstraintDiagnosticResponse]
    verified: bool
    message: str


class FacultyWorkloadDiagnosticResponse(BaseModel):
    """
    Independently computed workload and policy compliance for one faculty member.

    Fields:
        faculty: Faculty member whose assignments are summarized.
        credits: Total assigned course credits.
        minimum_credits: Configured minimum credit requirement.
        maximum_credits: Configured maximum credit allowance.
        teaching_days: Distinct weekdays containing assigned meetings.
        maximum_days: Configured maximum number of teaching days.
        distinct_courses: Count of distinct base course identifiers assigned.
        unique_course_limit: Configured distinct-course limit.
        mandatory_days_satisfied: Whether all required teaching days are used.
        locations: Source paths defining the faculty workload policy.
    """

    faculty: str
    credits: int
    minimum_credits: int
    maximum_credits: int
    teaching_days: list[str]
    maximum_days: int
    distinct_courses: int
    unique_course_limit: int
    mandatory_days_satisfied: bool
    locations: list[str]


class ResourceUsageDiagnosticResponse(BaseModel):
    """
    Assignment and collision summary for one room, lab, or faculty resource.

    Fields:
        kind: Resource category represented by this row.
        resource: Configured resource identifier.
        assignments: Course assignments consuming the resource.
        collisions: Detected overlap violations involving the resource.
    """

    kind: str
    resource: str
    assignments: list[str]
    collisions: list[ConstraintDiagnosticResponse]


class ObjectiveScoreDiagnosticResponse(BaseModel):
    """
    Explain one enabled optimization objective's realized schedule score.

    Fields:
        objective: Stable optimizer objective identifier.
        score: Preference score achieved by the audited schedule.
        independent_upper_bound: Per-assignment upper bound ignoring interactions.
        message: Human-readable interpretation of the objective result.
    """

    objective: str
    score: int
    independent_upper_bound: int
    message: str


class ScheduleAuditResponse(BaseModel):
    """
    Independent hard-rule verification and preference explanation for one schedule.

    Fields:
        schedule_id: Session containing the audited schedule.
        index: Zero-based generated-schedule index.
        is_valid: Whether independent auditing found no hard-rule violations.
        constraint_violations: All hard-rule violations detected by the auditor.
        faculty_workloads: Workload summaries for every configured faculty member.
        resource_usage: Usage and collision summaries for shared resources.
        objective_scores: Scores for enabled optimization objectives.
        preference_outcomes: Per-assignment preference explanations.
    """

    schedule_id: str
    index: int
    is_valid: bool
    constraint_violations: list[ConstraintDiagnosticResponse]
    faculty_workloads: list[FacultyWorkloadDiagnosticResponse]
    resource_usage: list[ResourceUsageDiagnosticResponse]
    objective_scores: list[ObjectiveScoreDiagnosticResponse]
    preference_outcomes: list[ConstraintDiagnosticResponse]


class ConfigurationDiagnosticResponse(BaseModel):
    """
    One structured schema or cross-reference error in raw configuration input.

    Fields:
        code: Stable machine-readable validation code.
        path: Primary JSON-style path containing the invalid value.
        message: Human-readable explanation of the problem.
        value: Safe textual representation of the invalid value, when available.
        related_paths: Other configuration paths involved in the same problem.
    """

    code: str
    path: str
    message: str
    value: str | None = None
    related_paths: list[str]


class ConfigurationValidationResponse(BaseModel):
    """
    Non-throwing schema and cross-reference validation result for raw JSON input.

    Fields:
        is_valid: Whether the payload can construct a valid combined configuration.
        diagnostics: Ordered structured errors; empty when validation succeeds.
        configuration_fingerprint: Stable digest for valid normalized input only.
    """

    is_valid: bool
    diagnostics: list[ConfigurationDiagnosticResponse]
    configuration_fingerprint: str | None = None


def _constraint_diagnostic_response(diagnostic: "ConstraintDiagnostic") -> ConstraintDiagnosticResponse:
    return ConstraintDiagnosticResponse(
        kind=diagnostic.kind,
        subjects=list(diagnostic.subjects),
        message=diagnostic.message,
        code=diagnostic.code,
        locations=list(diagnostic.locations),
    )


def _candidate_domain_response(domain: CandidateDomainDiagnostic) -> CandidateDomainDiagnosticResponse:
    return CandidateDomainDiagnosticResponse(
        course=domain.course,
        locations=list(domain.locations),
        faculty_candidates=list(domain.faculty_candidates),
        faculty_origin=domain.faculty_origin,
        room_candidates=list(domain.room_candidates),
        lab_candidates=list(domain.lab_candidates),
        compatible_time_patterns=list(domain.compatible_time_patterns),
        availability_by_faculty=[_constraint_diagnostic_response(item) for item in domain.availability_by_faculty],
        rejected_patterns=[_constraint_diagnostic_response(item) for item in domain.rejected_patterns],
        rejected_pattern_count=domain.rejected_pattern_count,
        rejected_patterns_truncated=domain.rejected_patterns_truncated,
    )


def _provenance_response(edge: ProvenanceEdge) -> ProvenanceEdgeResponse:
    return ProvenanceEdgeResponse(
        source=edge.source,
        target=edge.target,
        relationship=edge.relationship,
        subjects=list(edge.subjects),
    )


def _capacity_response(diagnostic: CapacityDiagnostic) -> CapacityDiagnosticResponse:
    return CapacityDiagnosticResponse(
        kind=diagnostic.kind,
        subjects=list(diagnostic.subjects),
        message=diagnostic.message,
        required=diagnostic.required,
        available=diagnostic.available,
        locations=list(diagnostic.locations),
    )


def _day_feasibility_response(diagnostic: DayFeasibilityDiagnostic) -> DayFeasibilityDiagnosticResponse:
    return DayFeasibilityDiagnosticResponse(
        faculty=diagnostic.faculty,
        day=diagnostic.day,
        availability_windows=list(diagnostic.availability_windows),
        eligible_courses=list(diagnostic.eligible_courses),
        compatible_pattern_count=diagnostic.compatible_pattern_count,
        available_pattern_count=diagnostic.available_pattern_count,
        is_mandatory=diagnostic.is_mandatory,
        locations=list(diagnostic.locations),
    )


def _repair_set_response(repair_set: RepairSetDiagnostic) -> RepairSetDiagnosticResponse:
    return RepairSetDiagnosticResponse(
        relaxed_constraints=[_constraint_diagnostic_response(item) for item in repair_set.relaxed_constraints],
        verified=repair_set.verified,
        message=repair_set.message,
    )


def _schedule_audit_response(schedule_id: str, index: int, audit: ScheduleAudit) -> ScheduleAuditResponse:
    return ScheduleAuditResponse(
        schedule_id=schedule_id,
        index=index,
        is_valid=audit.is_valid,
        constraint_violations=[_constraint_diagnostic_response(item) for item in audit.constraint_violations],
        faculty_workloads=[
            FacultyWorkloadDiagnosticResponse(
                faculty=item.faculty,
                credits=item.credits,
                minimum_credits=item.minimum_credits,
                maximum_credits=item.maximum_credits,
                teaching_days=list(item.teaching_days),
                maximum_days=item.maximum_days,
                distinct_courses=item.distinct_courses,
                unique_course_limit=item.unique_course_limit,
                mandatory_days_satisfied=item.mandatory_days_satisfied,
                locations=list(item.locations),
            )
            for item in audit.faculty_workloads
        ],
        resource_usage=[
            ResourceUsageDiagnosticResponse(
                kind=item.kind,
                resource=item.resource,
                assignments=list(item.assignments),
                collisions=[_constraint_diagnostic_response(collision) for collision in item.collisions],
            )
            for item in audit.resource_usage
        ],
        objective_scores=[
            ObjectiveScoreDiagnosticResponse(
                objective=item.objective,
                score=item.score,
                independent_upper_bound=item.independent_upper_bound,
                message=item.message,
            )
            for item in audit.objective_scores
        ],
        preference_outcomes=[_constraint_diagnostic_response(item) for item in audit.preference_outcomes],
    )


def _configuration_diagnostic_response(diagnostic: ConfigurationDiagnostic) -> ConfigurationDiagnosticResponse:
    return ConfigurationDiagnosticResponse(
        code=diagnostic.code,
        path=diagnostic.path,
        message=diagnostic.message,
        value=diagnostic.value,
        related_paths=list(diagnostic.related_paths),
    )


class RelaxationSuggestionResponse(BaseModel):
    """
    One ranked, directly derived configuration change that may restore feasibility.

    Fields:
        kind: Category of configuration relaxation being suggested.
        subjects: Courses, faculty, days, or resources affected by the change.
        message: Human-readable proposed change and rationale.
        priority: Relative ranking, with lower values presented first.
    """

    kind: str
    subjects: list[str]
    message: str
    priority: int


class ErrorResponse(BaseModel):
    """
    Error response model for API errors.

    **Usage:**
    ```python
    ErrorResponse(error="bad_request", message="...")
    ```

    **Fields:**
    - error: Error type or code
    - message: Detailed error message
    """

    error: str
    message: str


@dataclass
class ScheduleSession:
    """
    Represents an active schedule generation session.

    Fields:
        scheduler: Initialized scheduler, or null while construction is queued.
        scheduler_future: Thread-pool future performing scheduler construction.
        generator: Lazily created model generator for this session.
        full_config: Validated immutable-in-practice request configuration.
        generated_schedules: API-serialized schedules retained by index.
        generated_models: Original model objects retained for independent auditing.
        generation_lock: Async lock serializing generator, diagnosis, and audit access.
        background_task: At most one active generate-all task.
        created_at: Monotonic timestamp at session creation.
        last_accessed_at: Monotonic timestamp used for idle expiry.
        is_exhausted: Whether no further schedules may be generated.
        completion_reason: Machine-oriented terminal or cancellation reason.
        background_error: Last unexpected background-generation error text.
    """

    scheduler: Scheduler | None
    scheduler_future: Future[Scheduler | None] | None
    generator: Generator[list[CourseInstance], None, None] | None
    full_config: CombinedConfig
    generated_schedules: list[list[CourseInstanceResponse]]
    generated_models: list[list[CourseInstance]] = field(default_factory=list)
    generation_lock: asyncio.Lock = field(default_factory=asyncio.Lock)
    background_task: asyncio.Task[None] | None = None
    created_at: float = field(default_factory=time.monotonic)
    last_accessed_at: float = field(default_factory=time.monotonic)
    is_exhausted: bool = False
    completion_reason: str | None = None
    background_error: str | None = None


# Global storage for active sessions
schedule_sessions: dict[str, ScheduleSession] = {}


def cleanup_session(schedule_id: str):
    """
    Remove an API session and cancel work still associated with it.

    Args:
        schedule_id: Unique identifier of the session to remove.

    Returns:
        None.

    Raises:
        None intentionally; task and future cancellation requests are best-effort.

    Behavior:
        If the session exists, its unfinished background task and scheduler future
        are cancelled before the registry entry is deleted. Missing identifiers are
        logged and otherwise treated as an idempotent cleanup. Cancellation does not
        synchronously wait for an already running thread-pool operation to stop.
    """
    logger.debug(f"Cleaning up session {schedule_id}")
    logger.debug(f"Active sessions before cleanup: {list(schedule_sessions.keys())}")

    if schedule_id in schedule_sessions:
        session = schedule_sessions[schedule_id]

        if session.background_task is not None and not session.background_task.done():
            session.background_task.cancel()
            logger.debug(f"Cancelled background task for session {schedule_id}")
        if session.scheduler_future is not None:
            session.scheduler_future.cancel()

        del schedule_sessions[schedule_id]
        logger.debug(f"Removed session {schedule_id} from schedule_sessions")
    else:
        logger.warning(f"Session {schedule_id} not found in schedule_sessions during cleanup")

    logger.debug(f"Active sessions after cleanup: {list(schedule_sessions.keys())}")
    logger.info(f"Cleaned up session {schedule_id}")


def _session_has_active_work(session: ScheduleSession) -> bool:
    return (session.scheduler_future is not None and not session.scheduler_future.done()) or (
        session.background_task is not None and not session.background_task.done()
    )


def _session_diagnostic_response(schedule_id: str, session: ScheduleSession) -> SessionDiagnosticResponse:
    """Render live session state without invoking the solver or generator."""
    if session.scheduler_future is not None and not session.scheduler_future.done():
        state = "initializing"
    elif session.background_task is not None and not session.background_task.done():
        state = "generating"
    elif session.is_exhausted or len(session.generated_schedules) >= session.full_config.limit:
        state = "complete"
    else:
        state = "ready"

    if session.background_task is None:
        background_state = "not_started"
    elif not session.background_task.done():
        background_state = "running"
    elif session.background_task.cancelled():
        background_state = "cancelled"
    elif session.background_error:
        background_state = "failed"
    else:
        background_state = "completed"

    return SessionDiagnosticResponse(
        schedule_id=schedule_id,
        state=state,
        background_state=background_state,
        background_error=session.background_error,
        completion_reason=session.completion_reason,
        generated_schedules=len(session.generated_schedules),
        requested_schedule_limit=session.full_config.limit,
        enumeration_scope=(
            "exhausted" if session.completion_reason == "solution_space_exhausted" else "bounded_by_requested_limit"
        ),
        known_distinct_schedules=len(session.generated_schedules),
        idle_seconds=round(time.monotonic() - session.last_accessed_at),
        session_ttl_seconds=API_LIMITS.session_ttl_seconds,
        solver_timeout_ms=API_LIMITS.solver_timeout_ms,
        max_courses=API_LIMITS.max_courses,
        max_candidate_slots=API_LIMITS.max_candidate_slots,
        max_schedules_per_session=API_LIMITS.max_schedules_per_session,
    )


def cleanup_expired_sessions() -> None:
    """
    Remove every inactive API session whose idle lifetime has expired.

    Args:
        None.

    Returns:
        None.

    Raises:
        None intentionally; individual cleanup operations are best-effort.

    Behavior:
        A monotonic timestamp is sampled once, then a snapshot of the session
        registry is inspected. Sessions with queued scheduler construction or a
        running background task are preserved regardless of age. Other sessions at
        or beyond the configured TTL are passed to ``cleanup_session``.
    """
    now = time.monotonic()
    for schedule_id, session in list(schedule_sessions.items()):
        if not _session_has_active_work(session) and now - session.last_accessed_at >= API_LIMITS.session_ttl_seconds:
            cleanup_session(schedule_id)


def _count_meeting_starts(meeting, time_blocks, fallback_start: str | None) -> int:
    start_time = meeting.start_time or fallback_start
    total = 0
    for block in time_blocks:
        block_start = int(block.start[:2]) * 60 + int(block.start[3:])
        block_end = int(block.end[:2]) * 60 + int(block.end[3:])
        if start_time is not None:
            requested = int(start_time[:2]) * 60 + int(start_time[3:])
            total += int(block_start <= requested and requested + meeting.duration <= block_end)
        elif block_start + meeting.duration <= block_end:
            total += (block_end - block_start - meeting.duration) // block.spacing + 1
    return total


def _estimate_candidate_slots(request: CombinedConfig, limit: int) -> int:
    """Cheap upper bound for the Cartesian products used by TimeSlotGenerator."""
    required_credits = {course.credits for course in request.config.courses}
    estimate = 0
    for pattern in request.time_slot_config.classes:
        if pattern.disabled or pattern.credits not in required_credits:
            continue
        combinations = 1
        for meeting in pattern.meetings:
            combinations *= _count_meeting_starts(
                meeting,
                request.time_slot_config.times.get(meeting.day, []),
                pattern.start_time,
            )
            if combinations > limit:
                return combinations
        estimate += combinations
        if estimate > limit:
            return estimate
    return estimate


def _validate_submission_limits(request: CombinedConfig) -> None:
    cleanup_expired_sessions()
    if len(schedule_sessions) >= API_LIMITS.max_active_sessions:
        raise HTTPException(status_code=429, detail="Active schedule-session limit reached")
    if len(request.config.courses) > API_LIMITS.max_courses:
        raise HTTPException(status_code=422, detail=f"At most {API_LIMITS.max_courses} courses are allowed per request")
    if request.limit > API_LIMITS.max_schedules_per_session:
        raise HTTPException(
            status_code=422,
            detail=f"At most {API_LIMITS.max_schedules_per_session} schedules may be requested",
        )
    estimate = _estimate_candidate_slots(request, API_LIMITS.max_candidate_slots)
    if estimate > API_LIMITS.max_candidate_slots:
        raise HTTPException(
            status_code=422,
            detail=f"Configuration produces more than {API_LIMITS.max_candidate_slots} candidate time slots",
        )


async def ensure_scheduler_initialized(session_id: str, session: ScheduleSession):
    """
    Await and install the scheduler constructed for an API session.

    Args:
        session_id: Registry identifier used for cleanup and error reporting.
        session: Session whose scheduler future should be resolved.

    Returns:
        None. The resolved scheduler is stored on ``session.scheduler``.

    Raises:
        AssertionError: If an uninitialized session has no construction future.
        HTTPException: With status 422 if asynchronous scheduler construction fails;
            the failed session is removed before the exception is raised.

    Behavior:
        An already initialized scheduler is reused and only refreshes session access
        time. Otherwise the concurrent future is adapted to the active event loop,
        awaited without blocking it, stored exactly once, and marks the session as
        accessed. Construction errors trigger complete session cleanup.
    """
    if session.scheduler is not None:
        session.last_accessed_at = time.monotonic()
        return
    assert session.scheduler_future is not None
    # Wrap the Future in an asyncio.Future so it can be awaited
    try:
        session.scheduler = await asyncio.wrap_future(session.scheduler_future)
        session.last_accessed_at = time.monotonic()
    except Exception as e:
        cleanup_session(session_id)
        raise HTTPException(status_code=422, detail=f"Scheduler initialization failed: {str(e)}") from e


async def ensure_generator_initialized(session_id: str, session: ScheduleSession):
    """
    Lazily create a session's model generator under its generation lock.

    Args:
        session_id: Identifier used in operational logging.
        session: Session on which to install the generator.

    Returns:
        None. The generator is stored on ``session.generator``; if no scheduler is
        available yet, the function returns without changing the session.

    Raises:
        HTTPException: With status 408 when initialization is cancelled, or status
            500 when generator construction fails unexpectedly.

    Behavior:
        Existing generators are reused and refresh access time. Initialization is
        serialized by ``generation_lock`` and checked again after lock acquisition,
        preventing concurrent requests from constructing duplicate generators. The
        scheduler's lazy ``get_models`` call is dispatched through the Z3 executor.
    """
    if session.generator is not None:
        session.last_accessed_at = time.monotonic()
        return
    if session.scheduler is None:
        return

    async with session.generation_lock:
        # Double-check after acquiring lock
        if session.generator is not None:
            return

        # Initialize generator in thread pool
        try:
            session.generator = await asyncio.wrap_future(z3_executor.submit(session.scheduler.get_models))
            session.last_accessed_at = time.monotonic()
            logger.debug(f"Initialized generator for session {session_id}")
        except asyncio.CancelledError:
            logger.warning(f"Generator initialization was cancelled for session {session_id}")
            raise HTTPException(status_code=408, detail="Request timeout") from None
        except Exception as e:
            logger.error(f"Failed to initialize generator for session {session_id}: {e}")
            raise HTTPException(status_code=500, detail=f"Generator initialization failed: {str(e)}") from e


async def _advance_session(schedule_id: str, session: ScheduleSession) -> ScheduleResponse:
    """Advance one generator safely and store exactly one schedule result."""
    async with session.generation_lock:
        if len(session.generated_schedules) >= session.full_config.limit:
            session.is_exhausted = True
            session.completion_reason = "requested_schedule_limit_reached"
            raise HTTPException(
                status_code=400,
                detail=f"All {session.full_config.limit} schedules have been generated",
            )
        if session.is_exhausted:
            raise HTTPException(status_code=400, detail="No more schedules available")
        try:
            assert session.generator is not None
            model = cast(
                list[CourseInstance],
                await asyncio.wrap_future(z3_executor.submit(next, session.generator)),
            )
        except StopIteration:
            session.is_exhausted = True
            session.completion_reason = "solution_space_exhausted"
            raise HTTPException(status_code=400, detail="No more schedules available") from None
        except Exception as e:
            if "StopIteration" in str(e):
                session.is_exhausted = True
                session.completion_reason = "solution_space_exhausted"
                raise HTTPException(status_code=400, detail="No more schedules available") from e
            session.completion_reason = "generation_error"
            raise HTTPException(status_code=500, detail=f"Schedule generation failed: {str(e)}") from e

        rows = _schedule_response_rows(model)
        session.generated_schedules.append(rows)
        session.generated_models.append(model)
        session.last_accessed_at = time.monotonic()
        current_index = len(session.generated_schedules) - 1
        return ScheduleResponse(
            schedule_id=schedule_id,
            schedule=rows,
            index=current_index,
            total_generated=len(session.generated_schedules),
        )


@asynccontextmanager
async def lifespan(app: FastAPI):
    """
    Manage the session reaper and solver executor for the FastAPI application.

    Args:
        app: FastAPI application entering or leaving its lifespan. It is accepted
            for the framework protocol and is not otherwise inspected.

    Returns:
        An asynchronous context manager that yields control once startup is ready.

    Raises:
        BaseException: Any exception from application execution is propagated after
            shutdown cleanup completes.

    Behavior:
        Startup creates one periodic task that expires idle sessions at an interval
        no longer than 60 seconds. Shutdown cancels that reaper, cleans every
        remaining session (including queued initialization and background work),
        and waits for the shared Z3 thread pool to finish shutting down.
    """

    async def reap_expired_sessions() -> None:
        while True:
            await asyncio.sleep(min(60, API_LIMITS.session_ttl_seconds))
            cleanup_expired_sessions()

    reaper = asyncio.create_task(reap_expired_sessions())
    try:
        yield
    finally:
        reaper.cancel()
        for session_id in list(schedule_sessions.keys()):
            cleanup_session(session_id)
        z3_executor.shutdown(wait=True)


app = FastAPI(
    title="Course Scheduler API",
    description="HTTP API for generating course schedules using constraint satisfaction solving",
    version="1.0.0",
    lifespan=lifespan,
)

# CORS: browsers reject allow_origins=["*"] with allow_credentials=True.
# Use CORS_ORIGINS env (comma-separated) for explicit origins + credentials;
# when unset, allow all origins without credentials (suitable for local dev).
_cors_origins_env = os.getenv("CORS_ORIGINS", "").strip()
if _cors_origins_env:
    _cors_origins = [o.strip() for o in _cors_origins_env.split(",") if o.strip()]
    _cors_credentials = True
else:
    _cors_origins = ["*"]
    _cors_credentials = False

app.add_middleware(
    cast(Any, CORSMiddleware),
    allow_origins=_cors_origins,
    allow_credentials=_cors_credentials,
    allow_methods=["*"],
    allow_headers=["*"],
)


@app.post("/validate", response_model=ConfigurationValidationResponse)
async def validate_schedule_configuration(payload: dict[str, Any]) -> ConfigurationValidationResponse:
    """
    Validate raw combined configuration JSON without converting errors to HTTP failures.

    Args:
        payload: Untrusted JSON object containing scheduler and time-slot sections.

    Returns:
        Structured validity, ordered diagnostics, and a fingerprint when valid.

    Raises:
        None for configuration errors; they are encoded in the returned diagnostics.

    Behavior:
        Validation uses the same schema and combined cross-reference rules as
        submission, but preserves all discovered configuration problems as response
        records. It does not create a scheduler, consume session capacity, or invoke
        Z3, making the endpoint suitable for pre-submission feedback.
    """
    result = validate_combined_config_data(payload)
    return ConfigurationValidationResponse(
        is_valid=result.is_valid,
        diagnostics=[_configuration_diagnostic_response(item) for item in result.diagnostics],
        configuration_fingerprint=result.configuration_fingerprint,
    )


@app.post("/submit", response_model=SubmitResponse)
async def submit_schedule(request: SubmitRequest):
    """
    Create an API generation session for a validated combined configuration.

    Args:
        request: Pydantic-validated combined scheduler configuration from the body.

    Returns:
        A new session identifier and its base schedule endpoint.

    Raises:
        HTTPException: Status 429 when active-session capacity is full; status 422
            for course, schedule, or candidate-slot limits; status 500 if work cannot
            be submitted; or status 400 for other request setup failures.

    Behavior:
        Expired sessions and all built-in request limits are checked before work is
        accepted. Scheduler construction is queued on the shared executor with the
        API solver timeout. A UUID-backed session is registered immediately with
        empty results so later requests can await initialization asynchronously.
    """
    try:
        _validate_submission_limits(request)
        # Create scheduler in thread pool to avoid blocking
        try:
            scheduler_future = z3_executor.submit(Scheduler, request, solver_timeout_ms=API_LIMITS.solver_timeout_ms)
        except Exception as e:
            logger.error(f"Failed to create scheduler: {e}")
            raise HTTPException(status_code=500, detail=f"Scheduler creation failed: {str(e)}") from e

        # Generate unique ID for this session
        schedule_id = str(uuid.uuid4())

        # Store session
        schedule_sessions[schedule_id] = ScheduleSession(
            scheduler=None,
            scheduler_future=scheduler_future,  # type: ignore
            generator=None,
            full_config=request,
            generated_schedules=[],
        )

        logger.debug(f"Created new schedule session {schedule_id}")

        return SubmitResponse(schedule_id=schedule_id, endpoint=f"/schedules/{schedule_id}")

    except HTTPException:
        # Re-raise HTTP exceptions
        raise
    except Exception as e:
        logger.error(f"Error creating schedule session: {e}")
        raise HTTPException(status_code=400, detail=f"Invalid configuration: {str(e)}") from e


@app.get("/schedules/{schedule_id}/details", response_model=ScheduleDetailsResponse)
async def get_schedule_details(schedule_id: str):
    """
    Return the submitted configuration and generation count for one session.

    Args:
        schedule_id: Unique identifier returned by schedule submission.

    Returns:
        The full combined configuration augmented with session id and current count.

    Raises:
        HTTPException: Status 404 when the session does not exist, or status 422 if
            its queued scheduler initialization fails.

    Behavior:
        Access refreshes the session's idle timestamp and awaits scheduler
        construction so failed initialization cannot masquerade as a usable session.
        The endpoint reports retained results but does not initialize or advance the
        model generator.
    """
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]
    session.last_accessed_at = time.monotonic()

    await ensure_scheduler_initialized(schedule_id, session)

    return ScheduleDetailsResponse(
        schedule_id=schedule_id,
        **session.full_config.model_dump(),
        total_generated=len(session.generated_schedules),
    )


@app.get("/schedules/{schedule_id}/diagnosis", response_model=ScheduleDiagnosisResponse)
async def get_schedule_diagnosis(schedule_id: str) -> ScheduleDiagnosisResponse:
    """
    Diagnose hard-constraint feasibility for a submitted session configuration.

    Args:
        schedule_id: Unique identifier of the session to diagnose.

    Returns:
        Full structured diagnosis including cores, domains, repairs, provenance,
        completeness metadata, timing, and solver status.

    Raises:
        HTTPException: Status 404 when no session exists or status 422 if scheduler
            initialization fails. Unhandled executor failures become server errors.

    Behavior:
        Scheduler initialization is awaited, then diagnosis runs on the shared Z3
        executor while holding the session generation lock so it cannot race model
        enumeration or auditing. Internal immutable contracts are copied into API
        response models, and successful access refreshes the session TTL.
    """
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]
    await ensure_scheduler_initialized(schedule_id, session)
    assert session.scheduler is not None
    async with session.generation_lock:
        diagnosis = cast(
            ScheduleDiagnosis,
            await asyncio.wrap_future(z3_executor.submit(session.scheduler.diagnose)),
        )
    session.last_accessed_at = time.monotonic()
    return ScheduleDiagnosisResponse(
        schedule_id=schedule_id,
        status=diagnosis.status,
        conflicting_constraints=[
            _constraint_diagnostic_response(constraint) for constraint in diagnosis.conflicting_constraints
        ],
        alternative_conflict_sets=[
            [_constraint_diagnostic_response(constraint) for constraint in conflict_set]
            for conflict_set in diagnosis.alternative_conflict_sets
        ],
        supporting_facts=[_constraint_diagnostic_response(fact) for fact in diagnosis.supporting_facts],
        relaxation_suggestions=[
            RelaxationSuggestionResponse(
                kind=suggestion.kind,
                subjects=list(suggestion.subjects),
                message=suggestion.message,
                priority=suggestion.priority,
            )
            for suggestion in diagnosis.relaxation_suggestions
        ],
        repair_sets=[_repair_set_response(repair_set) for repair_set in diagnosis.repair_sets],
        candidate_domains=[_candidate_domain_response(domain) for domain in diagnosis.candidate_domains],
        capacity_analysis=[_capacity_response(item) for item in diagnosis.capacity_analysis],
        day_feasibility=[_day_feasibility_response(item) for item in diagnosis.day_feasibility],
        preflight_findings=[_constraint_diagnostic_response(item) for item in diagnosis.preflight_findings],
        provenance=[_provenance_response(edge) for edge in diagnosis.provenance],
        configuration_fingerprint=diagnosis.configuration_fingerprint,
        core_is_minimal=diagnosis.core_is_minimal,
        alternative_cores_complete=diagnosis.alternative_cores_complete,
        repair_sets_complete=diagnosis.repair_sets_complete,
        diagnostic_completeness=diagnosis.diagnostic_completeness,
        diagnostic_version=diagnosis.diagnostic_version,
        elapsed_ms=diagnosis.elapsed_ms,
        solver_timeout_ms=diagnosis.solver_timeout_ms,
        reason=diagnosis.reason,
    )


@app.get("/schedules/{schedule_id}/audit/{index}", response_model=ScheduleAuditResponse)
async def get_schedule_audit(schedule_id: str, index: int) -> ScheduleAuditResponse:
    """
    Independently audit one previously generated schedule and explain its objectives.

    Args:
        schedule_id: Unique identifier of the containing generation session.
        index: Zero-based index in that session's retained schedules.

    Returns:
        Hard-rule validity, violations, workload and resource summaries, objective
        scores, and preference outcomes for the selected model.

    Raises:
        HTTPException: Status 404 for an unknown session or schedule index, or status
            422 if scheduler initialization fails. Executor failures propagate as
            server errors.

    Behavior:
        The original decoded model is audited rather than its serialized response.
        Audit execution is dispatched to the shared executor while holding the same
        generation lock used by enumeration and diagnosis. No solver state is
        advanced, and successful access refreshes the session TTL.
    """
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")
    session = schedule_sessions[schedule_id]
    await ensure_scheduler_initialized(schedule_id, session)
    if index < 0 or index >= len(session.generated_models):
        raise HTTPException(status_code=404, detail="Generated schedule not found")
    assert session.scheduler is not None
    async with session.generation_lock:
        audit = cast(
            ScheduleAudit,
            await asyncio.wrap_future(
                z3_executor.submit(session.scheduler.audit_schedule, session.generated_models[index])
            ),
        )
    session.last_accessed_at = time.monotonic()
    return _schedule_audit_response(schedule_id, index, audit)


@app.post("/schedules/{schedule_id}/next", response_model=ScheduleResponse)
async def get_next_schedule(schedule_id: str) -> ScheduleResponse:
    """
    Generate, retain, and return exactly one next schedule for a session.

    Args:
        schedule_id: Unique identifier of the generation session to advance.

    Returns:
        The newly generated schedule, its zero-based index, and total retained count.

    Raises:
        HTTPException: Status 404 for an unknown session, 409 while generate-all is
            active, 400 at requested-limit or solution-space exhaustion, 408/422 for
            initialization problems, or 500 for unexpected generation failures.

    Behavior:
        Background conflicts are checked both before and after lazy scheduler and
        generator initialization. The shared advance path holds the session lock,
        calls ``next`` on the Z3 executor, appends serialized and original forms
        atomically, blocks duplicate models through the generator, and refreshes TTL.
    """
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]

    if session.background_task is not None and not session.background_task.done():
        raise HTTPException(status_code=409, detail="Background schedule generation is in progress")

    await ensure_scheduler_initialized(schedule_id, session)
    await ensure_generator_initialized(schedule_id, session)

    if session.background_task is not None and not session.background_task.done():
        raise HTTPException(status_code=409, detail="Background schedule generation is in progress")

    try:
        response = await _advance_session(schedule_id, session)
        logger.debug(f"Generated schedule {response.index + 1} for session {schedule_id}")
        return response

    except HTTPException:
        # Re-raise HTTP exceptions
        raise
    except Exception as e:
        logger.error(f"Error generating next schedule for {schedule_id}: {e}")
        raise HTTPException(status_code=500, detail=f"Error generating schedule: {str(e)}") from e


@app.post("/schedules/{schedule_id}/generate_all", response_model=GenerateAllResponse)
async def generate_all_schedules(schedule_id: str):
    """
    Start one background task to generate all remaining schedules up to the limit.

    Args:
        schedule_id: Unique identifier of the generation session to exhaust.

    Returns:
        Confirmation containing the current retained count and target limit; the
        response does not wait for enumeration to finish.

    Raises:
        HTTPException: Status 404 for an unknown session, 409 when another background
            run is active, 400 when the requested limit is already reached, or the
            initialization errors documented by the scheduler/generator helpers.

    Behavior:
        Initialization completes before a single session-owned task is created.
        That task repeatedly uses the same locked advance path as ``/next``, stopping
        on the requested bound, solution-space exhaustion, cancellation, or error.
        Terminal reasons and unexpected error text are recorded for status queries;
        concurrent next or generate-all calls observe the active-task conflict.
    """
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]

    if session.background_task is not None and not session.background_task.done():
        raise HTTPException(status_code=409, detail="Background schedule generation is already in progress")

    await ensure_scheduler_initialized(schedule_id, session)
    await ensure_generator_initialized(schedule_id, session)

    if session.background_task is not None and not session.background_task.done():
        raise HTTPException(status_code=409, detail="Background schedule generation is already in progress")

    # Check if we've already generated all schedules
    if len(session.generated_schedules) >= session.full_config.limit:
        raise HTTPException(
            status_code=400,
            detail=f"All {session.full_config.limit} schedules have already been generated",
        )

    # Start background task to generate all remaining schedules
    async def generate_all_background():
        try:
            remaining = session.full_config.limit - len(session.generated_schedules)
            logger.info(f"Starting background generation of {remaining} schedules for session {schedule_id}")

            for _i in range(remaining):
                try:
                    current_task = asyncio.current_task()
                    # Check if we've been cancelled
                    if current_task is not None and current_task.cancelled():
                        logger.debug(f"Background generation cancelled for session {schedule_id}")
                        return

                    await _advance_session(schedule_id, session)
                    n = len(session.generated_schedules)
                    logger.debug(f"Generated schedule {n} for session {schedule_id}")

                except HTTPException as e:
                    if e.status_code != 400:
                        logger.error(f"Failed to generate schedules for session {schedule_id}: {e.detail}")
                        session.background_error = str(e.detail)
                    session.is_exhausted = True
                    session.completion_reason = session.completion_reason or "solution_space_exhausted"
                    logger.info(f"No more schedules available for session {schedule_id}")
                    break
                except asyncio.CancelledError:
                    logger.debug(f"Background generation cancelled for session {schedule_id}")
                    session.completion_reason = "background_generation_cancelled"
                    return
                except Exception as e:
                    count = len(session.generated_schedules) + 1
                    logger.error(f"Failed to generate schedule {count} for session {schedule_id}: {e}")
                    session.background_error = str(e)
                    session.completion_reason = "background_generation_failed"
                    break
            n = len(session.generated_schedules)
            logger.info(f"Completed background generation for session {schedule_id}. Total generated: {n}")

        except asyncio.CancelledError:
            logger.debug(f"Background generation cancelled for session {schedule_id}")
            session.completion_reason = "background_generation_cancelled"
        except Exception as e:
            logger.error(f"Background generation failed for session {schedule_id}: {e}")
            session.background_error = str(e)
            session.completion_reason = "background_generation_failed"

    # Start one background task for this session.
    session.background_task = asyncio.create_task(generate_all_background())

    return GenerateAllResponse(
        message=f"Started generating all remaining schedules for session {schedule_id}",
        current_count=len(session.generated_schedules),
        target_count=session.full_config.limit,
    )


@app.get("/schedules/{schedule_id}/count", response_model=ScheduleCountResponse)
async def get_schedule_count(schedule_id: str):
    """
    Report the retained schedule count and completion state for one session.

    Args:
        schedule_id: Unique identifier of the session to inspect.

    Returns:
        Current result count, requested limit, and whether enumeration is complete.

    Raises:
        HTTPException: Status 404 when the session does not exist.

    Behavior:
        This is a non-blocking snapshot: it neither awaits initialization nor
        acquires the generation lock. Completion is true after solver exhaustion or
        once the retained count reaches the requested limit. Access refreshes TTL.
    """
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]
    session.last_accessed_at = time.monotonic()

    return ScheduleCountResponse(
        schedule_id=schedule_id,
        current_count=len(session.generated_schedules),
        limit=session.full_config.limit,
        is_complete=session.is_exhausted or len(session.generated_schedules) >= session.full_config.limit,
    )


@app.get("/schedules/{schedule_id}/status", response_model=SessionDiagnosticResponse)
async def get_schedule_status(schedule_id: str) -> SessionDiagnosticResponse:
    """
    Report live generation state, API safeguards, and terminal reason for a session.

    Args:
        schedule_id: Unique identifier of the session to inspect.

    Returns:
        A non-blocking operational snapshot including initialization/background
        states, idle age, counts, completion metadata, and configured limits.

    Raises:
        HTTPException: Status 404 when the session does not exist.

    Behavior:
        State is derived from futures, tasks, exhaustion, and retained counts without
        invoking the solver or generator. The query refreshes the session access
        timestamp before the response is built, so reported idle time is near zero.
    """
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")
    session = schedule_sessions[schedule_id]
    session.last_accessed_at = time.monotonic()
    return _session_diagnostic_response(schedule_id, session)


@app.get("/schedules/{schedule_id}/index/{index}", response_model=ScheduleResponse)
async def get_schedule_by_index(schedule_id: str, index: int):
    """
    Return one previously retained schedule without advancing generation.

    Args:
        schedule_id: Unique identifier of the containing generation session.
        index: Zero-based index into schedules generated so far.

    Returns:
        The stored serialized schedule, requested index, and current total count.

    Raises:
        HTTPException: Status 404 when either the session or requested index does not
            exist; the detail identifies the currently available index interval.

    Behavior:
        Results are read directly from the append-only serialized schedule list. No
        scheduler initialization or generation lock is required, and retrieving a
        result refreshes the session's idle-expiry timestamp.
    """
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    session = schedule_sessions[schedule_id]
    session.last_accessed_at = time.monotonic()
    n = len(session.generated_schedules)
    if index < 0 or index >= n:
        raise HTTPException(
            status_code=404,
            detail=f"Schedule index {index} not found. Available indices: 0-{n - 1}",
        )

    return ScheduleResponse(
        schedule_id=schedule_id,
        schedule=session.generated_schedules[index],
        index=index,
        total_generated=len(session.generated_schedules),
    )


@app.delete("/schedules/{schedule_id}/delete", response_model=MessageResponse)
async def delete_schedule_session(schedule_id: str, background_tasks: BackgroundTasks):
    """
    Schedule deletion of an existing session after the HTTP response is sent.

    Args:
        schedule_id: Unique identifier of the session to delete.
        background_tasks: FastAPI response-scoped background task collector.

    Returns:
        A message confirming that session cleanup has been queued.

    Raises:
        HTTPException: Status 404 when the session does not exist.

    Behavior:
        Cleanup is registered with FastAPI rather than run before responding. The
        cleanup routine removes the session and requests cancellation of unfinished
        scheduler initialization or background generation. A later request may see
        the session until the response background task executes.
    """
    if schedule_id not in schedule_sessions:
        raise HTTPException(status_code=404, detail="Schedule session not found")

    # Schedule cleanup in background
    background_tasks.add_task(cleanup_session, schedule_id)

    return MessageResponse(message=f"Schedule session {schedule_id} marked for deletion")


@app.post("/schedules/{schedule_id}/cleanup", response_model=MessageResponse)
async def cleanup_schedule_session(schedule_id: str):
    """
    Immediately remove a session and request cancellation of its active work.

    Args:
        schedule_id: Unique identifier of the session to clean up.

    Returns:
        A cleanup confirmation message for the supplied identifier.

    Raises:
        None for missing sessions; cleanup is intentionally idempotent.

    Behavior:
        Existing sessions are synchronously removed through ``cleanup_session``;
        unknown identifiers still receive the same success-shaped response. Running
        thread-pool work may finish internally after its future is cancelled, but
        its session is no longer addressable.
    """
    if schedule_id in schedule_sessions:
        cleanup_session(schedule_id)

    return MessageResponse(message=f"Schedule session {schedule_id} cleaned up")


@app.get("/health", response_model=HealthCheck)
async def health_check():
    """
    Return a lightweight service health and active-session snapshot.

    Args:
        None.

    Returns:
        A healthy status string and the current number of registered sessions.

    Raises:
        None.

    Behavior:
        The endpoint reads only the in-memory registry and does not expire sessions,
        await solver work, or probe Z3. It therefore confirms process responsiveness
        rather than the satisfiability or completion of individual requests.
    """
    return HealthCheck(status="healthy", active_sessions=len(schedule_sessions))


@click.command()
@click.option("--port", "-p", default=8000, help="Port to run the server on", type=int)
@click.option(
    "--log-level",
    "-l",
    default="info",
    type=click.Choice(["debug", "info", "warning", "error", "critical"]),
    help="Log level for the server",
)
@click.option("--host", "-h", default="0.0.0.0", help="Host to bind the server to")
@click.option("--workers", "-w", default=16, help="Number of worker threads", type=int)
def main(port: int, log_level: str, host: str, workers: int):
    """
    Run the Course Scheduler FastAPI application through Uvicorn.

    Args:
        port: TCP port on which Uvicorn listens.
        log_level: Uvicorn logging severity selected by the CLI.
        host: Network interface address to bind.
        workers: Size of the shared thread pool used for Z3 operations.

    Returns:
        None after the Uvicorn server terminates.

    Raises:
        ImportError: If Uvicorn is unavailable in the runtime environment.
        OSError: If the requested network address cannot be bound.

    Behavior:
        Process logging is configured first. A non-default worker count replaces the
        module's initial Z3 executor before serving begins. Uvicorn then runs the
        single application process with reload disabled; ``workers`` controls solver
        threads, not Uvicorn multiprocess workers.
    """
    configure_logging()

    import uvicorn

    # Update thread pool size if different from default
    global z3_executor
    if workers != 16:
        z3_executor.shutdown(wait=True)
        z3_executor = ThreadPoolExecutor(max_workers=workers, thread_name_prefix="z3-solver")

    logger.info(f"Starting server on {host}:{port} with log level {log_level} and {workers} Z3 workers")

    uvicorn.run(app, host=host, port=port, log_level=log_level, reload=False)


if __name__ == "__main__":
    main()
