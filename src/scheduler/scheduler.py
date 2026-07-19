import itertools
import json
import os
import time
from collections import defaultdict
from collections.abc import Callable, Generator, Mapping
from dataclasses import dataclass
from functools import cache
from typing import Any, cast

import z3
from bidict import frozenbidict
from pydantic import BaseModel, ValidationError

from .config import (
    CombinedConfig,
    FacultyConfig,
    OptimizerFlags,
)
from .logging import logger
from .models import (
    Course,
    CourseInstance,
    Day,
    TimeInstance,
    TimePoint,
    TimeSlot,
)
from .time_slot_generator import TimeSlotGenerator

MAX_REJECTED_PATTERN_DIAGNOSTICS = 128
MAX_PAIR_PATTERN_COMPARISONS = 4_096


def load_config_from_file[T: BaseModel](
    config_cls: type[T],
    filename: str | os.PathLike[str],
) -> T:
    """
    Load scheduler configuration from a JSON file.

    **Usage:**
    ```python
    from scheduler import CombinedConfig, load_config_from_file
    cfg = load_config_from_file(CombinedConfig, "config.json")
    ```

    **Args:**
    - config_cls: The class of the configuration to load
    - filename: Path to the file (str or pathlib.Path)

    **Returns:**
    The loaded configuration

    **Example:**
    >>> load_config_from_file(CombinedConfig, "config.json")
    >>> load_config_from_file(CombinedConfig, Path("config.json"))
    """
    with open(filename, encoding="utf-8") as f:
        data = json.load(f)
    return config_cls(**data)


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


def _json_pointer(location: tuple[object, ...]) -> str:
    if not location:
        return ""
    return "/" + "/".join(str(part).replace("~", "~0").replace("/", "~1") for part in location)


def validate_combined_config_data(payload: Mapping[str, Any]) -> ConfigurationValidationResult:
    """Validate raw configuration data without raising a Pydantic exception.

    Use this at API boundaries when callers need actionable diagnostics rather
    than an exception payload.  A valid result retains only a stable input
    fingerprint; callers can construct :class:`CombinedConfig` separately.
    """
    try:
        config = CombinedConfig.model_validate(payload)
    except ValidationError as exc:
        diagnostics: list[ConfigurationDiagnostic] = []
        for error in exc.errors(include_url=False):
            invalid_value = error.get("input")
            value = repr(invalid_value) if isinstance(invalid_value, str | int | float | bool) else None
            diagnostics.append(
                ConfigurationDiagnostic(
                    code="SCHED.CONFIG." + str(error["type"]).upper().replace("_", "."),
                    path=_json_pointer(tuple(error["loc"])),
                    message=str(error["msg"]),
                    value=value,
                )
            )
        return ConfigurationValidationResult(is_valid=False, diagnostics=tuple(diagnostics))
    canonical = json.dumps(config.model_dump(mode="json"), sort_keys=True, separators=(",", ":"))
    import hashlib

    return ConfigurationValidationResult(
        is_valid=True,
        configuration_fingerprint=hashlib.sha256(canonical.encode()).hexdigest(),
    )


def get_faculty_availability(
    faculty_config: FacultyConfig,
) -> list[TimeInstance]:
    """
    Calculate the availability of a faculty as a list of `TimeInstance` objects.

    **Usage:**
    ```python
    slots = get_faculty_availability(faculty_config)
    ```

    **Args:**
    - faculty_config: The configuration of the faculty

    **Returns:**
    The availability of the faculty as a list of `TimeInstance` objects
    """
    days: list[Day] = [Day.MON, Day.TUE, Day.WED, Day.THU, Day.FRI]
    result: list[TimeInstance] = []
    for day in days:
        day_name = day.name
        times = faculty_config.times.get(day_name, [])
        for time_range in times:
            # Parse TimeRange object
            start_str = time_range.start
            end_str = time_range.end
            start_hour, start_minute = map(int, start_str.split(":"))
            end_hour, end_minute = map(int, end_str.split(":"))

            start_time: TimePoint = TimePoint.make_from(start_hour, start_minute)
            end_time: TimePoint = TimePoint.make_from(end_hour, end_minute)
            result.append(
                TimeInstance(
                    day=day,
                    start=start_time,
                    duration=end_time - start_time,
                )
            )
    return result


@dataclass
class _FunctionConstraints:
    """
    Structured data for function constraints and their references.

    **Usage:**
    ```python
    # Built by Scheduler._build_function_constraints
    ```
    """

    constraints: list[z3.BoolRef]
    overlaps: z3.FuncDeclRef
    lab_overlaps: z3.FuncDeclRef
    lecture_next_to: z3.FuncDeclRef
    faculty_available: z3.FuncDeclRef
    lab_next_to: z3.FuncDeclRef


@dataclass
class _Z3SortsAndConstants:
    """
    Structured data for Z3 sorts and their corresponding constant mappings.

    **Usage:**
    ```python
    # Built by Scheduler._create_z3_enumsorts
    ```
    """

    time_slot_sort: z3.SortRef
    time_slot_constants: frozenbidict[TimeSlot, z3.ExprRef]
    faculty_sort: z3.SortRef
    faculty_constants: frozenbidict[str, z3.ExprRef]
    room_sort: z3.SortRef
    room_constants: frozenbidict[str, z3.ExprRef]
    lab_sort: z3.SortRef
    lab_constants: frozenbidict[str | None, z3.ExprRef]


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
    provenance: tuple["ProvenanceEdge", ...] = ()
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


@dataclass(frozen=True)
class _DiagnosticConstraint:
    expression: z3.BoolRef
    message: str
    kind: str = "constraint"
    subjects: tuple[str, ...] = ()


class Scheduler:
    """
    Scheduler class for generating schedules.

    **Usage:**
    ```python
    sched = Scheduler(full_config)
    next(sched.get_models())
    ```
    """

    def _initialize_faculty_data(self, config) -> None:
        """
        Initialize faculty-related data structures and preferences.

        **Usage:**
        ```python
        self._initialize_faculty_data(config)
        ```
        """
        for index, faculty_data in enumerate(config.faculty):
            faculty_name = faculty_data.name
            self._faculty_config_paths[faculty_name] = f"/config/faculty/{index}"
            self._faculty.append(faculty_name)
            self._faculty_maximum_credits[faculty_name] = faculty_data.maximum_credits
            self._faculty_maximum_days[faculty_name] = faculty_data.maximum_days
            self._faculty_minimum_credits[faculty_name] = faculty_data.minimum_credits
            self._faculty_unique_course_limits[faculty_name] = faculty_data.unique_course_limit
            self._faculty_course_preferences[faculty_name] = faculty_data.course_preferences
            self._faculty_room_preferences[faculty_name] = faculty_data.room_preferences
            self._faculty_lab_preferences[faculty_name] = faculty_data.lab_preferences
            self._faculty_mandatory_days[faculty_name] = {
                day if isinstance(day, Day) else Day[day] for day in faculty_data.mandatory_days
            }
            self._faculty_availability[faculty_name] = get_faculty_availability(faculty_data)

    def _initialize_courses(self, config) -> tuple[list[Course], set[int]]:
        """
        Initialize courses and return them along with required credits.

        **Usage:**
        ```python
        courses, credits = self._initialize_courses(config)
        ```
        """
        courses: list[Course] = []
        required_credits = set()
        course_counts: dict[str, int] = defaultdict(int)

        for index, c in enumerate(config.courses):
            course_counts[c.course_id] += 1
            required_credits.add(c.credits)
            course_faculty = (
                list(c.faculty)
                if c.faculty is not None
                else [faculty.name for faculty in config.faculty if c.course_id in faculty.course_preferences]
            )
            course = Course(
                credits=c.credits,
                course_id=c.course_id,
                section=course_counts[c.course_id],
                labs=c.lab,
                rooms=c.room,
                conflicts=c.conflicts,
                faculties=course_faculty,
            )
            courses.append(course)
            self._course_config_paths[str(course)] = f"/config/courses/{index}"
            self._course_faculty_origins[str(course)] = (
                "derived_from_preferences" if c.faculty is None else "configured"
            )

        return courses, required_credits

    def _initialize_time_slots(self, time_slot_config, required_credits: set[int]) -> None:
        """
        Initialize time slots and create ranges for different credit levels.

        **Usage:**
        ```python
        self._initialize_time_slots(time_slot_config, required_credits)
        ```
        """
        self._time_slot_generator = TimeSlotGenerator(time_slot_config)
        self._ranges: dict[int, tuple[int, int]] = {}
        self._slots: list[TimeSlot] = []

        for creds in sorted(required_credits):
            low = len(self._slots)
            self._slots.extend(self._time_slot_generator.time_slots(creds))
            self._ranges[creds] = (low, len(self._slots) - 1)

    def _create_z3_enumsorts(self) -> _Z3SortsAndConstants:
        """
        Create Z3 EnumSorts for time slots, faculty, rooms, and labs.

        **Usage:**
        ```python
        z3_data = self._create_z3_enumsorts()
        ```
        """

        # Create TimeSlot EnumSort
        time_slot_names = [f"time_slot_{i}" for i in range(len(self._slots))]
        time_slot_sort, time_slot_constants = z3.EnumSort("TimeSlot", time_slot_names, ctx=self._ctx)
        time_slot_constants_dict = frozenbidict(
            {time_slot: time_slot_constants[i] for i, time_slot in enumerate(self._slots)}
        )

        # Create Faculty EnumSort
        faculty_names = [f"faculty_{i}" for i in range(len(self._faculty))]
        faculty_sort, faculty_constants = z3.EnumSort("Faculty", faculty_names, ctx=self._ctx)
        faculty_constants_dict = frozenbidict(
            {faculty: faculty_constants[i] for i, faculty in enumerate(self._faculty)},
        )

        # Create Room EnumSort
        room_names = [f"room_{i}" for i in range(len(self._rooms))]
        room_sort, room_constants = z3.EnumSort("Room", room_names, ctx=self._ctx)
        room_constants_dict = frozenbidict(
            {room: room_constants[i] for i, room in enumerate(self._rooms)},
        )

        # Always include an internal no-lab value so configurations without
        # labs do not create an invalid empty EnumSort.
        lab_values: list[str | None] = [None, *self._labs]
        lab_names = ["lab_none", *[f"lab_{i}" for i in range(len(self._labs))]]
        lab_sort, lab_constants = z3.EnumSort("Lab", lab_names, ctx=self._ctx)
        lab_constants_dict = frozenbidict(
            {lab: lab_constants[i] for i, lab in enumerate(lab_values)},
        )

        return _Z3SortsAndConstants(
            time_slot_sort=time_slot_sort,
            time_slot_constants=time_slot_constants_dict,
            faculty_sort=faculty_sort,
            faculty_constants=faculty_constants_dict,
            room_sort=room_sort,
            room_constants=room_constants_dict,
            lab_sort=lab_sort,
            lab_constants=lab_constants_dict,
        )

    def _create_course_variables(self, z3_data: _Z3SortsAndConstants) -> None:
        """
        Create Z3 variables for each course.

        **Usage:**
        ```python
        self._create_course_variables(z3_data)
        ```
        """
        for course in self._courses:
            course.time = z3.Const(f"{str(course)}_time", z3_data.time_slot_sort)
            course.faculty = z3.Const(f"{str(course)}_faculty", z3_data.faculty_sort)
            course.room = z3.Const(f"{str(course)}_room", z3_data.room_sort)
            course.lab = z3.Const(f"{str(course)}_lab", z3_data.lab_sort)

    def __init__(self, full_config: CombinedConfig, *, solver_timeout_ms: int | None = None):
        """
        Initializes the scheduler with all the necessary constraints and variables.

        **Usage:**
        ```python
        Scheduler(full_config)
        ```

        **Args:**
        - full_config: `CombinedConfig` object containing all the configuration
                       settings including the scheduler config, time slot config,
                       limit, and optimizer flags
        - solver_timeout_ms: Optional per-check Z3 timeout in milliseconds.
          The REST API supplies this as a deployment safeguard; library callers
          remain uncapped by default.

        **Raises:**
        - ValueError: If the optimizer flags are invalid
        """
        # Extract configuration
        config = full_config.config
        time_slot_config = full_config.time_slot_config
        self._optimizer_flags = full_config.optimizer_flags
        self._limit = full_config.limit
        self._solver_timeout_ms = solver_timeout_ms
        self._full_config = full_config

        # Initialize Z3 context
        self._ctx = z3.Context()

        # Initialize data structures
        self._faculty: list[str] = []
        self._faculty_config_paths: dict[str, str] = {}
        self._course_config_paths: dict[str, str] = {}
        self._course_faculty_origins: dict[str, str] = {}
        self._faculty_maximum_credits: dict[str, int] = {}
        self._faculty_maximum_days: dict[str, int] = {}
        self._faculty_minimum_credits: dict[str, int] = {}
        self._faculty_unique_course_limits: dict[str, int] = {}
        self._faculty_course_preferences: dict[str, dict[str, int]] = {}
        self._faculty_room_preferences: dict[str, dict[str, int]] = {}
        self._faculty_lab_preferences: dict[str, dict[str, int]] = {}
        self._faculty_mandatory_days: dict[str, set[Day]] = {}
        self._faculty_availability: dict[str, list[TimeInstance]] = {}
        self._initialize_faculty_data(config)

        # Initialize courses and time slots
        self._rooms = list(config.rooms)
        self._labs = list(config.labs)
        self._courses, required_credits = self._initialize_courses(config)
        self._initialize_time_slots(time_slot_config, required_credits)
        self._compatible_slots_by_course: dict[str, tuple[TimeSlot, ...]] = {}

        # Create Z3 structures
        z3_data = self._create_z3_enumsorts()
        self._create_course_variables(z3_data)

        # Build function constraints and get the function references
        function_data = self._build_function_constraints(z3_data)

        self._diagnostic_constraints: list[_DiagnosticConstraint] = []

        # Build faculty constraints
        faculty_constraints = self._build_faculty_constraints(z3_data)

        # Build course constraints
        course_constraints = self._build_course_constraints(
            function_data.overlaps,
            function_data.faculty_available,
            z3_data,
        )

        # Build resource constraints
        resource_constraints = self._build_resource_constraints(
            function_data.overlaps,
            function_data.lab_overlaps,
            function_data.lecture_next_to,
            function_data.lab_next_to,
            z3_data,
        )

        # Aggregate all constraints
        self._constraints = self._aggregate_constraints(
            function_data.constraints, faculty_constraints, course_constraints, resource_constraints
        )

        self._function_data = function_data
        self._z3_data = z3_data

    def diagnose(self) -> ScheduleDiagnosis:
        """Explain hard-constraint feasibility without running soft optimization objectives."""
        started_at = time.perf_counter()
        status, conflicts, core_indexes, reason = self._diagnostic_core()
        if status == "unsatisfiable":
            conflicts, core_indexes = self._minimize_core(core_indexes)
        elapsed_ms = round((time.perf_counter() - started_at) * 1000)
        candidate_domains = self._candidate_domains()
        capacity_analysis = self._capacity_analysis()
        day_feasibility = self._day_feasibility()
        preflight_findings = self._preflight_findings(candidate_domains, capacity_analysis)
        if status == "unsatisfiable":
            alternatives, alternatives_complete = self._alternative_cores(core_indexes)
            repair_sets, repair_sets_complete = self._repair_sets()
            supporting_facts = self._supporting_facts(conflicts)
            return ScheduleDiagnosis(
                status=status,
                conflicting_constraints=conflicts,
                alternative_conflict_sets=alternatives,
                supporting_facts=supporting_facts,
                relaxation_suggestions=self._relaxation_suggestions(conflicts, supporting_facts),
                repair_sets=repair_sets,
                candidate_domains=candidate_domains,
                capacity_analysis=capacity_analysis,
                day_feasibility=day_feasibility,
                preflight_findings=preflight_findings,
                provenance=self._provenance(candidate_domains, conflicts),
                configuration_fingerprint=self._configuration_fingerprint(),
                core_is_minimal=True,
                alternative_cores_complete=alternatives_complete,
                repair_sets_complete=repair_sets_complete,
                diagnostic_completeness="bounded_unsat_cores",
                elapsed_ms=elapsed_ms,
                solver_timeout_ms=self._solver_timeout_ms,
            )
        return ScheduleDiagnosis(
            status=status,
            candidate_domains=candidate_domains,
            capacity_analysis=capacity_analysis,
            day_feasibility=day_feasibility,
            preflight_findings=preflight_findings,
            provenance=self._provenance(candidate_domains, ()),
            configuration_fingerprint=self._configuration_fingerprint(),
            diagnostic_completeness="preflight_only" if status == "unknown" else "hard_constraint_feasibility",
            elapsed_ms=elapsed_ms,
            solver_timeout_ms=self._solver_timeout_ms,
            reason=reason,
        )

    def _configuration_fingerprint(self) -> str:
        """Return a stable, non-secret identity for the diagnostic input."""
        payload = json.dumps(self._full_config.model_dump(mode="json"), sort_keys=True, separators=(",", ":"))
        # Keeping this dependency-free makes the identifier usable in library and API callers.
        import hashlib

        return hashlib.sha256(payload.encode()).hexdigest()

    @staticmethod
    def _diagnostic_code(kind: str) -> str:
        return "SCHED." + kind.upper().replace("_", ".")

    def _diagnostic_locations(self, kind: str, subjects: tuple[str, ...]) -> tuple[str, ...]:
        """Map a business rule to the relevant JSON Pointer configuration paths."""
        locations: list[str] = []
        field_by_kind = {
            "course_time_pattern": "credits",
            "course_lab_eligibility": "lab",
            "course_room_eligibility": "room",
            "course_faculty_eligibility": "faculty",
            "course_conflict": "conflicts",
            "faculty_availability": "times",
            "faculty_credit_range": None,
            "faculty_unique_course_limit": "unique_course_limit",
            "faculty_maximum_days": "maximum_days",
            "faculty_mandatory_day": "mandatory_days",
        }
        for subject in subjects:
            course_path = self._course_config_paths.get(subject)
            if course_path is not None:
                locations.append(f"{course_path}/{field_by_kind.get(kind, '')}".rstrip("/"))
            faculty_path = self._faculty_config_paths.get(subject)
            if faculty_path is not None:
                field = field_by_kind.get(kind)
                locations.append(f"{faculty_path}/{field}" if field else faculty_path)
        if kind in {"course_time_pattern", "course_lab_eligibility", "faculty_availability"}:
            locations.append("/time_slot_config/classes")
        if kind in {"shared_room_overlap", "same_course_room"}:
            locations.append("/config/rooms")
        if kind in {"shared_lab_overlap", "same_course_lab"}:
            locations.append("/config/labs")
        return tuple(dict.fromkeys(locations))

    def _make_diagnostic(self, kind: str, subjects: tuple[str, ...], message: str) -> ConstraintDiagnostic:
        return ConstraintDiagnostic(
            kind=kind,
            subjects=subjects,
            message=message,
            code=self._diagnostic_code(kind),
            locations=self._diagnostic_locations(kind, subjects),
        )

    def _compatible_slots(self, course: Course) -> tuple[TimeSlot, ...]:
        cached_slots = self._compatible_slots_by_course.get(str(course))
        if cached_slots is not None:
            return cached_slots
        start, stop = self._ranges[course.credits]
        compatible_slots = tuple(
            slot
            for index, slot in enumerate(self._slots)
            if start <= index <= stop and slot.has_lab() == bool(course.labs)
        )
        self._compatible_slots_by_course[str(course)] = compatible_slots
        return compatible_slots

    @staticmethod
    def _any_pattern_pair(
        first_slots: tuple[TimeSlot, ...],
        second_slots: tuple[TimeSlot, ...],
        predicate: Callable[[TimeSlot, TimeSlot], bool],
    ) -> bool | None:
        """Return a witness for a pair relation, or ``None`` if the safe scan cap is reached."""
        for comparisons, (first, second) in enumerate(itertools.product(first_slots, second_slots), start=1):
            if predicate(first, second):
                return True
            if comparisons >= MAX_PAIR_PATTERN_COMPARISONS:
                return None
        return False

    def _candidate_domains(self) -> tuple[CandidateDomainDiagnostic, ...]:
        """Expose static candidate domains and availability eliminations for every course."""
        domains: list[CandidateDomainDiagnostic] = []
        for course in self._courses:
            compatible_slots = self._compatible_slots(course)
            availability: list[ConstraintDiagnostic] = []
            for faculty in course.faculties:
                available_count = sum(
                    slot.in_time_ranges(self._faculty_availability[faculty]) for slot in compatible_slots
                )
                availability.append(
                    self._make_diagnostic(
                        "faculty_candidate_availability",
                        (str(course), faculty),
                        f"Faculty {faculty} can teach course {course} in {available_count} of "
                        f"{len(compatible_slots)} compatible meeting patterns",
                    )
                )

            rejected_patterns: list[ConstraintDiagnostic] = []
            rejected_pattern_count = 0
            credit_slots = set(self._slots[self._ranges[course.credits][0] : self._ranges[course.credits][1] + 1])
            for slot in self._slots:
                if slot in compatible_slots:
                    continue
                rejected_pattern_count += 1
                if len(rejected_patterns) >= MAX_REJECTED_PATTERN_DIAGNOSTICS:
                    continue
                reason = "credit count" if slot not in credit_slots else "lab requirement"
                rejected_patterns.append(
                    self._make_diagnostic(
                        "rejected_time_pattern",
                        (str(course),),
                        f"Course {course} rejects pattern {slot} because its {reason} does not match",
                    )
                )
            domains.append(
                CandidateDomainDiagnostic(
                    course=str(course),
                    locations=(self._course_config_paths[str(course)],),
                    faculty_candidates=tuple(course.faculties),
                    faculty_origin=self._course_faculty_origins[str(course)],
                    room_candidates=tuple(course.rooms),
                    lab_candidates=tuple(course.labs),
                    compatible_time_patterns=tuple(map(str, compatible_slots)),
                    availability_by_faculty=tuple(availability),
                    rejected_patterns=tuple(rejected_patterns),
                    rejected_pattern_count=rejected_pattern_count,
                    rejected_patterns_truncated=rejected_pattern_count > len(rejected_patterns),
                )
            )
        return tuple(domains)

    def _capacity_analysis(self) -> tuple[CapacityDiagnostic, ...]:
        """Evaluate cheap necessary conditions and forced-resource bottlenecks."""
        diagnostics: list[CapacityDiagnostic] = []
        total_credits = sum(course.credits for course in self._courses)
        diagnostics.append(
            CapacityDiagnostic(
                kind="global_faculty_maximum_credits",
                subjects=(),
                message="Total course credits compared with total faculty maximum credit capacity",
                required=total_credits,
                available=sum(self._faculty_maximum_credits.values()),
                locations=("/config/courses", "/config/faculty"),
            )
        )
        diagnostics.append(
            CapacityDiagnostic(
                kind="global_faculty_minimum_credits",
                subjects=(),
                message="Total faculty minimum credit commitment compared with total course credits",
                required=sum(self._faculty_minimum_credits.values()),
                available=total_credits,
                locations=("/config/courses", "/config/faculty"),
            )
        )
        for faculty in self._faculty:
            eligible = [course for course in self._courses if faculty in course.faculties]
            forced = [course for course in eligible if course.faculties == [faculty]]
            diagnostics.extend(
                (
                    CapacityDiagnostic(
                        kind="faculty_minimum_credit_coverage",
                        subjects=(faculty,),
                        message=f"Courses eligible for {faculty} can contribute at most the shown credits",
                        required=self._faculty_minimum_credits[faculty],
                        available=sum(course.credits for course in eligible),
                        locations=(self._faculty_config_paths[faculty] + "/minimum_credits",),
                    ),
                    CapacityDiagnostic(
                        kind="faculty_forced_credit_load",
                        subjects=(faculty,),
                        message=f"Courses with only {faculty} as a candidate require the shown credits",
                        required=sum(course.credits for course in forced),
                        available=self._faculty_maximum_credits[faculty],
                        locations=(self._faculty_config_paths[faculty] + "/maximum_credits",),
                    ),
                )
            )
            forced_course_ids = {course.course_id for course in forced}
            diagnostics.append(
                CapacityDiagnostic(
                    kind="faculty_forced_unique_courses",
                    subjects=(faculty,),
                    message=f"Distinct courses forced onto {faculty} compared with their unique-course limit",
                    required=len(forced_course_ids),
                    available=self._faculty_unique_course_limits[faculty],
                    locations=(self._faculty_config_paths[faculty] + "/unique_course_limit",),
                )
            )
            for mandatory_day in self._faculty_mandatory_days[faculty]:
                available_patterns = sum(
                    1
                    for course in eligible
                    for slot in self._compatible_slots(course)
                    if mandatory_day in {time.day for time in slot.times}
                    and slot.in_time_ranges(self._faculty_availability[faculty])
                )
                diagnostics.append(
                    CapacityDiagnostic(
                        kind="faculty_mandatory_day_pattern_coverage",
                        subjects=(faculty, mandatory_day.name),
                        message=f"Available eligible patterns placing {faculty} on mandatory day {mandatory_day.name}",
                        required=1,
                        available=available_patterns,
                        locations=(
                            self._faculty_config_paths[faculty] + "/mandatory_days",
                            self._faculty_config_paths[faculty] + "/times",
                            "/time_slot_config/classes",
                        ),
                    )
                )

        for first, second in itertools.combinations(self._courses, 2):
            first_slots = self._compatible_slots(first)
            second_slots = self._compatible_slots(second)
            pair_subjects = (str(first), str(second))
            requirements: list[tuple[str, bool | None, tuple[str, ...], str]] = []
            if second.course_id in first.conflicts or first.course_id in second.conflicts:
                requirements.append(
                    (
                        "course_conflict_separation",
                        self._any_pattern_pair(first_slots, second_slots, lambda left, right: not left.overlaps(right)),
                        (
                            self._course_config_paths[str(first)] + "/conflicts",
                            self._course_config_paths[str(second)] + "/conflicts",
                        ),
                        "non-overlapping pattern pairs for courses declared as conflicts",
                    )
                )
            if first.faculties == second.faculties and len(first.faculties) == 1:
                requirements.append(
                    (
                        "forced_shared_faculty_separation",
                        self._any_pattern_pair(first_slots, second_slots, lambda left, right: not left.overlaps(right)),
                        (
                            self._course_config_paths[str(first)] + "/faculty",
                            self._course_config_paths[str(second)] + "/faculty",
                        ),
                        f"non-overlapping pattern pairs for courses forced to faculty {first.faculties[0]}",
                    )
                )
            if first.rooms == second.rooms and len(first.rooms) == 1:
                requirements.append(
                    (
                        "forced_shared_room_separation",
                        self._any_pattern_pair(first_slots, second_slots, lambda left, right: not left.overlaps(right)),
                        (
                            self._course_config_paths[str(first)] + "/room",
                            self._course_config_paths[str(second)] + "/room",
                        ),
                        f"non-overlapping pattern pairs for courses forced to room {first.rooms[0]}",
                    )
                )
            if first.labs == second.labs and len(first.labs) == 1:
                requirements.append(
                    (
                        "forced_shared_lab_separation",
                        self._any_pattern_pair(
                            first_slots, second_slots, lambda left, right: not left.lab_overlaps(right)
                        ),
                        (
                            self._course_config_paths[str(first)] + "/lab",
                            self._course_config_paths[str(second)] + "/lab",
                        ),
                        f"non-overlapping lab pattern pairs for courses forced to lab {first.labs[0]}",
                    )
                )
            if (
                first.course_id == second.course_id
                and first.faculties == second.faculties
                and len(first.faculties) == 1
            ):
                requirements.append(
                    (
                        "forced_section_adjacency",
                        self._any_pattern_pair(
                            first_slots, second_slots, lambda left, right: left.lecture_next_to(right)
                        ),
                        (
                            self._course_config_paths[str(first)],
                            self._course_config_paths[str(second)],
                        ),
                        "adjacent pattern pairs for same-course sections forced to one faculty",
                    )
                )
            for kind, feasible, locations, message in requirements:
                if feasible is None:
                    continue
                diagnostics.append(
                    CapacityDiagnostic(
                        kind=kind,
                        subjects=pair_subjects,
                        message=message,
                        required=1,
                        available=int(feasible),
                        locations=locations,
                    )
                )

        for resource_kind, attribute in (("room", "rooms"), ("lab", "labs")):
            bottleneck_groups: defaultdict[tuple[str, str], list[Course]] = defaultdict(list)
            for course in self._courses:
                candidates = getattr(course, attribute)
                compatible_slots = self._compatible_slots(course)
                if len(candidates) == 1 and len(compatible_slots) == 1:
                    bottleneck_groups[(candidates[0], str(compatible_slots[0]))].append(course)
            for (resource, pattern), courses in bottleneck_groups.items():
                if len(courses) < 2:
                    continue
                diagnostics.append(
                    CapacityDiagnostic(
                        kind=f"forced_{resource_kind}_time_bottleneck",
                        subjects=(resource, *(str(course) for course in courses)),
                        message=(
                            f"{len(courses)} courses are forced to {resource_kind} {resource} during "
                            f"the same pattern {pattern}"
                        ),
                        required=len(courses),
                        available=1,
                        locations=tuple(
                            self._course_config_paths[str(course)] + f"/{resource_kind}" for course in courses
                        ),
                    )
                )

        singleton_pattern_groups: defaultdict[str, list[Course]] = defaultdict(list)
        for course in self._courses:
            compatible_slots = self._compatible_slots(course)
            if len(compatible_slots) == 1:
                singleton_pattern_groups[str(compatible_slots[0])].append(course)
        for pattern, courses in singleton_pattern_groups.items():
            if len(courses) < 2:
                continue
            if not all(
                second.course_id in first.conflicts or first.course_id in second.conflicts
                for first, second in itertools.combinations(courses, 2)
            ):
                continue
            diagnostics.append(
                CapacityDiagnostic(
                    kind="singleton_pattern_conflict_clique",
                    subjects=tuple(str(course) for course in courses),
                    message=(
                        f"Courses {', '.join(map(str, courses))} form a conflict clique but all have only "
                        f"the same meeting pattern {pattern}"
                    ),
                    required=len(courses),
                    available=1,
                    locations=tuple(self._course_config_paths[str(course)] + "/conflicts" for course in courses),
                )
            )
        return tuple(diagnostics)

    def _day_feasibility(self) -> tuple[DayFeasibilityDiagnostic, ...]:
        """Return every faculty/day cell with availability and eligible-pattern counts."""
        diagnostics: list[DayFeasibilityDiagnostic] = []
        for faculty in self._faculty:
            faculty_path = self._faculty_config_paths[faculty]
            eligible = [course for course in self._courses if faculty in course.faculties]
            for day in Day:
                course_patterns = [
                    slot
                    for course in eligible
                    for slot in self._compatible_slots(course)
                    if day in {time.day for time in slot.times}
                ]
                available_patterns = sum(
                    slot.in_time_ranges(self._faculty_availability[faculty]) for slot in course_patterns
                )
                diagnostics.append(
                    DayFeasibilityDiagnostic(
                        faculty=faculty,
                        day=day.name,
                        availability_windows=tuple(
                            str(instance) for instance in self._faculty_availability[faculty] if instance.day == day
                        ),
                        eligible_courses=tuple(str(course) for course in eligible),
                        compatible_pattern_count=len(course_patterns),
                        available_pattern_count=available_patterns,
                        is_mandatory=day in self._faculty_mandatory_days[faculty],
                        locations=(
                            faculty_path + "/times",
                            faculty_path + "/mandatory_days",
                            "/time_slot_config/classes",
                        ),
                    )
                )
        return tuple(diagnostics)

    def _preflight_findings(
        self,
        domains: tuple[CandidateDomainDiagnostic, ...],
        capacities: tuple[CapacityDiagnostic, ...],
    ) -> tuple[ConstraintDiagnostic, ...]:
        """Surface deterministic impossibilities before an unsat core is inspected."""
        findings: list[ConstraintDiagnostic] = []
        for domain in domains:
            if domain.faculty_origin == "derived_from_preferences":
                findings.append(
                    self._make_diagnostic(
                        "derived_faculty_candidates",
                        (domain.course, *domain.faculty_candidates),
                        f"Course {domain.course} derives faculty candidates from course preferences: "
                        f"{', '.join(domain.faculty_candidates)}",
                    )
                )
            if not domain.compatible_time_patterns:
                findings.append(
                    self._make_diagnostic(
                        "empty_time_pattern_domain",
                        (domain.course,),
                        f"Course {domain.course} has no meeting pattern matching its credits and lab requirement",
                    )
                )
            for availability in domain.availability_by_faculty:
                if availability.message.split(" in ", 1)[1].startswith("0 of"):
                    findings.append(
                        self._make_diagnostic(
                            "faculty_candidate_unavailable",
                            availability.subjects,
                            f"{availability.subjects[1]} has no available compatible meeting pattern "
                            f"for {availability.subjects[0]}",
                        )
                    )
        for capacity in capacities:
            if capacity.required > capacity.available:
                findings.append(
                    self._make_diagnostic(
                        "capacity_shortfall",
                        capacity.subjects,
                        f"{capacity.message}: required {capacity.required}, available {capacity.available}",
                    )
                )
        return tuple(findings)

    def _provenance(
        self,
        domains: tuple[CandidateDomainDiagnostic, ...],
        conflicts: tuple[ConstraintDiagnostic, ...],
    ) -> tuple[ProvenanceEdge, ...]:
        """Build a compact graph from configuration fields to derived facts and cores."""
        edges: list[ProvenanceEdge] = []
        for domain in domains:
            course_path = self._course_config_paths[domain.course]
            edges.append(
                ProvenanceEdge(
                    source=course_path,
                    target=f"candidate-domain:{domain.course}",
                    relationship="defines_course_candidates",
                    subjects=(domain.course,),
                )
            )
            edges.append(
                ProvenanceEdge(
                    source="/time_slot_config/classes",
                    target=f"candidate-domain:{domain.course}",
                    relationship="generates_compatible_patterns",
                    subjects=(domain.course,),
                )
            )
            for faculty in domain.faculty_candidates:
                source = (
                    self._faculty_config_paths[faculty] + "/course_preferences"
                    if domain.faculty_origin == "derived_from_preferences"
                    else course_path + "/faculty"
                )
                edges.append(
                    ProvenanceEdge(
                        source=source,
                        target=f"candidate:{domain.course}:faculty:{faculty}",
                        relationship=domain.faculty_origin,
                        subjects=(domain.course, faculty),
                    )
                )
        for conflict in conflicts:
            target = f"core:{conflict.code or self._diagnostic_code(conflict.kind)}"
            for location in conflict.locations:
                edges.append(
                    ProvenanceEdge(
                        source=location,
                        target=target,
                        relationship="contributes_to_unsat_core",
                        subjects=conflict.subjects,
                    )
                )
        return tuple(edges)

    def _diagnostic_core(
        self,
        excluded_indexes: frozenset[int] = frozenset(),
        active_indexes: frozenset[int] | None = None,
    ) -> tuple[str, tuple[ConstraintDiagnostic, ...], frozenset[int], str | None]:
        """Return one labeled unsat core, optionally relaxing selected tracked rules."""
        solver = z3.Solver(ctx=self._ctx)
        if self._solver_timeout_ms is not None:
            solver.set(timeout=self._solver_timeout_ms)

        # Generated function tables are required for correctness, but they are
        # implementation details rather than useful user-facing explanations.
        solver.add(self._function_data.constraints)
        tracked_constraints: dict[str, tuple[int, _DiagnosticConstraint]] = {}
        for index, constraint in enumerate(self._diagnostic_constraints):
            if index in excluded_indexes or (active_indexes is not None and index not in active_indexes):
                continue
            tracker_name = f"diagnostic_constraint_{index}"
            tracker = z3.Bool(tracker_name, ctx=self._ctx)
            solver.assert_and_track(constraint.expression, tracker)
            tracked_constraints[tracker_name] = (index, constraint)

        result = solver.check()
        if result == z3.unsat:
            core_tracker_names = [str(tracker) for tracker in solver.unsat_core()]
            conflicts = tuple(
                self._make_diagnostic(
                    tracked_constraints[name][1].kind,
                    tracked_constraints[name][1].subjects,
                    tracked_constraints[name][1].message,
                )
                for name in core_tracker_names
                if name in tracked_constraints
            )
            core_indexes = frozenset(
                tracked_constraints[name][0] for name in core_tracker_names if name in tracked_constraints
            )
            return "unsatisfiable", conflicts, core_indexes, None
        if result == z3.sat:
            return "satisfiable", (), frozenset(), None
        return "unknown", (), frozenset(), solver.reason_unknown()

    def _minimize_core(self, core_indexes: frozenset[int]) -> tuple[tuple[ConstraintDiagnostic, ...], frozenset[int]]:
        """Shrink a solver-provided core to a subset-minimal business-rule core."""
        active = set(core_indexes)
        for index in tuple(sorted(active)):
            candidate = frozenset(active - {index})
            status, _core, _indexes, _reason = self._diagnostic_core(active_indexes=candidate)
            if status == "unsatisfiable":
                active.remove(index)
        minimized = frozenset(active)
        constraints = tuple(
            self._make_diagnostic(
                self._diagnostic_constraints[index].kind,
                self._diagnostic_constraints[index].subjects,
                self._diagnostic_constraints[index].message,
            )
            for index in sorted(minimized)
        )
        return constraints, minimized

    def _alternative_cores(
        self, primary_core_indexes: frozenset[int], max_alternatives: int = 16, max_solver_checks: int = 128
    ) -> tuple[tuple[tuple[ConstraintDiagnostic, ...], ...], bool]:
        """Enumerate distinct subset-minimal alternative cores with explicit bounds.

        Each discovered core is blocked one rule at a time.  This explores all
        alternatives reachable within the stated solver-check and result caps;
        the boolean reports whether those bounds were sufficient to exhaust
        the search rather than implying an unbounded enumeration completed.
        """
        alternatives: list[tuple[ConstraintDiagnostic, ...]] = []
        seen = {primary_core_indexes}
        pending = [frozenset({index}) for index in primary_core_indexes]
        visited: set[frozenset[int]] = set()
        checks = 0
        complete = True

        while pending and len(alternatives) < max_alternatives and checks < max_solver_checks:
            excluded = pending.pop(0)
            if excluded in visited:
                continue
            visited.add(excluded)
            status, _core, core_indexes, _reason = self._diagnostic_core(excluded)
            checks += 1
            if status == "unknown":
                complete = False
                continue
            if status != "unsatisfiable":
                continue
            minimized_core, minimized_indexes = self._minimize_core(core_indexes)
            if minimized_indexes in seen:
                continue
            seen.add(minimized_indexes)
            alternatives.append(minimized_core)
            for index in minimized_indexes:
                child = excluded | frozenset({index})
                if child not in visited:
                    pending.append(child)

        if pending or checks >= max_solver_checks:
            complete = False
        return tuple(alternatives), complete

    def _repair_sets(
        self, max_repair_sets: int = 5, max_solver_checks: int = 64
    ) -> tuple[tuple[RepairSetDiagnostic, ...], bool]:
        """Find bounded minimum-cardinality correction sets using core-guided search.

        These are deliberately expressed as *rule* relaxations.  A caller can
        map them to configuration edits, while the solver check establishes
        that relaxing every listed rule is sufficient and that no smaller set
        was found before it.
        """
        pending: list[frozenset[int]] = [frozenset()]
        visited: set[frozenset[int]] = set()
        repairs: list[RepairSetDiagnostic] = []
        solver_checks = 0
        completed = True

        while pending and len(repairs) < max_repair_sets and solver_checks < max_solver_checks:
            pending.sort(key=lambda excluded: (len(excluded), tuple(sorted(excluded))))
            excluded = pending.pop(0)
            if excluded in visited:
                continue
            visited.add(excluded)
            status, core, core_indexes, _reason = self._diagnostic_core(excluded)
            solver_checks += 1
            if status == "satisfiable":
                relaxed = tuple(
                    self._make_diagnostic(
                        self._diagnostic_constraints[index].kind,
                        self._diagnostic_constraints[index].subjects,
                        self._diagnostic_constraints[index].message,
                    )
                    for index in sorted(excluded)
                )
                repairs.append(
                    RepairSetDiagnostic(
                        relaxed_constraints=relaxed,
                        verified=True,
                        message=(
                            "Relaxing these business rules makes the hard constraint system satisfiable; "
                            "translate them into configuration edits before applying a change"
                        ),
                    )
                )
                continue
            if status == "unknown" or not core_indexes:
                completed = False
                continue
            for index in core_indexes:
                child = excluded | frozenset({index})
                if child not in visited and not any(existing <= child for existing in pending):
                    pending.append(child)

        if pending or solver_checks >= max_solver_checks:
            completed = False
        return tuple(repairs), completed

    def _supporting_facts(self, conflicts: tuple[ConstraintDiagnostic, ...]) -> tuple[ConstraintDiagnostic, ...]:
        """Add configuration facts and workload details needed to interpret a core."""
        constrained_faculty = {
            diagnostic.subjects[0]
            for diagnostic in conflicts
            if diagnostic.kind.startswith("faculty_") and diagnostic.subjects
        }
        facts: list[ConstraintDiagnostic] = []
        for course in self._courses:
            if len(course.faculties) == 1 and course.faculties[0] in constrained_faculty:
                faculty = course.faculties[0]
                facts.append(
                    ConstraintDiagnostic(
                        kind="forced_course_faculty",
                        subjects=(str(course), faculty),
                        message=f"Course {course} can only be assigned to faculty {faculty}",
                    )
                )
                facts.append(
                    ConstraintDiagnostic(
                        kind="faculty_workload_contribution",
                        subjects=(faculty, str(course)),
                        message=f"Course {course} contributes {course.credits} credits to faculty {faculty}",
                    )
                )

            if len(course.rooms) == 1:
                facts.append(
                    ConstraintDiagnostic(
                        kind="forced_course_room",
                        subjects=(str(course), course.rooms[0]),
                        message=f"Course {course} can only use room {course.rooms[0]}",
                    )
                )
            if len(course.labs) == 1:
                facts.append(
                    ConstraintDiagnostic(
                        kind="forced_course_lab",
                        subjects=(str(course), course.labs[0]),
                        message=f"Course {course} can only use lab {course.labs[0]}",
                    )
                )

            start, stop = self._ranges[course.credits]
            compatible_patterns = [
                slot
                for index, slot in enumerate(self._slots)
                if start <= index <= stop and slot.has_lab() == bool(course.labs)
            ]
            if len(compatible_patterns) == 1:
                facts.append(
                    ConstraintDiagnostic(
                        kind="forced_course_time_pattern",
                        subjects=(str(course),),
                        message=f"Course {course} has exactly one compatible meeting pattern",
                    )
                )

        for faculty in constrained_faculty:
            forced_courses = [course for course in self._courses if course.faculties == [faculty]]
            if any(
                diagnostic.kind == "faculty_unique_course_limit" and diagnostic.subjects[0] == faculty
                for diagnostic in conflicts
            ):
                for course_id in sorted({course.course_id for course in forced_courses}):
                    facts.append(
                        ConstraintDiagnostic(
                            kind="faculty_unique_course_contribution",
                            subjects=(faculty, course_id),
                            message=f"Faculty {faculty} is forced to teach course {course_id}",
                        )
                    )
            if any(
                diagnostic.kind in {"faculty_maximum_days", "faculty_mandatory_day"}
                and diagnostic.subjects[0] == faculty
                for diagnostic in conflicts
            ):
                for course in forced_courses:
                    start, stop = self._ranges[course.credits]
                    days = sorted(
                        {
                            time.day.name
                            for index, slot in enumerate(self._slots)
                            if start <= index <= stop and slot.has_lab() == bool(course.labs)
                            for time in slot.times
                        }
                    )
                    facts.append(
                        ConstraintDiagnostic(
                            kind="course_possible_teaching_days",
                            subjects=(faculty, str(course), *days),
                            message=f"Course {course} can meet on: {', '.join(days)}",
                        )
                    )

        for diagnostic in conflicts:
            if diagnostic.kind != "faculty_mandatory_day" or len(diagnostic.subjects) < 2:
                continue
            faculty, day_name = diagnostic.subjects[:2]
            day = Day[day_name]
            availability = [str(instance) for instance in self._faculty_availability[faculty] if instance.day == day]
            if availability:
                message = f"Faculty {faculty} is available on {day_name} only during: {', '.join(availability)}"
            else:
                message = f"Faculty {faculty} has no availability windows on {day_name}"
            facts.append(
                ConstraintDiagnostic(
                    kind="faculty_day_availability",
                    subjects=(faculty, day_name),
                    message=message,
                )
            )
            for course in self._courses:
                if faculty not in course.faculties:
                    continue
                start, stop = self._ranges[course.credits]
                compatible = [
                    slot
                    for index, slot in enumerate(self._slots)
                    if start <= index <= stop and slot.has_lab() == bool(course.labs)
                ]
                day_compatible = [slot for slot in compatible if any(time.day == day for time in slot.times)]
                if not day_compatible:
                    facts.append(
                        ConstraintDiagnostic(
                            kind="course_day_pattern_gap",
                            subjects=(str(course), day_name),
                            message=f"Course {course} has no compatible meeting pattern on {day_name}",
                        )
                    )
        return tuple(self._make_diagnostic(fact.kind, fact.subjects, fact.message) for fact in facts)

    def _relaxation_suggestions(
        self,
        conflicts: tuple[ConstraintDiagnostic, ...],
        supporting_facts: tuple[ConstraintDiagnostic, ...],
    ) -> tuple[RelaxationSuggestion, ...]:
        """Provide conservative, directly-derived candidate relaxations."""
        suggestions: list[RelaxationSuggestion] = []
        for conflict in conflicts:
            if conflict.kind == "faculty_credit_range" and conflict.subjects:
                faculty = conflict.subjects[0]
                forced_credits = sum(course.credits for course in self._courses if course.faculties == [faculty])
                maximum = self._faculty_maximum_credits[faculty]
                if forced_credits > maximum:
                    suggestions.append(
                        RelaxationSuggestion(
                            kind="increase_faculty_maximum_credits",
                            subjects=(faculty,),
                            message=f"Increase {faculty}'s maximum credits from {maximum} to at least {forced_credits}",
                        )
                    )
                    for course in self._courses:
                        if course.faculties == [faculty]:
                            suggestions.append(
                                RelaxationSuggestion(
                                    kind="add_faculty_candidate",
                                    subjects=(str(course), faculty),
                                    message=f"Add another eligible faculty candidate for course {course}",
                                )
                            )
            elif conflict.kind == "faculty_unique_course_limit" and conflict.subjects:
                faculty = conflict.subjects[0]
                suggestions.append(
                    RelaxationSuggestion(
                        kind="increase_faculty_unique_course_limit",
                        subjects=(faculty,),
                        message=f"Increase {faculty}'s unique-course limit or reassign one forced course",
                    )
                )
            elif conflict.kind == "faculty_maximum_days" and conflict.subjects:
                faculty = conflict.subjects[0]
                suggestions.append(
                    RelaxationSuggestion(
                        kind="increase_faculty_maximum_days",
                        subjects=(faculty,),
                        message=f"Increase {faculty}'s maximum teaching days or reassign a course",
                    )
                )
            elif conflict.kind == "faculty_mandatory_day" and len(conflict.subjects) >= 2:
                faculty, day_name = conflict.subjects[:2]
                suggestions.append(
                    RelaxationSuggestion(
                        kind="adjust_mandatory_day_or_availability",
                        subjects=(faculty, day_name),
                        message=f"Add {day_name} availability or remove {day_name} from {faculty}'s mandatory days",
                    )
                )
            elif conflict.kind == "course_conflict":
                suggestions.append(
                    RelaxationSuggestion(
                        kind="relax_course_conflict",
                        subjects=conflict.subjects,
                        message=(
                            f"Relax the declared conflict between {conflict.subjects[0]} and {conflict.subjects[1]}"
                        ),
                    )
                )
            elif conflict.kind in {"shared_room_overlap", "shared_lab_overlap"}:
                suggestions.append(
                    RelaxationSuggestion(
                        kind="add_resource_candidate",
                        subjects=conflict.subjects,
                        message=(
                            f"Add another room or lab candidate for {conflict.subjects[0]} or {conflict.subjects[1]}"
                        ),
                    )
                )
        if not suggestions and any(fact.kind == "forced_course_faculty" for fact in supporting_facts):
            for fact in supporting_facts:
                if fact.kind == "forced_course_faculty":
                    course, faculty = fact.subjects
                    suggestions.append(
                        RelaxationSuggestion(
                            kind="add_faculty_candidate",
                            subjects=(course, faculty),
                            message=f"Add another eligible faculty candidate for course {course}",
                        )
                    )
        return tuple(
            RelaxationSuggestion(
                kind=suggestion.kind,
                subjects=suggestion.subjects,
                message=suggestion.message,
                priority=priority,
            )
            for priority, suggestion in enumerate(suggestions, start=1)
        )

    @cache
    def _simplify(self, x: z3.ExprRef) -> z3.BoolRef:
        """
        Cached simplification to avoid redundant computation

        **Usage:**
        ```python
        self._simplify(z3_expr)
        ```
        """
        return cast(z3.BoolRef, z3.simplify(x, cache_all=True, local_ctx=True))

    @cache
    def _cached_slot_relationship(self, fn_name: str, slot_i: TimeSlot, slot_j: TimeSlot) -> bool:
        if fn_name == "overlaps":
            return slot_i.overlaps(slot_j)
        elif fn_name == "lab_overlaps":
            return slot_i.lab_overlaps(slot_j)
        elif fn_name == "lecture_next_to":
            return slot_i.lecture_next_to(slot_j)
        elif fn_name == "lab_next_to":
            return slot_i.lab_next_to(slot_j)
        else:
            raise ValueError(f"Unknown relationship function: {fn_name}")

    def _z3ify_time_constraint(
        self, z3_data: _Z3SortsAndConstants, name: str, *, ctx: z3.Context | None = None
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        z3fn = z3.Function(
            name,
            z3_data.time_slot_sort,
            z3_data.time_slot_sort,
            z3.BoolSort(ctx=ctx),
        )

        true: list[tuple[z3.BoolRef, z3.BoolRef]] = []
        false: list[tuple[z3.BoolRef, z3.BoolRef]] = []

        for slot_i, slot_j in itertools.combinations_with_replacement(self._slots, 2):
            c_i = cast(z3.BoolRef, z3_data.time_slot_constants[slot_i])
            c_j = cast(z3.BoolRef, z3_data.time_slot_constants[slot_j])
            if self._cached_slot_relationship(name, slot_i, slot_j):
                true.append((c_i, c_j))
                true.append((c_j, c_i))
            else:
                false.append((c_i, c_j))
                false.append((c_j, c_i))

        constraints: list[z3.BoolRef] = []
        if true:
            constraints.append(cast(z3.BoolRef, z3.And([z3fn(ts_i, ts_j) for ts_i, ts_j in true])))
        if false:
            constraints.append(
                cast(
                    z3.BoolRef,
                    z3.And([z3.Not(z3fn(ts_i, ts_j)) for ts_i, ts_j in false]),
                )
            )

        return z3fn, constraints

    def _z3ify_time_slot_fn(
        self,
        z3_data: _Z3SortsAndConstants,
        name: str,
        fn: Callable[[TimeSlot], bool],
        *,
        ctx: z3.Context | None = None,
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        z3fn = z3.Function(name, z3_data.time_slot_sort, z3.BoolSort(ctx=ctx))

        true: list[z3.BoolRef] = []
        false: list[z3.BoolRef] = []
        for slot in self._slots:
            c = cast(z3.BoolRef, z3_data.time_slot_constants[slot])
            if fn(slot):
                true.append(c)
            else:
                false.append(c)
        constraints: list[z3.BoolRef] = []
        if true:
            constraints.append(cast(z3.BoolRef, z3.And([z3fn(ts) for ts in true])))
        if false:
            constraints.append(cast(z3.BoolRef, z3.And([z3.Not(z3fn(ts)) for ts in false])))
        return z3fn, constraints

    def _z3ify_faculty_time_constraint(
        self, z3_data: _Z3SortsAndConstants, name: str, *, ctx: z3.Context | None = None
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        z3fn = z3.Function(
            name,
            z3_data.faculty_sort,
            z3_data.time_slot_sort,
            z3.BoolSort(ctx=ctx),
        )

        constraints: list[z3.BoolRef] = []
        for faculty in self._faculty:
            true: list[tuple[z3.BoolRef, z3.BoolRef]] = []
            false: list[tuple[z3.BoolRef, z3.BoolRef]] = []
            faculty_times = self._faculty_availability[faculty]
            faculty_constant = cast(z3.BoolRef, z3_data.faculty_constants[faculty])
            for slot in self._slots:
                slot_constant = cast(z3.BoolRef, z3_data.time_slot_constants[slot])
                if slot.in_time_ranges(faculty_times):
                    true.append((faculty_constant, slot_constant))
                else:
                    false.append((faculty_constant, slot_constant))
            if true:
                constraints.append(
                    cast(
                        z3.BoolRef,
                        z3.And([z3fn(faculty, slot) for faculty, slot in true]),
                    )
                )
            if false:
                constraints.append(
                    cast(
                        z3.BoolRef,
                        z3.And([z3.Not(z3fn(faculty, slot)) for faculty, slot in false]),
                    )
                )

        return z3fn, constraints

    def _build_function_constraints(self, z3_data: _Z3SortsAndConstants) -> _FunctionConstraints:
        """
        Create Z3 function definitions and their constraints.

        **Usage:**
        ```python
        self._build_function_constraints(z3_data)
        ```

        **Args:**
        - z3_data: `_Z3SortsAndConstants` object containing the Z3 sorts and constants

        **Returns:**
        - `_FunctionConstraints` object containing the Z3 function definitions and their constraints
        """
        # abstract function constraints
        overlaps, overlaps_C = self._z3ify_time_constraint(z3_data, "overlaps", ctx=self._ctx)
        lab_overlaps, lab_overlaps_C = self._z3ify_time_constraint(z3_data, "lab_overlaps", ctx=self._ctx)
        lecture_next_to, lecture_next_to_C = self._z3ify_time_constraint(z3_data, "lecture_next_to", ctx=self._ctx)
        faculty_available, faculty_available_C = self._z3ify_faculty_time_constraint(
            z3_data, "faculty_available", ctx=self._ctx
        )
        lab_next_to, lab_next_to_C = self._z3ify_time_constraint(z3_data, "lab_next_to", ctx=self._ctx)

        function_constraints: list[z3.BoolRef] = []
        function_constraints.extend(overlaps_C)
        function_constraints.extend(lab_overlaps_C)
        function_constraints.extend(lecture_next_to_C)
        function_constraints.extend(lab_next_to_C)
        function_constraints.extend(faculty_available_C)

        return _FunctionConstraints(
            constraints=function_constraints,
            overlaps=overlaps,
            lab_overlaps=lab_overlaps,
            lecture_next_to=lecture_next_to,
            faculty_available=faculty_available,
            lab_next_to=lab_next_to,
        )

    def _build_faculty_constraints(self, z3_data: _Z3SortsAndConstants) -> list[z3.BoolRef]:
        """
        Create constraints for faculty credit limits and unique course limits.

        **Usage:**
        ```python
        self._build_faculty_constraints(z3_data)
        ```

        **Args:**
        - z3_data: `_Z3SortsAndConstants` object containing the Z3 sorts and constants

        **Returns:**
        - `list[z3.BoolRef]` containing the faculty constraints
        """
        # Pre-compute course groupings to reduce repeated calculations
        # Pre-compute time slot constants per day for reuse
        day_slot_map: defaultdict[Day, set[z3.ExprRef]] = defaultdict(set)
        for slot in self._slots:
            slot_constant = z3_data.time_slot_constants[slot]
            for time_instance in slot.times:
                day_slot_map[time_instance.day].add(slot_constant)
        day_to_slot_constants: dict[Day, tuple[z3.ExprRef, ...]] = {
            day: tuple(slot_constants) for day, slot_constants in day_slot_map.items()
        }

        # Add faculty credit and unique course limits - batch generation
        faculty_constraints: list[z3.BoolRef] = []
        for faculty in self._faculty:
            # Include every course in these sums.  Course-level eligibility
            # constraints make non-candidate terms false, while this also
            # correctly detects faculty with positive minimums and no work.
            faculty_courses = self._courses
            faculty_constant = z3_data.faculty_constants[faculty]
            max_days = self._faculty_maximum_days[faculty]
            mandatory_days = self._faculty_mandatory_days[faculty]
            min_credits = self._faculty_minimum_credits[faculty]
            max_credits = self._faculty_maximum_credits[faculty]
            credit_sum = z3.Sum([z3.If(c.faculty == faculty_constant, c.credits, 0) for c in faculty_courses])
            # Ensure that every faculty is assigned between their min and max,
            # including faculty with no eligible courses.
            credit_constraint = cast(z3.BoolRef, z3.And(credit_sum >= min_credits, credit_sum <= max_credits))
            faculty_constraints.append(credit_constraint)
            self._diagnostic_constraints.append(
                _DiagnosticConstraint(
                    credit_constraint,
                    f"Faculty {faculty} must teach between {min_credits} and {max_credits} credits",
                    kind="faculty_credit_range",
                    subjects=(faculty,),
                )
            )

            unique_limit = self._faculty_unique_course_limits[faculty]
            unique_courses: defaultdict[str, list[Course]] = defaultdict(list)
            for c in faculty_courses:
                unique_courses[c.course_id].append(c)
            if len(unique_courses) > unique_limit:
                teaches_course: list[z3.BoolRef] = []
                for course_group in unique_courses.values():
                    teaches_course.append(
                        cast(
                            z3.BoolRef,
                            z3.Or([c.faculty == faculty_constant for c in course_group]),
                        )
                    )
                limit = self._simplify(z3.Sum([z3.If(tc, 1, 0) for tc in teaches_course]) <= unique_limit)
                faculty_constraints.append(limit)
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        limit,
                        f"Faculty {faculty} may teach at most {unique_limit} distinct courses",
                        kind="faculty_unique_course_limit",
                        subjects=(faculty,),
                    )
                )

            # Track whether the faculty teaches on a given day
            day_indicator_map: dict[Day, z3.BoolRef] = {}
            for day in Day:
                slot_constants = day_to_slot_constants.get(day, ())
                course_day_assignments: list[z3.BoolRef] = []
                if slot_constants and faculty_courses:
                    for course in faculty_courses:
                        slot_matches = [course.time == slot_const for slot_const in slot_constants]
                        if slot_matches:
                            course_day_assignments.append(
                                self._simplify(
                                    z3.And(
                                        course.faculty == faculty_constant,
                                        z3.Or(slot_matches),
                                    )
                                )
                            )
                if course_day_assignments:
                    day_indicator_map[day] = self._simplify(z3.Or(course_day_assignments))
                else:
                    day_indicator_map[day] = z3.BoolVal(False, ctx=self._ctx)

            # Maximum-day constraint
            day_sum_terms = [z3.If(indicator, 1, 0) for indicator in day_indicator_map.values()]
            day_sum = z3.Sum(day_sum_terms) if day_sum_terms else z3.IntVal(0, ctx=self._ctx)
            max_days_constraint = self._simplify(day_sum <= max_days)
            faculty_constraints.append(max_days_constraint)
            self._diagnostic_constraints.append(
                _DiagnosticConstraint(
                    max_days_constraint,
                    f"Faculty {faculty} may teach at most {max_days} days",
                    kind="faculty_maximum_days",
                    subjects=(faculty,),
                )
            )

            # Mandatory-day constraints
            for mandatory_day in mandatory_days:
                indicator = day_indicator_map.get(mandatory_day, z3.BoolVal(False, ctx=self._ctx))
                faculty_constraints.append(self._simplify(indicator))
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        self._simplify(indicator),
                        f"Faculty {faculty} must teach on {mandatory_day.name}",
                        kind="faculty_mandatory_day",
                        subjects=(faculty, mandatory_day.name),
                    )
                )

        return faculty_constraints

    def _build_course_constraints(
        self,
        overlaps: z3.FuncDeclRef,
        faculty_available: z3.FuncDeclRef,
        z3_data: _Z3SortsAndConstants,
    ) -> list[z3.BoolRef]:
        """
        Create individual course constraints.

        **Usage:**
        ```python
        self._build_course_constraints(overlaps, faculty_available, z3_data)
        ```

        **Args:**
        - overlaps: `z3.FuncDeclRef` function for checking time overlaps
        - faculty_available: `z3.FuncDeclRef` function for checking faculty availability
        - z3_data: `_Z3SortsAndConstants` object containing the Z3 sorts and constants

        **Returns:**
        - `list[z3.BoolRef]` containing the course constraints
        """
        # Course constraints with optimized conflict checking - batch generation
        course_constraints: list[z3.BoolRef] = []
        for c in self._courses:
            # conflict constraints
            conflict_constraints: list[z3.BoolRef] = []
            for d in self._courses:
                if d != c and d.course_id in c.conflicts:
                    conflict = cast(z3.BoolRef, z3.Not(overlaps(c.time, d.time)))
                    conflict_constraints.append(conflict)
                    self._diagnostic_constraints.append(
                        _DiagnosticConstraint(
                            conflict,
                            f"Course {c} must not overlap course {d}",
                            kind="course_conflict",
                            subjects=(str(c), str(d)),
                        )
                    )

            # faculty availability constraint
            availability_constraint = cast(z3.BoolRef, faculty_available(c.faculty, c.time))
            course_constraint_list: list[z3.BoolRef] = [availability_constraint]
            self._diagnostic_constraints.append(
                _DiagnosticConstraint(
                    availability_constraint,
                    f"Course {c} must use an available faculty time",
                    kind="faculty_availability",
                    subjects=(str(c),),
                )
            )

            # Get valid time slots for this credit level
            start, stop = self._ranges[c.credits]
            requires_lab = bool(c.labs)
            valid_time_slots = {
                i for i, slot in enumerate(self._slots) if start <= i <= stop and slot.has_lab() == requires_lab
            }
            if valid_time_slots:
                # Constrain time to valid slots for this credit level
                time_constraint = cast(
                    z3.BoolRef,
                    z3.Or([c.time == z3_data.time_slot_constants[self._slots[i]] for i in valid_time_slots]),
                )
                course_constraint_list.append(time_constraint)
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        time_constraint,
                        f"Course {c} must use a compatible {c.credits}-credit meeting pattern",
                        kind="course_time_pattern",
                        subjects=(str(c),),
                    )
                )

            if c.labs:
                # we must assign to a lab when we have options
                lab_constraint = cast(
                    z3.BoolRef,
                    z3.Or([c.lab == z3_data.lab_constants[lab] for lab in self._labs if lab in c.labs]),
                )
                course_constraint_list.append(lab_constraint)
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        lab_constraint,
                        f"Course {c} must use one of its allowed labs",
                        kind="course_lab_eligibility",
                        subjects=(str(c), *c.labs),
                    )
                )
            else:
                course_constraint_list.append(cast(z3.BoolRef, c.lab == z3_data.lab_constants[None]))
            if c.rooms:
                # we must assign to a room when we have options
                room_constraint = cast(
                    z3.BoolRef,
                    z3.Or([c.room == z3_data.room_constants[room] for room in self._rooms if room in c.rooms]),
                )
                course_constraint_list.append(room_constraint)
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        room_constraint,
                        f"Course {c} must use one of its allowed rooms",
                        kind="course_room_eligibility",
                        subjects=(str(c), *c.rooms),
                    )
                )
            if c.faculties:
                # we must assign to a faculty from the candidates
                faculty_constraint = cast(
                    z3.BoolRef,
                    z3.Or([c.faculty == z3_data.faculty_constants[faculty] for faculty in c.faculties]),
                )
                course_constraint_list.append(faculty_constraint)
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        faculty_constraint,
                        f"Course {c} must use one of its eligible faculty",
                        kind="course_faculty_eligibility",
                        subjects=(str(c), *c.faculties),
                    )
                )
            if conflict_constraints:
                conflict_constraint = cast(z3.BoolRef, z3.And(conflict_constraints))
                course_constraint_list.append(conflict_constraint)

            course_constraints.append(cast(z3.BoolRef, z3.And(course_constraint_list)))

        return course_constraints

    def _build_resource_constraints(
        self,
        overlaps: z3.FuncDeclRef,
        lab_overlaps: z3.FuncDeclRef,
        lecture_next_to: z3.FuncDeclRef,
        lab_next_to: z3.FuncDeclRef,
        z3_data: _Z3SortsAndConstants,
    ) -> list[z3.BoolRef]:
        """
        Create resource sharing and faculty scheduling constraints.

        **Usage:**
        ```python
        self._build_resource_constraints(overlaps, lab_overlaps, lecture_next_to, lab_next_to, z3_data)
        ```

        **Args:**
        - overlaps: `z3.FuncDeclRef` function for checking time overlaps
        - lab_overlaps: `z3.FuncDeclRef` function for checking lab overlaps
        - lecture_next_to: `z3.FuncDeclRef` function for checking lecture next to each other
        - lab_next_to: `z3.FuncDeclRef` function for checking lab next to each other
        - z3_data: `_Z3SortsAndConstants` object containing the Z3 sorts and constants

        **Returns:**
        - `list[z3.BoolRef]` containing the resource constraints
        """
        resource_constraints: list[z3.BoolRef] = []

        for i, j in itertools.combinations(self._courses, 2):
            resource: list[z3.BoolRef] = []
            constraint_parts: list[z3.BoolRef] = []
            shared_faculty_parts: list[tuple[z3.BoolRef, str, str]] = []

            # Enforce same room usage when both courses can use the same rooms
            if set(i.rooms) & set(j.rooms):
                shared_room_constraint = cast(
                    z3.BoolRef,
                    z3.Implies(i.room == j.room, z3.Not(overlaps(i.time, j.time))),
                )
                resource.append(shared_room_constraint)
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        shared_room_constraint,
                        f"Courses {i} and {j} cannot overlap when sharing a room",
                        kind="shared_room_overlap",
                        subjects=(str(i), str(j)),
                    )
                )
                if i.course_id == j.course_id:
                    # when a faculty teaches two sections of the same course,
                    # they must use the same room
                    same_room_constraint = cast(z3.BoolRef, i.room == j.room)
                    constraint_parts.append(same_room_constraint)
                    shared_faculty_parts.append(
                        (same_room_constraint, "same_course_room", f"Sections {i} and {j} must use the same room")
                    )

            # Enforce same lab usage when both courses have labs and can use the same labs
            if set(i.labs) & set(j.labs):
                shared_lab_constraint = cast(
                    z3.BoolRef,
                    z3.Implies(i.lab == j.lab, z3.Not(lab_overlaps(i.time, j.time))),
                )
                resource.append(shared_lab_constraint)
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        shared_lab_constraint,
                        f"Courses {i} and {j} cannot overlap when sharing a lab",
                        kind="shared_lab_overlap",
                        subjects=(str(i), str(j)),
                    )
                )
                if i.course_id == j.course_id:
                    # when a faculty teaches two sections of the same course,
                    # they must use the same lab
                    same_lab_constraint = cast(z3.BoolRef, i.lab == j.lab)
                    constraint_parts.append(same_lab_constraint)
                    shared_faculty_parts.append(
                        (same_lab_constraint, "same_course_lab", f"Sections {i} and {j} must use the same lab")
                    )

            # Prevent time overlap for courses taught by same faculty
            shared_faculty_overlap = cast(z3.BoolRef, z3.Not(overlaps(i.time, j.time)))
            constraint_parts.append(shared_faculty_overlap)
            shared_faculty_parts.append(
                (
                    shared_faculty_overlap,
                    "shared_faculty_overlap",
                    f"Courses {i} and {j} cannot overlap for one faculty",
                )
            )
            if i.course_id == j.course_id:
                # when a faculty teaches two sections of the same course,
                # they must be next to each other
                lecture_adjacency = cast(z3.BoolRef, lecture_next_to(i.time, j.time))
                constraint_parts.append(lecture_adjacency)
                shared_faculty_parts.append(
                    (lecture_adjacency, "same_course_lecture_adjacency", f"Sections {i} and {j} must be adjacent")
                )
                # Only require lab_next_to if the course has labs
                if i.labs:
                    lab_adjacency = cast(z3.BoolRef, lab_next_to(i.time, j.time))
                    constraint_parts.append(lab_adjacency)
                    shared_faculty_parts.append(
                        (lab_adjacency, "same_course_lab_adjacency", f"Sections {i} and {j} must have adjacent labs")
                    )
            else:
                # when a faculty teaches two sections of different courses,
                # they must not be next to each other
                lecture_separation = cast(z3.BoolRef, z3.Not(lecture_next_to(i.time, j.time)))
                constraint_parts.append(lecture_separation)
                shared_faculty_parts.append(
                    (
                        lecture_separation,
                        "different_course_lecture_separation",
                        f"Courses {i} and {j} cannot be adjacent",
                    )
                )
                # Only require lab_next_to constraint if both courses have labs
                if i.labs and j.labs:
                    lab_separation = cast(z3.BoolRef, z3.Not(lab_next_to(i.time, j.time)))
                    constraint_parts.append(lab_separation)
                    shared_faculty_parts.append(
                        (
                            lab_separation,
                            "different_course_lab_separation",
                            f"Courses {i} and {j} cannot have adjacent labs",
                        )
                    )

            if i.course_id == j.course_id:
                # prevent overlapping times for different sections of the same course
                section_overlap_constraint = cast(z3.BoolRef, z3.Not(overlaps(i.time, j.time)))
                resource_constraints.append(section_overlap_constraint)
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        section_overlap_constraint,
                        f"Sections {i} and {j} must not overlap",
                        kind="section_overlap",
                        subjects=(str(i), str(j)),
                    )
                )

            if resource:
                # add all resource constraints (room, lab, etc.)
                shared_resource_constraint = cast(z3.BoolRef, z3.And(resource))
                resource_constraints.append(shared_resource_constraint)
            # add all course constraints when faculty is the same
            shared_faculty_constraint = cast(
                z3.BoolRef,
                z3.Implies(i.faculty == j.faculty, z3.And(constraint_parts)),
            )
            resource_constraints.append(shared_faculty_constraint)
            for constraint, kind, message in shared_faculty_parts:
                self._diagnostic_constraints.append(
                    _DiagnosticConstraint(
                        cast(z3.BoolRef, z3.Implies(i.faculty == j.faculty, constraint)),
                        message,
                        kind=kind,
                        subjects=(str(i), str(j)),
                    )
                )

        return resource_constraints

    def _aggregate_constraints(
        self,
        function_constraints: list[z3.BoolRef],
        faculty_constraints: list[z3.BoolRef],
        course_constraints: list[z3.BoolRef],
        resource_constraints: list[z3.BoolRef],
    ) -> list[z3.BoolRef]:
        """
        Combine all constraints and apply simplification.

        **Usage:**
        ```python
        self._aggregate_constraints(function_c, faculty_c, course_c, resource_c)
        ```

        **Args:**
        - function_constraints: `list[z3.BoolRef]` containing the function constraints
        - faculty_constraints: `list[z3.BoolRef]` containing the faculty constraints
        - course_constraints: `list[z3.BoolRef]` containing the course constraints
        - resource_constraints: `list[z3.BoolRef]` containing the resource constraints

        **Returns:**
        - `list[z3.BoolRef]` containing the aggregated constraints
        """
        all_constraints: list[z3.BoolRef] = []

        for c in itertools.chain(
            function_constraints,
            faculty_constraints,
            course_constraints,
            resource_constraints,
        ):
            all_constraints.append(self._simplify(c))

        logger.debug(f"Added {len(function_constraints)} function constraints")
        logger.debug(f"Added {len(faculty_constraints)} faculty constraints")
        logger.debug(f"Added {len(course_constraints)} course constraints")
        logger.debug(f"Added {len(resource_constraints)} resource constraints")

        return all_constraints

    def audit_schedule(self, schedule: list["CourseInstance"]) -> ScheduleAudit:
        """Independently audit one emitted schedule and explain its soft scores.

        This accepts a schedule returned by :meth:`get_models`; it does not
        trust the solver model and therefore also catches serialization or
        downstream mutation errors.
        """
        by_course = {str(instance.course): instance for instance in schedule}
        violations: list[ConstraintDiagnostic] = []
        expected_courses = {str(course) for course in self._courses}
        if set(by_course) != expected_courses or len(schedule) != len(self._courses):
            violations.append(
                self._make_diagnostic(
                    "schedule_course_coverage",
                    tuple(sorted(set(by_course) ^ expected_courses)),
                    "Schedule must contain exactly one assignment for every configured course section",
                )
            )

        for course in self._courses:
            instance = by_course.get(str(course))
            if instance is None:
                continue
            if instance.faculty not in course.faculties:
                violations.append(
                    self._make_diagnostic(
                        "course_faculty_eligibility",
                        (str(course), instance.faculty),
                        f"Course {course} is assigned ineligible faculty {instance.faculty}",
                    )
                )
            if instance.room not in course.rooms:
                violations.append(
                    self._make_diagnostic(
                        "course_room_eligibility",
                        (str(course), str(instance.room)),
                        f"Course {course} is assigned ineligible room {instance.room}",
                    )
                )
            if (course.labs and instance.lab not in course.labs) or (not course.labs and instance.lab is not None):
                violations.append(
                    self._make_diagnostic(
                        "course_lab_eligibility",
                        (str(course), str(instance.lab)),
                        f"Course {course} has an invalid lab assignment {instance.lab}",
                    )
                )
            if instance.time not in self._compatible_slots(course):
                violations.append(
                    self._make_diagnostic(
                        "course_time_pattern",
                        (str(course),),
                        f"Course {course} uses a meeting pattern incompatible with its credits or lab requirement",
                    )
                )
            if instance.faculty in self._faculty_availability and not instance.time.in_time_ranges(
                self._faculty_availability[instance.faculty]
            ):
                violations.append(
                    self._make_diagnostic(
                        "faculty_availability",
                        (str(course), instance.faculty),
                        f"Course {course} falls outside {instance.faculty}'s availability",
                    )
                )

        workloads: list[FacultyWorkloadDiagnostic] = []
        for faculty in self._faculty:
            assigned = [instance for instance in schedule if instance.faculty == faculty]
            credits = sum(instance.course.credits for instance in assigned)
            days = tuple(sorted({time.day.name for instance in assigned for time in instance.time.times}))
            course_ids = {instance.course.course_id for instance in assigned}
            mandatory = self._faculty_mandatory_days[faculty]
            mandatory_satisfied = mandatory <= {Day[day] for day in days}
            workloads.append(
                FacultyWorkloadDiagnostic(
                    faculty=faculty,
                    credits=credits,
                    minimum_credits=self._faculty_minimum_credits[faculty],
                    maximum_credits=self._faculty_maximum_credits[faculty],
                    teaching_days=days,
                    maximum_days=self._faculty_maximum_days[faculty],
                    distinct_courses=len(course_ids),
                    unique_course_limit=self._faculty_unique_course_limits[faculty],
                    mandatory_days_satisfied=mandatory_satisfied,
                    locations=(self._faculty_config_paths[faculty],),
                )
            )
            if not self._faculty_minimum_credits[faculty] <= credits <= self._faculty_maximum_credits[faculty]:
                violations.append(
                    self._make_diagnostic(
                        "faculty_credit_range",
                        (faculty,),
                        f"Faculty {faculty} has {credits} credits outside "
                        f"{self._faculty_minimum_credits[faculty]}-{self._faculty_maximum_credits[faculty]}",
                    )
                )
            if len(days) > self._faculty_maximum_days[faculty]:
                violations.append(
                    self._make_diagnostic(
                        "faculty_maximum_days",
                        (faculty,),
                        f"Faculty {faculty} teaches {len(days)} days, exceeding {self._faculty_maximum_days[faculty]}",
                    )
                )
            if len(course_ids) > self._faculty_unique_course_limits[faculty]:
                violations.append(
                    self._make_diagnostic(
                        "faculty_unique_course_limit",
                        (faculty,),
                        f"Faculty {faculty} teaches {len(course_ids)} distinct courses, exceeding "
                        f"{self._faculty_unique_course_limits[faculty]}",
                    )
                )
            for day in mandatory - {Day[day] for day in days}:
                violations.append(
                    self._make_diagnostic(
                        "faculty_mandatory_day",
                        (faculty, day.name),
                        f"Faculty {faculty} is not scheduled on mandatory day {day.name}",
                    )
                )

        usage: list[ResourceUsageDiagnostic] = []
        for kind, attribute in (("room", "room"), ("lab", "lab")):
            grouped: defaultdict[str, list[CourseInstance]] = defaultdict(list)
            for instance in schedule:
                resource = getattr(instance, attribute)
                if resource is not None:
                    grouped[resource].append(instance)
            for resource, assignments in sorted(grouped.items()):
                collisions: list[ConstraintDiagnostic] = []
                for first, second in itertools.combinations(assignments, 2):
                    overlaps = (
                        first.time.lab_overlaps(second.time) if kind == "lab" else first.time.overlaps(second.time)
                    )
                    if overlaps:
                        collisions.append(
                            self._make_diagnostic(
                                f"shared_{kind}_overlap",
                                (str(first.course), str(second.course), resource),
                                f"Courses {first.course} and {second.course} overlap while using {kind} {resource}",
                            )
                        )
                usage.append(
                    ResourceUsageDiagnostic(
                        kind=kind,
                        resource=resource,
                        assignments=tuple(str(instance.course) for instance in assignments),
                        collisions=tuple(collisions),
                    )
                )
                violations.extend(collisions)

        for first, second in itertools.combinations(schedule, 2):
            left, right = first.course, second.course
            if right.course_id in left.conflicts and first.time.overlaps(second.time):
                violations.append(
                    self._make_diagnostic(
                        "course_conflict",
                        (str(left), str(right)),
                        f"Conflicting courses {left} and {right} overlap",
                    )
                )
            if left.course_id == right.course_id and first.time.overlaps(second.time):
                violations.append(
                    self._make_diagnostic(
                        "section_overlap",
                        (str(left), str(right)),
                        f"Sections {left} and {right} overlap",
                    )
                )
            if first.faculty != second.faculty:
                continue
            if first.time.overlaps(second.time):
                violations.append(
                    self._make_diagnostic(
                        "shared_faculty_overlap",
                        (str(left), str(right), first.faculty),
                        f"Faculty {first.faculty} teaches overlapping courses {left} and {right}",
                    )
                )
            if left.course_id == right.course_id:
                if first.room != second.room:
                    violations.append(
                        self._make_diagnostic(
                            "same_course_room",
                            (str(left), str(right)),
                            f"Sections {left} and {right} taught by one faculty use different rooms",
                        )
                    )
                if left.labs and first.lab != second.lab:
                    violations.append(
                        self._make_diagnostic(
                            "same_course_lab",
                            (str(left), str(right)),
                            f"Sections {left} and {right} taught by one faculty use different labs",
                        )
                    )
                if not first.time.lecture_next_to(second.time):
                    violations.append(
                        self._make_diagnostic(
                            "same_course_lecture_adjacency",
                            (str(left), str(right)),
                            f"Sections {left} and {right} taught by one faculty are not adjacent",
                        )
                    )
                if left.labs and not first.time.lab_next_to(second.time):
                    violations.append(
                        self._make_diagnostic(
                            "same_course_lab_adjacency",
                            (str(left), str(right)),
                            f"Sections {left} and {right} taught by one faculty do not have adjacent labs",
                        )
                    )
            else:
                if first.time.lecture_next_to(second.time):
                    violations.append(
                        self._make_diagnostic(
                            "different_course_lecture_separation",
                            (str(left), str(right)),
                            f"Different courses {left} and {right} taught by one faculty are adjacent",
                        )
                    )
                if left.labs and right.labs and first.time.lab_next_to(second.time):
                    violations.append(
                        self._make_diagnostic(
                            "different_course_lab_separation",
                            (str(left), str(right)),
                            f"Different courses {left} and {right} taught by one faculty have adjacent labs",
                        )
                    )

        objective_scores, preference_outcomes = self._objective_diagnostics(schedule)
        return ScheduleAudit(
            is_valid=not violations,
            constraint_violations=tuple(violations),
            faculty_workloads=tuple(workloads),
            resource_usage=tuple(usage),
            objective_scores=objective_scores,
            preference_outcomes=preference_outcomes,
        )

    def _objective_diagnostics(
        self, schedule: list["CourseInstance"]
    ) -> tuple[tuple[ObjectiveScoreDiagnostic, ...], tuple[ConstraintDiagnostic, ...]]:
        """Calculate enabled soft-objective contributions without re-solving."""
        scores: list[ObjectiveScoreDiagnostic] = []
        outcomes: list[ConstraintDiagnostic] = []
        objective_maps = (
            (OptimizerFlags.FACULTY_COURSE, "faculty_course", "course"),
            (OptimizerFlags.FACULTY_ROOM, "faculty_room", "room"),
            (OptimizerFlags.FACULTY_LAB, "faculty_lab", "lab"),
        )
        for flag, objective, target in objective_maps:
            if flag not in self._optimizer_flags:
                continue
            score = 0
            upper_bound = 0
            for instance in schedule:
                preferences = (
                    self._faculty_course_preferences
                    if target == "course"
                    else self._faculty_room_preferences
                    if target == "room"
                    else self._faculty_lab_preferences
                )
                value = instance.course.course_id if target == "course" else getattr(instance, target)
                assigned = preferences[instance.faculty].get(value, 0) if value is not None else 0
                score += assigned
                potential = [preferences[faculty].get(value, 0) for faculty in instance.course.faculties]
                upper_bound += max(potential, default=0)
                if assigned < max(potential, default=0):
                    outcomes.append(
                        self._make_diagnostic(
                            "preference_not_selected",
                            (str(instance.course), instance.faculty, objective),
                            f"Course {instance.course} receives {assigned}/{max(potential, default=0)} "
                            f"available {objective} preference points; hard constraints or competing objectives "
                            "selected "
                            "a lower-scoring eligible assignment",
                        )
                    )
            scores.append(
                ObjectiveScoreDiagnostic(
                    objective=objective,
                    score=score,
                    independent_upper_bound=upper_bound,
                    message=f"Achieved {score} of independent upper bound {upper_bound} for {objective}",
                )
            )
        pair_objectives = (
            (OptimizerFlags.SAME_ROOM, "same_room", "room"),
            (OptimizerFlags.SAME_LAB, "same_lab", "lab"),
            (OptimizerFlags.PACK_ROOMS, "pack_rooms", "room"),
            (OptimizerFlags.PACK_LABS, "pack_labs", "lab"),
        )
        for flag, objective, resource in pair_objectives:
            if flag not in self._optimizer_flags:
                continue
            score = 0
            upper_bound = 0
            for first, second in itertools.combinations(schedule, 2):
                first_candidates = getattr(first.course, f"{resource}s")
                second_candidates = getattr(second.course, f"{resource}s")
                if not set(first_candidates) & set(second_candidates):
                    continue
                if objective.startswith("pack_") and first.course.course_id == second.course.course_id:
                    continue
                upper_bound += 1
                same_resource = getattr(first, resource) == getattr(second, resource)
                if objective == "same_room" or objective == "same_lab":
                    satisfied = first.faculty == second.faculty and same_resource
                elif objective == "pack_rooms":
                    satisfied = same_resource and first.time.lecture_next_to(second.time)
                else:
                    satisfied = same_resource and first.time.lab_next_to(second.time)
                score += int(satisfied)
                if not satisfied:
                    outcomes.append(
                        self._make_diagnostic(
                            "objective_pair_not_selected",
                            (str(first.course), str(second.course), objective),
                            f"Pair {first.course}/{second.course} does not receive the {objective} point; "
                            "the selected schedule trades it against hard constraints or another objective",
                        )
                    )
            scores.append(
                ObjectiveScoreDiagnostic(
                    objective=objective,
                    score=score,
                    independent_upper_bound=upper_bound,
                    message=f"Achieved {score} of independent upper bound {upper_bound} for {objective}",
                )
            )
        return tuple(scores), tuple(outcomes)

    def _get_schedule(self, model: z3.ModelRef) -> list["CourseInstance"]:
        """
        Internal method to convert a Z3 model to a schedule of `CourseInstance` objects.

        **Usage:**
        ```python
        schedule = self._get_schedule(model)
        ```

        **Args:**
        - model: The Z3 model containing assignments

        **Returns:**
        - `list[CourseInstance]` representing the schedule
        """

        schedule = []
        for course in self._courses:
            slot = model.eval(course.time)
            time = self._z3_data.time_slot_constants.inverse[slot]
            faculty = self._z3_data.faculty_constants.inverse.get(model.eval(course.faculty), None)
            room = self._z3_data.room_constants.inverse.get(model.eval(course.room), None)
            lab = self._z3_data.lab_constants.inverse.get(model.eval(course.lab), None)

            if time is None or faculty is None:
                raise ValueError(f"Invalid model: {model}")

            # Create CourseInstance
            course_instance = CourseInstance(
                course=course,
                time=time,
                faculty=faculty,
                room=room,
                lab=lab,
            )
            schedule.append(course_instance)

        return schedule

    def _update(self, s: z3.Optimize):
        """
        Update the Z3 solver with the new constraints.

        **Usage:**
        ```python
        self._update(optimize_solver)
        ```

        **Args:**
        - s: `z3.Optimize` object containing the Z3 solver

        **Returns:**
        - `None`
        """
        m: z3.ModelRef = s.model()
        rearranged = []
        per_course = []
        # group courses by faculty first
        for _, group_iter in itertools.groupby(self._courses, key=lambda x: m[x.faculty]):
            group = list(group_iter)
            for _, cs_iter in itertools.groupby(group, key=lambda x: x.course_id):
                cs = list(cs_iter)
                if len(cs) > 1:
                    rearranged.append(
                        z3.And(
                            [z3.And(i.time != m[j.time], j.time != m[i.time]) for i, j in itertools.combinations(cs, 2)]
                        )
                    )
                for c in cs:
                    per_instance = []
                    per_instance.append(c.time == m[c.time])
                    if c.rooms:
                        per_instance.append(c.room == m[c.room])
                    if c.labs:
                        per_instance.append(c.lab == m[c.lab])
                    per_course.append(z3.Not(z3.And(per_instance)))

        if rearranged:
            logger.debug(f"Adding 1 course rearrangement constraint with {len(rearranged)} predicates")
            s.add(z3.And(rearranged))
        if per_course:
            logger.debug(f"Adding 1 per-course constraint with {len(per_course)} predicates")
            s.add(z3.Or(per_course))

    def get_models(self) -> Generator[list[CourseInstance], None, None]:
        """
        Generate schedules one-at-a-time using the Z3 solver.

        **Usage:**
        ```python
        for schedule in sched.get_models():
            ...
        ```

        **Returns:**
        Generator of lists of `CourseInstance` objects representing complete schedules

        **Example:**
        >>> full_config = load_config_from_file(CombinedConfig, "config.json")
        >>> scheduler = Scheduler(full_config)
        >>> for model in scheduler.get_models():
        ...     for course in model:
        ...         print(course.as_csv())
        """
        s = z3.Optimize(ctx=self._ctx)

        if self._solver_timeout_ms is not None:
            s.set(timeout=self._solver_timeout_ms)

        # Optimized solver configuration for EnumSort-based problems
        # Core optimization settings
        s.set("maxres.maximize_assignment", True)
        s.set("maxsat_engine", "maxres")
        s.set("optsmt_engine", "symba")
        s.set("enable_lns", True)
        s.set("maxres.max_core_size", 100)
        s.set("maxres.wmax", True)
        s.set("pb.compile_equality", True)
        s.set("priority", "pareto")

        for c in self._constraints:
            s.add(c)

        # Add faculty preferences as optimization goals with improved caching - only if requested
        if OptimizerFlags.FACULTY_COURSE in self._optimizer_flags:
            course_preference_terms = []
            for faculty_name, preferences in self._faculty_course_preferences.items():
                if not preferences:  # Skip faculty with no preferences
                    continue

                faculty_constant = self._z3_data.faculty_constants[faculty_name]
                for course in self._courses:
                    if course.course_id in preferences:
                        # Use preference value directly
                        # (1-5 scale where 5 is strongly prefer, 1 is weakest)
                        preference_value = preferences[course.course_id]
                        if preference_value == 0:
                            continue
                        term = z3.If(
                            course.faculty == faculty_constant,
                            preference_value,
                            0,
                        )
                        course_preference_terms.append(term)

            if course_preference_terms:
                n = len(course_preference_terms)
                logger.debug(
                    f"Adding {n} faculty course preference optimization goals",
                )
                s.maximize(z3.Sum(course_preference_terms))

        if OptimizerFlags.FACULTY_ROOM in self._optimizer_flags:
            room_preference_terms = []
            for faculty_name, preferences in self._faculty_room_preferences.items():
                if not preferences:  # Skip faculty with no preferences
                    continue

                faculty_constant = self._z3_data.faculty_constants[faculty_name]
                for course in self._courses:
                    for room in course.rooms:
                        room_constant = self._z3_data.room_constants[room]
                        if room in preferences:
                            preference_value = preferences[room]
                            if preference_value == 0:
                                continue
                            term = z3.If(
                                z3.And(
                                    course.faculty == faculty_constant,
                                    course.room == room_constant,
                                ),
                                preference_value,
                                0,
                            )
                            room_preference_terms.append(term)

            if room_preference_terms:
                n = len(room_preference_terms)
                logger.debug(
                    f"Adding {n} faculty room preference optimization goals",
                )
                s.maximize(z3.Sum(room_preference_terms))

        if OptimizerFlags.FACULTY_LAB in self._optimizer_flags:
            lab_preference_terms = []
            for faculty_name, preferences in self._faculty_lab_preferences.items():
                if not preferences:  # Skip faculty with no preferences
                    continue

                faculty_constant = self._z3_data.faculty_constants[faculty_name]
                for course in self._courses:
                    for lab in course.labs:
                        if lab in preferences:
                            preference_value = preferences[lab]
                            if preference_value == 0:
                                continue
                            term = z3.If(
                                z3.And(
                                    course.faculty == faculty_constant,
                                    course.lab == self._z3_data.lab_constants[lab],
                                ),
                                preference_value,
                                0,
                            )
                            lab_preference_terms.append(term)

            if lab_preference_terms:
                logger.debug(
                    f"Adding {len(lab_preference_terms)} faculty lab preference optimization goals",
                )
                s.maximize(z3.Sum(lab_preference_terms))

        same_rooms = []
        same_labs = []
        packing_rooms = []
        packing_labs = []
        for i, j in itertools.combinations(self._courses, 2):
            if set(i.rooms) & set(j.rooms):
                same_rooms.append(
                    z3.If(
                        z3.And(i.faculty == j.faculty, i.room == j.room),
                        1,
                        0,
                    )
                )
                if i.course_id != j.course_id:
                    packing_rooms.append(
                        z3.If(
                            z3.And(
                                i.room == j.room,
                                self._function_data.lecture_next_to(i.time, j.time),
                            ),
                            1,
                            0,
                        )
                    )
            if set(i.labs) & set(j.labs):
                same_labs.append(z3.If(z3.And(i.faculty == j.faculty, i.lab == j.lab), 1, 0))
                if i.course_id != j.course_id:
                    packing_labs.append(
                        z3.If(
                            z3.And(
                                i.lab == j.lab,
                                self._function_data.lab_next_to(i.time, j.time),
                            ),
                            1,
                            0,
                        )
                    )

        if same_rooms and OptimizerFlags.SAME_ROOM in self._optimizer_flags:
            logger.debug(f"Adding {len(same_rooms)} same room optimization goals")
            s.maximize(z3.Sum(same_rooms))
        if same_labs and OptimizerFlags.SAME_LAB in self._optimizer_flags:
            logger.debug(f"Adding {len(same_labs)} same lab optimization goals")
            s.maximize(z3.Sum(same_labs))
        if packing_rooms and OptimizerFlags.PACK_ROOMS in self._optimizer_flags:
            logger.debug(f"Adding {len(packing_rooms)} room packing optimization goals")
            s.maximize(z3.Sum(packing_rooms))
        if packing_labs and OptimizerFlags.PACK_LABS in self._optimizer_flags:
            logger.debug(f"Adding {len(packing_labs)} lab packing optimization goals")
            s.maximize(z3.Sum(packing_labs))

        if len(self._optimizer_flags) > 0:
            logger.debug("Created all optimization goals")
        else:
            logger.debug("Skipping optimization goals")

        for i in range(self._limit):
            start_time = time.time()
            if s.check() == z3.sat:
                generation_time = time.time() - start_time
                logger.debug(f"Schedule {i + 1} generation took {generation_time:.2f}s")
                yield self._get_schedule(s.model())
                if i < self._limit - 1:
                    self._update(s)
                    i += 1
            else:
                generation_time = time.time() - start_time
                if i == 0:
                    logger.error("No solution found")
                else:
                    logger.warning("No more solutions found")
                logger.debug(f"Final check took {generation_time:.2f} seconds")
                break
