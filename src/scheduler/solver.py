"""Z3-backed constraint construction, optimization, and model enumeration."""

import itertools
import time
from collections import defaultdict
from collections.abc import Callable, Generator, Mapping, Sequence
from copy import copy, deepcopy
from dataclasses import dataclass
from types import MappingProxyType
from typing import cast

import z3
from bidict import frozenbidict

from .config import OptimizerFlags
from .logging import logger
from .models import Course, CourseInstance, Day, TimeInstance, TimeSlot
from .problem import SchedulingProblem

type RoomOverlapKey = tuple[bool, bool]


@dataclass(frozen=True)
class RelationTables:
    """Z3 relation declarations and their finite truth-table constraints.

    Fields:
        constraints: Expressions defining every finite relation-table entry.
        overlaps: Relation indicating whether two complete time slots overlap.
        lab_overlaps: Relation indicating whether two lab meetings overlap.
        lecture_next_to: Relation indicating lecture adjacency.
        faculty_available: Relation indicating faculty availability for a slot.
        lab_next_to: Relation indicating lab-meeting adjacency.
        room_overlaps: Cached, total room-occupancy relations keyed by the two
            courses' lab-reservation policies.
        room_next_to: Cached, total room-occupancy adjacency relations keyed by
            the two courses' lab-reservation policies.
    """

    constraints: tuple[z3.BoolRef, ...]
    overlaps: z3.FuncDeclRef
    lab_overlaps: z3.FuncDeclRef
    lecture_next_to: z3.FuncDeclRef
    faculty_available: z3.FuncDeclRef
    lab_next_to: z3.FuncDeclRef
    room_overlaps: Mapping[RoomOverlapKey, z3.FuncDeclRef]
    room_next_to: Mapping[RoomOverlapKey, z3.FuncDeclRef]


@dataclass(frozen=True)
class Z3Symbols:
    """Z3 enum sorts and deterministic mappings to domain values.

    Fields:
        time_slot_sort: Enum sort representing generated time slots.
        time_slot_constants: Bidirectional mapping from slots to enum constants.
        faculty_sort: Enum sort representing configured faculty.
        faculty_constants: Bidirectional mapping from faculty labels to constants.
        room_sort: Enum sort representing configured rooms.
        room_constants: Bidirectional mapping from room labels or ``None`` to constants.
        lab_sort: Enum sort representing labs plus the internal no-lab value.
        lab_constants: Bidirectional mapping from lab labels or ``None`` to constants.
    """

    time_slot_sort: z3.SortRef
    time_slot_constants: frozenbidict[TimeSlot | None, z3.ExprRef]
    faculty_sort: z3.SortRef
    faculty_constants: frozenbidict[str, z3.ExprRef]
    room_sort: z3.SortRef
    room_constants: frozenbidict[str | None, z3.ExprRef]
    lab_sort: z3.SortRef
    lab_constants: frozenbidict[str | None, z3.ExprRef]


@dataclass(frozen=True)
class DiagnosticConstraintArtifact:
    """Tracked hard-rule expression with business-level explanation metadata.

    Fields:
        expression: Z3 Boolean expression implementing the rule.
        message: Human-readable explanation used in diagnoses.
        kind: Stable business-rule family.
        subjects: Courses, faculty, days, or resources governed by the rule.
    """

    expression: z3.BoolRef
    message: str
    kind: str = "constraint"
    subjects: tuple[str, ...] = ()


@dataclass(frozen=True)
class CourseVariables:
    """Z3 assignment variables for one course section.

    Fields:
        time: Selected time-slot enum variable.
        faculty: Selected faculty enum variable.
        room: Selected room enum variable.
        lab: Selected lab or no-lab enum variable.
    """

    time: z3.ExprRef
    faculty: z3.ExprRef
    room: z3.ExprRef
    lab: z3.ExprRef


@dataclass(frozen=True)
class SolverArtifacts:
    """Read-only solver structures needed for feasibility diagnostics.

    Fields:
        context: Z3 context owning every included expression and declaration.
        symbols: Deterministic enum sorts and domain mappings.
        relations: Finite relation declarations and truth-table constraints.
        constraints: Simplified hard constraints used for normal solving.
        diagnostic_constraints: Individually tracked business-rule constraints.
        course_variables: Immutable mapping from course names to assignment variables.
    """

    context: z3.Context
    symbols: Z3Symbols
    relations: RelationTables
    constraints: tuple[z3.BoolRef, ...]
    diagnostic_constraints: tuple[DiagnosticConstraintArtifact, ...]
    course_variables: Mapping[str, CourseVariables]


class SolverEngine:
    """Own the complete Z3 lifecycle for one normalized problem."""

    def _create_course_variables(self, z3_data: Z3Symbols) -> None:
        """Create solver-owned variables and populate legacy course mirrors."""
        for course in self._courses:
            variables = CourseVariables(
                time=z3.Const(f"{course}_time", z3_data.time_slot_sort),
                faculty=z3.Const(f"{course}_faculty", z3_data.faculty_sort),
                room=z3.Const(f"{course}_room", z3_data.room_sort),
                lab=z3.Const(f"{course}_lab", z3_data.lab_sort),
            )
            self._course_variables[str(course)] = variables
            course.time = variables.time
            course.faculty = variables.faculty
            course.room = variables.room
            course.lab = variables.lab

    def _variables(self, course: Course) -> CourseVariables:
        return self._course_variables[str(course)]

    @property
    def artifacts(self) -> SolverArtifacts:
        """Expose the immutable solver state consumed by diagnostics.

        Args:
            None.

        Returns:
            Frozen symbols, relation tables, constraints, and course-variable map.

        Raises:
            AttributeError: If accessed before engine initialization completes.

        Behavior:
            Returns the same snapshot for the engine lifetime; callers cannot replace
            mapped course variables or mutate the constraint tuples through it.
        """
        return self._artifacts

    @property
    def enumeration_completion_reason(self) -> str | None:
        """Return why the most recently consumed model generator terminated.

        Args:
            None.

        Returns:
            A stable completion reason after solver exhaustion or an unknown result,
            otherwise ``None`` while enumeration is active or has not started.

        Raises:
            None.

        Behavior:
            Reports metadata recorded by the latest ``get_models`` generator without
            advancing, restarting, or otherwise mutating that generator.
        """
        return self._enumeration_completion_reason

    def _create_z3_enumsorts(self) -> Z3Symbols:
        """
        Create Z3 EnumSorts for time slots, faculty, rooms, and labs.

        **Usage:**
        ```python
        z3_data = self._create_z3_enumsorts()
        ```
        """

        # Equal TimeSlot values can be generated for different credit domains.
        # Use one enum value per distinct slot so no unreachable enum constant is
        # left unconstrained when the value-to-symbol lookup deduplicates them.
        unique_slots = tuple(dict.fromkeys(self._slots))
        time_slot_values: tuple[TimeSlot | None, ...] = unique_slots or (None,)
        time_slot_names = (
            ["time_slot_none"] if not unique_slots else [f"time_slot_{i}" for i in range(len(unique_slots))]
        )
        time_slot_sort, time_slot_constants = z3.EnumSort("TimeSlot", time_slot_names, ctx=self._ctx)
        time_slot_constants_dict = frozenbidict(
            {time_slot: time_slot_constants[i] for i, time_slot in enumerate(time_slot_values)}
        )

        # Create Faculty EnumSort
        faculty_names = [f"faculty_{i}" for i in range(len(self._faculty))]
        faculty_sort, faculty_constants = z3.EnumSort("Faculty", faculty_names, ctx=self._ctx)
        faculty_constants_dict = frozenbidict(
            {faculty: faculty_constants[i] for i, faculty in enumerate(self._faculty)},
        )

        # Add an internal no-room value whenever a course has no room candidates
        # or can select a pattern whose meetings do not occupy a lecture room.
        has_roomless_assignment = any(
            not course.rooms
            or any(
                not self._problem._slot_requires_room(
                    slot,
                    reserve_room_during_lab=course.reserve_room_during_lab,
                )
                for slot in self._slots
            )
            for course in self._courses
        )
        room_values: list[str | None] = ([None] if has_roomless_assignment else []) + self._rooms
        room_names = (["room_none"] if has_roomless_assignment else []) + [f"room_{i}" for i in range(len(self._rooms))]
        room_sort, room_constants = z3.EnumSort("Room", room_names, ctx=self._ctx)
        room_constants_dict = frozenbidict(
            {room: room_constants[i] for i, room in enumerate(room_values)},
        )

        # Always include an internal no-lab value so configurations without
        # labs do not create an invalid empty EnumSort.
        lab_values: list[str | None] = [None, *self._labs]
        lab_names = ["lab_none", *[f"lab_{i}" for i in range(len(self._labs))]]
        lab_sort, lab_constants = z3.EnumSort("Lab", lab_names, ctx=self._ctx)
        lab_constants_dict = frozenbidict(
            {lab: lab_constants[i] for i, lab in enumerate(lab_values)},
        )

        return Z3Symbols(
            time_slot_sort=time_slot_sort,
            time_slot_constants=time_slot_constants_dict,
            faculty_sort=faculty_sort,
            faculty_constants=faculty_constants_dict,
            room_sort=room_sort,
            room_constants=room_constants_dict,
            lab_sort=lab_sort,
            lab_constants=lab_constants_dict,
        )

    def __init__(self, problem: SchedulingProblem, *, solver_timeout_ms: int | None = None):
        """Build all Z3 state for a normalized problem.

        ``solver_timeout_ms`` applies to each solver check. Library callers are
        uncapped when it is omitted.
        """
        # Normalize all solver-independent configuration once. The aliases below
        # preserve the existing internal consumers until they move behind their
        # dedicated engines.
        if solver_timeout_ms is not None and (
            isinstance(solver_timeout_ms, bool) or not isinstance(solver_timeout_ms, int) or solver_timeout_ms <= 0
        ):
            raise ValueError("solver_timeout_ms must be a positive integer or None")
        self._problem = problem
        self._optimizer_flags = self._problem.optimizer_flags
        self._limit = self._problem.limit
        self._solver_timeout_ms = solver_timeout_ms
        self._enumeration_completion_reason: str | None = None
        self._full_config = self._problem.full_config

        # Initialize Z3 context
        self._ctx = z3.Context()

        policies = self._problem.faculty_policies
        self._faculty = self._problem.faculty
        self._faculty_config_paths = {name: policy.config_path for name, policy in policies.items()}
        self._course_config_paths = self._problem.course_config_paths
        self._course_faculty_origins = self._problem.course_faculty_origins
        self._faculty_maximum_credits = {name: policy.maximum_credits for name, policy in policies.items()}
        self._faculty_maximum_days = {name: policy.maximum_days for name, policy in policies.items()}
        self._faculty_minimum_credits = {name: policy.minimum_credits for name, policy in policies.items()}
        self._faculty_unique_course_limits = {name: policy.unique_course_limit for name, policy in policies.items()}
        self._faculty_course_preferences = {name: policy.course_preferences for name, policy in policies.items()}
        self._faculty_room_preferences = {name: policy.room_preferences for name, policy in policies.items()}
        self._faculty_lab_preferences = {name: policy.lab_preferences for name, policy in policies.items()}
        self._faculty_mandatory_days = {name: set(policy.mandatory_days) for name, policy in policies.items()}
        self._faculty_availability = {name: list(policy.availability) for name, policy in policies.items()}
        self._rooms = self._problem.rooms
        self._labs = self._problem.labs
        self._room_capacities = {name: policy.capacity for name, policy in self._problem.room_policies.items()}
        self._lab_capacities = {name: policy.capacity for name, policy in self._problem.lab_policies.items()}
        self._room_features = {name: policy.features for name, policy in self._problem.room_policies.items()}
        self._lab_features = {name: policy.features for name, policy in self._problem.lab_policies.items()}
        self._room_availability = {name: policy.availability for name, policy in self._problem.room_policies.items()}
        self._lab_availability = {name: policy.availability for name, policy in self._problem.lab_policies.items()}
        # Solver-owned copies carry legacy Z3 variable mirrors while the normalized
        # SchedulingProblem remains independent of Z3 state.
        self._courses = deepcopy(self._problem.courses)
        self._slots = self._problem.slots
        self._ranges = self._problem.slot_ranges
        self._compatible_slots_by_course = self._problem._compatible_slots_by_course
        self._slot_relationship_cache: dict[tuple[str, TimeSlot, TimeSlot], bool] = {}
        self._simplified_expressions: dict[z3.ExprRef, z3.BoolRef] = {}

        self._course_variables: dict[str, CourseVariables] = {}

        # Create Z3 structures
        z3_data = self._create_z3_enumsorts()
        self._z3_data = z3_data
        self._create_course_variables(z3_data)

        # Build function constraints and get the function references
        function_data = self._build_function_constraints(z3_data)

        self._diagnostic_constraints: list[DiagnosticConstraintArtifact] = []

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
            function_data.room_overlaps,
        )

        # Aggregate all constraints
        self._constraints = self._aggregate_constraints(
            function_data.constraints, faculty_constraints, course_constraints, resource_constraints
        )

        self._function_data = function_data
        self._artifacts = SolverArtifacts(
            context=self._ctx,
            symbols=z3_data,
            relations=function_data,
            constraints=tuple(self._constraints),
            diagnostic_constraints=tuple(self._diagnostic_constraints),
            course_variables=MappingProxyType(dict(self._course_variables)),
        )

    def _simplify(self, x: z3.ExprRef) -> z3.BoolRef:
        """
        Cached simplification to avoid redundant computation

        **Usage:**
        ```python
        self._simplify(z3_expr)
        ```
        """
        cached = self._simplified_expressions.get(x)
        if cached is not None:
            return cached
        simplified = cast(z3.BoolRef, z3.simplify(x, cache_all=True, local_ctx=True))
        self._simplified_expressions[x] = simplified
        return simplified

    def _cached_slot_relationship(self, fn_name: str, slot_i: TimeSlot, slot_j: TimeSlot) -> bool:
        key = (fn_name, slot_i, slot_j)
        cached = self._slot_relationship_cache.get(key)
        if cached is not None:
            return cached
        if fn_name == "overlaps":
            result = slot_i.overlaps(slot_j)
        elif fn_name == "lab_overlaps":
            result = slot_i.lab_overlaps(slot_j)
        elif fn_name == "lecture_next_to":
            result = slot_i.lecture_next_to(slot_j)
        elif fn_name == "lab_next_to":
            result = slot_i.lab_next_to(slot_j)
        else:
            raise ValueError(f"Unknown relationship function: {fn_name}")
        self._slot_relationship_cache[key] = result
        return result

    def _allowed_time_expression(self, variable: z3.ExprRef, slots: Sequence[TimeSlot]) -> z3.BoolRef:
        """Restrict a time variable to an ordered finite slot domain."""
        choices = [variable == self._z3_data.time_slot_constants[slot] for slot in slots]
        return cast(z3.BoolRef, z3.Or(choices) if choices else z3.BoolVal(False, ctx=self._ctx))

    def _or_in_context(self, expressions: Sequence[z3.BoolRef]) -> z3.BoolRef:
        """Build a disjunction whose empty value belongs to this engine's context."""
        return cast(z3.BoolRef, z3.Or(expressions) if expressions else z3.BoolVal(False, ctx=self._ctx))

    def _room_is_assigned(self, variable: z3.ExprRef) -> z3.BoolRef:
        """Return a guard that excludes the internal no-room enum value."""
        no_room = self._z3_data.room_constants.get(None)
        if no_room is None:
            return z3.BoolVal(True, ctx=self._ctx)
        return cast(z3.BoolRef, variable != no_room)

    @staticmethod
    def _times_available(times: Sequence[TimeInstance], availability: tuple[TimeInstance, ...] | None) -> bool:
        """Return whether every meeting is contained by an optional availability policy."""
        if availability is None:
            return True
        return all(
            any(
                meeting.day == window.day and window.start <= meeting.start and meeting.stop <= window.stop
                for window in availability
            )
            for meeting in times
        )

    def _lab_time_available(self, slot: TimeSlot, availability: tuple[TimeInstance, ...] | None) -> bool:
        """Return whether a slot has a lab meeting inside the supplied windows."""
        lab_time = slot.lab_time()
        return lab_time is not None and self._times_available((lab_time,), availability)

    @staticmethod
    def _room_times(slot: TimeSlot, *, include_lab: bool) -> tuple[TimeInstance, ...]:
        """Return physical meetings in a slot that occupy its lecture room."""
        times = list(slot.physical_lecture_times())
        lab = slot.lab_time()
        if include_lab and lab is not None:
            times.append(lab)
        return tuple(times)

    @staticmethod
    def _meetings_overlap(left: Sequence[TimeInstance], right: Sequence[TimeInstance]) -> bool:
        """Return whether any meetings in two occupancy sets overlap."""
        return any(TimeSlot._overlaps(first, second) for first in left for second in right)

    @staticmethod
    def _meetings_next_to(
        left: Sequence[TimeInstance],
        right: Sequence[TimeInstance],
        max_time_gap,
    ) -> bool:
        """Return whether any meetings in two occupancy sets satisfy adjacency."""
        return any(TimeSlot._diff_between_slots(first, second) <= max_time_gap for first in left for second in right)

    def _room_overlap_key(self, left: Course, right: Course) -> RoomOverlapKey:
        """Return the reusable room-occupancy relation key for a course pair."""
        return (left.reserve_room_during_lab, right.reserve_room_during_lab)

    def _z3ify_room_overlap_constraint(
        self,
        z3_data: Z3Symbols,
        name: str,
        key: RoomOverlapKey,
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        """Define one room-overlap relation for reusable occupancy semantics."""
        reserve_left, reserve_right = key
        z3fn = z3.Function(
            name,
            z3_data.time_slot_sort,
            z3_data.time_slot_sort,
            z3.BoolSort(ctx=self._ctx),
        )
        true: list[tuple[z3.ExprRef, z3.ExprRef]] = []
        false: list[tuple[z3.ExprRef, z3.ExprRef]] = []
        # Define the relation over the complete enum domain. Diagnostics may
        # intentionally relax course time-domain constraints; a partial table
        # would make those repair checks depend on unconstrained function values.
        for left_slot in z3_data.time_slot_constants:
            for right_slot in z3_data.time_slot_constants:
                constants = (
                    z3_data.time_slot_constants[left_slot],
                    z3_data.time_slot_constants[right_slot],
                )
                overlaps = (
                    left_slot is not None
                    and right_slot is not None
                    and self._meetings_overlap(
                        self._room_times(left_slot, include_lab=reserve_left),
                        self._room_times(right_slot, include_lab=reserve_right),
                    )
                )
                (true if overlaps else false).append(constants)

        constraints: list[z3.BoolRef] = []
        if true:
            constraints.append(cast(z3.BoolRef, z3.And([z3fn(left, right) for left, right in true])))
        if false:
            constraints.append(cast(z3.BoolRef, z3.And([z3.Not(z3fn(left, right)) for left, right in false])))
        return z3fn, constraints

    def _z3ify_room_adjacency_constraint(
        self,
        z3_data: Z3Symbols,
        name: str,
        key: RoomOverlapKey,
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        """Define one room-occupancy adjacency relation over the complete slot enum."""
        reserve_left, reserve_right = key
        z3fn = z3.Function(
            name,
            z3_data.time_slot_sort,
            z3_data.time_slot_sort,
            z3.BoolSort(ctx=self._ctx),
        )
        true: list[tuple[z3.ExprRef, z3.ExprRef]] = []
        false: list[tuple[z3.ExprRef, z3.ExprRef]] = []
        for left_slot in z3_data.time_slot_constants:
            for right_slot in z3_data.time_slot_constants:
                constants = (
                    z3_data.time_slot_constants[left_slot],
                    z3_data.time_slot_constants[right_slot],
                )
                adjacent = (
                    left_slot is not None
                    and right_slot is not None
                    and self._meetings_next_to(
                        self._room_times(left_slot, include_lab=reserve_left),
                        self._room_times(right_slot, include_lab=reserve_right),
                        left_slot.max_time_gap,
                    )
                )
                (true if adjacent else false).append(constants)
        constraints: list[z3.BoolRef] = []
        if true:
            constraints.append(cast(z3.BoolRef, z3.And([z3fn(left, right) for left, right in true])))
        if false:
            constraints.append(cast(z3.BoolRef, z3.And([z3.Not(z3fn(left, right)) for left, right in false])))
        return z3fn, constraints

    def _z3ify_time_constraint(
        self, z3_data: Z3Symbols, name: str, *, ctx: z3.Context | None = None
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        z3fn = z3.Function(
            name,
            z3_data.time_slot_sort,
            z3_data.time_slot_sort,
            z3.BoolSort(ctx=ctx),
        )

        true: list[tuple[z3.BoolRef, z3.BoolRef]] = []
        false: list[tuple[z3.BoolRef, z3.BoolRef]] = []

        for slot_i, slot_j in itertools.combinations_with_replacement(z3_data.time_slot_constants, 2):
            c_i = cast(z3.BoolRef, z3_data.time_slot_constants[slot_i])
            c_j = cast(z3.BoolRef, z3_data.time_slot_constants[slot_j])
            if slot_i is not None and slot_j is not None and self._cached_slot_relationship(name, slot_i, slot_j):
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
        z3_data: Z3Symbols,
        name: str,
        fn: Callable[[TimeSlot], bool],
        *,
        ctx: z3.Context | None = None,
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        z3fn = z3.Function(name, z3_data.time_slot_sort, z3.BoolSort(ctx=ctx))

        true: list[z3.BoolRef] = []
        false: list[z3.BoolRef] = []
        for slot in z3_data.time_slot_constants:
            c = cast(z3.BoolRef, z3_data.time_slot_constants[slot])
            if slot is not None and fn(slot):
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
        self, z3_data: Z3Symbols, name: str, *, ctx: z3.Context | None = None
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
            for slot in z3_data.time_slot_constants:
                slot_constant = cast(z3.BoolRef, z3_data.time_slot_constants[slot])
                if slot is not None and slot.in_time_ranges(faculty_times):
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

    def _build_function_constraints(self, z3_data: Z3Symbols) -> RelationTables:
        """
        Create Z3 function definitions and their constraints.

        **Usage:**
        ```python
        self._build_function_constraints(z3_data)
        ```

        **Args:**
        - z3_data: `Z3Symbols` object containing the Z3 sorts and constants

        **Returns:**
        - `RelationTables` object containing the Z3 function definitions and their constraints
        """
        # abstract function constraints
        overlaps, overlaps_C = self._z3ify_time_constraint(z3_data, "overlaps", ctx=self._ctx)
        lab_overlaps, lab_overlaps_C = self._z3ify_time_constraint(z3_data, "lab_overlaps", ctx=self._ctx)
        lecture_next_to, lecture_next_to_C = self._z3ify_time_constraint(z3_data, "lecture_next_to", ctx=self._ctx)
        faculty_available, faculty_available_C = self._z3ify_faculty_time_constraint(
            z3_data, "faculty_available", ctx=self._ctx
        )
        lab_next_to, lab_next_to_C = self._z3ify_time_constraint(z3_data, "lab_next_to", ctx=self._ctx)

        room_overlap_keys: list[RoomOverlapKey] = []
        for left, right in itertools.combinations(self._courses, 2):
            if set(left.rooms) & set(right.rooms):
                key = self._room_overlap_key(left, right)
                if key not in room_overlap_keys:
                    room_overlap_keys.append(key)
        room_overlaps: dict[RoomOverlapKey, z3.FuncDeclRef] = {}
        room_next_to: dict[RoomOverlapKey, z3.FuncDeclRef] = {}
        room_overlap_constraints: list[z3.BoolRef] = []
        for index, key in enumerate(room_overlap_keys):
            relation, constraints = self._z3ify_room_overlap_constraint(
                z3_data,
                f"room_overlaps_{index}",
                key,
            )
            room_overlaps[key] = relation
            room_overlap_constraints.extend(constraints)
            adjacency, constraints = self._z3ify_room_adjacency_constraint(
                z3_data,
                f"room_next_to_{index}",
                key,
            )
            room_next_to[key] = adjacency
            room_overlap_constraints.extend(constraints)

        function_constraints: list[z3.BoolRef] = []
        function_constraints.extend(overlaps_C)
        function_constraints.extend(lab_overlaps_C)
        function_constraints.extend(lecture_next_to_C)
        function_constraints.extend(lab_next_to_C)
        function_constraints.extend(faculty_available_C)
        function_constraints.extend(room_overlap_constraints)

        return RelationTables(
            constraints=tuple(function_constraints),
            overlaps=overlaps,
            lab_overlaps=lab_overlaps,
            lecture_next_to=lecture_next_to,
            faculty_available=faculty_available,
            lab_next_to=lab_next_to,
            room_overlaps=MappingProxyType(room_overlaps),
            room_next_to=MappingProxyType(room_next_to),
        )

    def _build_faculty_constraints(self, z3_data: Z3Symbols) -> list[z3.BoolRef]:
        """
        Create constraints for faculty credit limits and unique course limits.

        **Usage:**
        ```python
        self._build_faculty_constraints(z3_data)
        ```

        **Args:**
        - z3_data: `Z3Symbols` object containing the Z3 sorts and constants

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
            credit_sum = z3.Sum(
                [z3.If(self._variables(c).faculty == faculty_constant, c.credits, 0) for c in faculty_courses]
            )
            # Ensure that every faculty is assigned between their min and max,
            # including faculty with no eligible courses.
            credit_constraint = cast(z3.BoolRef, z3.And(credit_sum >= min_credits, credit_sum <= max_credits))
            faculty_constraints.append(credit_constraint)
            self._diagnostic_constraints.append(
                DiagnosticConstraintArtifact(
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
                            z3.Or([self._variables(c).faculty == faculty_constant for c in course_group]),
                        )
                    )
                limit = self._simplify(z3.Sum([z3.If(tc, 1, 0) for tc in teaches_course]) <= unique_limit)
                faculty_constraints.append(limit)
                self._diagnostic_constraints.append(
                    DiagnosticConstraintArtifact(
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
                        time_variables = [self._variables(course).time]
                        slot_matches = [
                            time_variable == slot_const
                            for time_variable in time_variables
                            for slot_const in slot_constants
                        ]
                        if slot_matches:
                            course_day_assignments.append(
                                self._simplify(
                                    z3.And(
                                        self._variables(course).faculty == faculty_constant,
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
                DiagnosticConstraintArtifact(
                    max_days_constraint,
                    f"Faculty {faculty} may teach at most {max_days} days",
                    kind="faculty_maximum_days",
                    subjects=(faculty,),
                )
            )

            # Mandatory-day constraints
            for mandatory_day in sorted(mandatory_days):
                indicator = day_indicator_map.get(mandatory_day, z3.BoolVal(False, ctx=self._ctx))
                faculty_constraints.append(self._simplify(indicator))
                self._diagnostic_constraints.append(
                    DiagnosticConstraintArtifact(
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
        z3_data: Z3Symbols,
    ) -> list[z3.BoolRef]:
        """Create assignment-domain, compatibility, and availability constraints."""
        course_constraints: list[z3.BoolRef] = []
        for c in self._courses:
            course_constraint_list: list[z3.BoolRef] = []
            compatible_slots = self._problem.compatible_slots(c)
            time_constraint = self._allowed_time_expression(self._variables(c).time, compatible_slots)
            course_constraint_list.append(time_constraint)
            self._diagnostic_constraints.append(
                DiagnosticConstraintArtifact(
                    time_constraint,
                    f"Course {c} must use a compatible {c.credits}-credit {c.modality} meeting pattern",
                    kind="course_time_pattern",
                    subjects=(str(c),),
                )
            )

            for d in self._courses:
                if d != c and d.course_id in c.conflicts:
                    conflict = cast(z3.BoolRef, z3.Not(overlaps(self._variables(c).time, self._variables(d).time)))
                    course_constraint_list.append(conflict)
                    self._diagnostic_constraints.append(
                        DiagnosticConstraintArtifact(
                            conflict,
                            f"Course {c} must not overlap course {d}",
                            kind="course_conflict",
                            subjects=(str(c), str(d)),
                        )
                    )

            availability_constraint = cast(
                z3.BoolRef, faculty_available(self._variables(c).faculty, self._variables(c).time)
            )
            course_constraint_list.append(availability_constraint)
            self._diagnostic_constraints.append(
                DiagnosticConstraintArtifact(
                    availability_constraint,
                    f"Course {c} must use an available faculty time",
                    kind="faculty_availability",
                    subjects=(str(c),),
                )
            )

            if c.labs:
                lab_constraint = cast(
                    z3.BoolRef,
                    z3.Or([self._variables(c).lab == z3_data.lab_constants[lab] for lab in c.labs]),
                )
                course_constraint_list.append(lab_constraint)
                self._diagnostic_constraints.append(
                    DiagnosticConstraintArtifact(
                        lab_constraint,
                        f"Course {c} must use one of its allowed labs",
                        kind="course_lab_eligibility",
                        subjects=(str(c), *c.labs),
                    )
                )

                capacity_constraint = self._or_in_context(
                    [
                        self._variables(c).lab == z3_data.lab_constants[lab]
                        for lab in c.labs
                        if self._lab_capacities[lab] >= c.capacity
                    ]
                )
                course_constraint_list.append(capacity_constraint)
                self._diagnostic_constraints.append(
                    DiagnosticConstraintArtifact(
                        capacity_constraint,
                        f"Course {c} requires a lab capacity of at least {c.capacity}",
                        kind="course_lab_capacity",
                        subjects=(str(c),),
                    )
                )

                if c.required_lab_features:
                    feature_constraint = self._or_in_context(
                        [
                            self._variables(c).lab == z3_data.lab_constants[lab]
                            for lab in c.labs
                            if c.required_lab_features <= self._lab_features[lab]
                        ]
                    )
                    course_constraint_list.append(feature_constraint)
                    self._diagnostic_constraints.append(
                        DiagnosticConstraintArtifact(
                            feature_constraint,
                            f"Course {c} requires lab features {sorted(c.required_lab_features)}",
                            kind="course_lab_features",
                            subjects=(str(c),),
                        )
                    )

                if any(self._lab_availability[lab] is not None for lab in c.labs):
                    lab_availability_parts = []
                    for lab in c.labs:
                        available_slots = tuple(
                            slot for slot in self._slots if self._lab_time_available(slot, self._lab_availability[lab])
                        )
                        lab_availability_parts.append(
                            z3.Implies(
                                self._variables(c).lab == z3_data.lab_constants[lab],
                                self._allowed_time_expression(self._variables(c).time, available_slots),
                            )
                        )
                    lab_availability_constraint = cast(z3.BoolRef, z3.And(lab_availability_parts))
                    course_constraint_list.append(lab_availability_constraint)
                    self._diagnostic_constraints.append(
                        DiagnosticConstraintArtifact(
                            lab_availability_constraint,
                            f"Course {c} must fit the selected lab's availability",
                            kind="course_lab_availability",
                            subjects=(str(c),),
                        )
                    )
            else:
                course_constraint_list.append(cast(z3.BoolRef, self._variables(c).lab == z3_data.lab_constants[None]))

            room_required_slots = tuple(
                slot
                for slot in self._slots
                if self._problem._slot_requires_room(
                    slot,
                    reserve_room_during_lab=c.reserve_room_during_lab,
                )
            )
            room_required = self._allowed_time_expression(self._variables(c).time, room_required_slots)
            allowed_rooms = self._or_in_context(
                [self._variables(c).room == z3_data.room_constants[room] for room in c.rooms]
            )
            no_room = z3_data.room_constants.get(None)
            if no_room is None:
                room_constraint = allowed_rooms
            else:
                room_constraint = cast(
                    z3.BoolRef,
                    z3.And(
                        z3.Implies(room_required, allowed_rooms),
                        z3.Implies(z3.Not(room_required), self._variables(c).room == no_room),
                    ),
                )
            course_constraint_list.append(room_constraint)
            self._diagnostic_constraints.append(
                DiagnosticConstraintArtifact(
                    room_constraint,
                    f"Course {c} must use an allowed room exactly when its selected pattern requires one",
                    kind="course_room_eligibility",
                    subjects=(str(c), *c.rooms),
                )
            )

            if c.rooms:
                room_capacity_constraint = cast(
                    z3.BoolRef,
                    z3.Implies(
                        room_required,
                        self._or_in_context(
                            [
                                self._variables(c).room == z3_data.room_constants[room]
                                for room in c.rooms
                                if self._room_capacities[room] >= c.capacity
                            ]
                        ),
                    ),
                )
                course_constraint_list.append(room_capacity_constraint)
                self._diagnostic_constraints.append(
                    DiagnosticConstraintArtifact(
                        room_capacity_constraint,
                        f"Course {c} requires a room with capacity of at least {c.capacity}",
                        kind="course_room_capacity",
                        subjects=(str(c),),
                    )
                )

                if c.required_room_features:
                    feature_constraint = cast(
                        z3.BoolRef,
                        z3.Implies(
                            room_required,
                            self._or_in_context(
                                [
                                    self._variables(c).room == z3_data.room_constants[room]
                                    for room in c.rooms
                                    if c.required_room_features <= self._room_features[room]
                                ]
                            ),
                        ),
                    )
                    course_constraint_list.append(feature_constraint)
                    self._diagnostic_constraints.append(
                        DiagnosticConstraintArtifact(
                            feature_constraint,
                            f"Course {c} requires room features {sorted(c.required_room_features)}",
                            kind="course_room_features",
                            subjects=(str(c),),
                        )
                    )

                if any(self._room_availability[room] is not None for room in c.rooms):
                    room_availability_parts = []
                    for room in c.rooms:
                        availability = self._room_availability[room]
                        main_slots = tuple(
                            slot
                            for slot in self._slots
                            if self._times_available(
                                self._room_times(slot, include_lab=c.reserve_room_during_lab), availability
                            )
                        )
                        room_availability_parts.append(
                            z3.Implies(
                                self._variables(c).room == z3_data.room_constants[room],
                                self._allowed_time_expression(self._variables(c).time, main_slots),
                            )
                        )
                    room_availability_constraint = cast(z3.BoolRef, z3.And(room_availability_parts))
                    course_constraint_list.append(room_availability_constraint)
                    self._diagnostic_constraints.append(
                        DiagnosticConstraintArtifact(
                            room_availability_constraint,
                            f"Course {c} must fit the selected room's availability",
                            kind="course_room_availability",
                            subjects=(str(c),),
                        )
                    )

            faculty_constraint = cast(
                z3.BoolRef,
                z3.Or([self._variables(c).faculty == z3_data.faculty_constants[faculty] for faculty in c.faculties]),
            )
            course_constraint_list.append(faculty_constraint)
            self._diagnostic_constraints.append(
                DiagnosticConstraintArtifact(
                    faculty_constraint,
                    f"Course {c} must use one of its eligible faculty",
                    kind="course_faculty_eligibility",
                    subjects=(str(c), *c.faculties),
                )
            )

            course_constraints.append(cast(z3.BoolRef, z3.And(course_constraint_list)))

        return course_constraints

    def _build_resource_constraints(
        self,
        overlaps: z3.FuncDeclRef,
        lab_overlaps: z3.FuncDeclRef,
        lecture_next_to: z3.FuncDeclRef,
        lab_next_to: z3.FuncDeclRef,
        room_overlaps: Mapping[RoomOverlapKey, z3.FuncDeclRef],
    ) -> list[z3.BoolRef]:
        """
        Create resource sharing and faculty scheduling constraints.

        **Usage:**
        ```python
        self._build_resource_constraints(overlaps, lab_overlaps, lecture_next_to, lab_next_to, room_overlaps)
        ```

        **Args:**
        - overlaps: `z3.FuncDeclRef` function for checking time overlaps
        - lab_overlaps: `z3.FuncDeclRef` function for checking lab overlaps
        - lecture_next_to: `z3.FuncDeclRef` function for checking lecture next to each other
        - lab_next_to: `z3.FuncDeclRef` function for checking lab next to each other
        - room_overlaps: total room-occupancy relations keyed by reservation policy

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
                room_overlap = room_overlaps[self._room_overlap_key(i, j)]
                room_non_overlap = z3.Not(room_overlap(self._variables(i).time, self._variables(j).time))
                shared_room_constraint = cast(
                    z3.BoolRef,
                    z3.Implies(
                        z3.And(
                            self._room_is_assigned(self._variables(i).room),
                            self._room_is_assigned(self._variables(j).room),
                            self._variables(i).room == self._variables(j).room,
                        ),
                        room_non_overlap,
                    ),
                )
                resource.append(shared_room_constraint)
                self._diagnostic_constraints.append(
                    DiagnosticConstraintArtifact(
                        shared_room_constraint,
                        f"Courses {i} and {j} cannot overlap when sharing a room",
                        kind="shared_room_overlap",
                        subjects=(str(i), str(j)),
                    )
                )
                if i.course_id == j.course_id:
                    # when a faculty teaches two sections of the same course,
                    # their physical room assignments must match. A section whose
                    # selected pattern is roomless has no room to coordinate.
                    same_room_constraint = cast(
                        z3.BoolRef,
                        z3.Implies(
                            z3.And(
                                self._room_is_assigned(self._variables(i).room),
                                self._room_is_assigned(self._variables(j).room),
                            ),
                            self._variables(i).room == self._variables(j).room,
                        ),
                    )
                    constraint_parts.append(same_room_constraint)
                    shared_faculty_parts.append(
                        (same_room_constraint, "same_course_room", f"Sections {i} and {j} must use the same room")
                    )

            # Enforce same lab usage when both courses have labs and can use the same labs
            if set(i.labs) & set(j.labs):
                shared_lab_constraint = cast(
                    z3.BoolRef,
                    z3.Implies(
                        self._variables(i).lab == self._variables(j).lab,
                        z3.Not(lab_overlaps(self._variables(i).time, self._variables(j).time)),
                    ),
                )
                resource.append(shared_lab_constraint)
                self._diagnostic_constraints.append(
                    DiagnosticConstraintArtifact(
                        shared_lab_constraint,
                        f"Courses {i} and {j} cannot overlap when sharing a lab",
                        kind="shared_lab_overlap",
                        subjects=(str(i), str(j)),
                    )
                )
                if i.course_id == j.course_id:
                    # when a faculty teaches two sections of the same course,
                    # they must use the same lab
                    same_lab_constraint = cast(z3.BoolRef, self._variables(i).lab == self._variables(j).lab)
                    constraint_parts.append(same_lab_constraint)
                    shared_faculty_parts.append(
                        (same_lab_constraint, "same_course_lab", f"Sections {i} and {j} must use the same lab")
                    )

            # Prevent time overlap for courses taught by same faculty
            shared_faculty_overlap = cast(
                z3.BoolRef, z3.Not(overlaps(self._variables(i).time, self._variables(j).time))
            )
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
                lecture_adjacency = cast(z3.BoolRef, lecture_next_to(self._variables(i).time, self._variables(j).time))
                constraint_parts.append(lecture_adjacency)
                shared_faculty_parts.append(
                    (lecture_adjacency, "same_course_lecture_adjacency", f"Sections {i} and {j} must be adjacent")
                )
                # Lab adjacency only applies when both sections contain lab meetings.
                if i.labs and j.labs:
                    lab_adjacency = cast(z3.BoolRef, lab_next_to(self._variables(i).time, self._variables(j).time))
                    constraint_parts.append(lab_adjacency)
                    shared_faculty_parts.append(
                        (lab_adjacency, "same_course_lab_adjacency", f"Sections {i} and {j} must have adjacent labs")
                    )
            else:
                # when a faculty teaches two sections of different courses,
                # they must not be next to each other
                lecture_separation = cast(
                    z3.BoolRef, z3.Not(lecture_next_to(self._variables(i).time, self._variables(j).time))
                )
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
                    lab_separation = cast(
                        z3.BoolRef, z3.Not(lab_next_to(self._variables(i).time, self._variables(j).time))
                    )
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
                section_overlap_constraint = cast(
                    z3.BoolRef,
                    z3.Not(overlaps(self._variables(i).time, self._variables(j).time)),
                )
                resource_constraints.append(section_overlap_constraint)
                self._diagnostic_constraints.append(
                    DiagnosticConstraintArtifact(
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
                z3.Implies(self._variables(i).faculty == self._variables(j).faculty, z3.And(constraint_parts)),
            )
            resource_constraints.append(shared_faculty_constraint)
            for constraint, kind, message in shared_faculty_parts:
                self._diagnostic_constraints.append(
                    DiagnosticConstraintArtifact(
                        cast(
                            z3.BoolRef, z3.Implies(self._variables(i).faculty == self._variables(j).faculty, constraint)
                        ),
                        message,
                        kind=kind,
                        subjects=(str(i), str(j)),
                    )
                )

        return resource_constraints

    def _aggregate_constraints(
        self,
        function_constraints: Sequence[z3.BoolRef],
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
            slot = model.eval(self._variables(course).time)
            time = self._z3_data.time_slot_constants.inverse[slot]
            faculty = self._z3_data.faculty_constants.inverse.get(model.eval(self._variables(course).faculty), None)
            room = self._z3_data.room_constants.inverse.get(model.eval(self._variables(course).room), None)
            lab = self._z3_data.lab_constants.inverse.get(model.eval(self._variables(course).lab), None)

            if time is None or faculty is None:
                raise ValueError(f"Invalid model: {model}")

            # Create CourseInstance
            decoded_course = copy(course)
            decoded_course.labs = list(course.labs)
            decoded_course.rooms = list(course.rooms)
            decoded_course.conflicts = list(course.conflicts)
            decoded_course.faculties = list(course.faculties)
            course_instance = CourseInstance(
                course=decoded_course,
                time=time.model_copy(deep=True),
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
        assignment_equalities = []
        for course in self._courses:
            variables = self._variables(course)
            assignment_equalities.extend(
                variable == m.eval(variable, model_completion=True)
                for variable in (variables.time, variables.faculty, variables.room, variables.lab)
            )
        if assignment_equalities:
            logger.debug("Blocking the complete emitted schedule assignment")
            s.add(z3.Not(z3.And(assignment_equalities)))

    def get_models(self) -> Generator[list[CourseInstance], None, None]:
        """Generate optimized schedules lazily in stable model-blocking order.

        Args:
            None.

        Returns:
            A generator of complete decoded course-assignment lists, stopping at the
            configured limit, solver exhaustion, or an unknown solver result.

        Raises:
            z3.Z3Exception: If solver configuration, optimization, or evaluation fails.

        Behavior:
            Creates a fresh optimizer, applies the configured timeout and hard rules,
            registers enabled objectives in their established order, decodes each
            optimal model, yields it, and blocks the emitted arrangement before the
            next check. Unknown and unsatisfiable results terminate enumeration.
        """
        self._enumeration_completion_reason = None
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
                        # Preference values use the configured 0-10 scale; zero contributes no objective points.
                        preference_value = preferences[course.course_id]
                        if preference_value == 0:
                            continue
                        term = z3.If(
                            self._variables(course).faculty == faculty_constant,
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
                                    self._variables(course).faculty == faculty_constant,
                                    self._variables(course).room == room_constant,
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
                                    self._variables(course).faculty == faculty_constant,
                                    self._variables(course).lab == self._z3_data.lab_constants[lab],
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
                        z3.And(
                            self._variables(i).faculty == self._variables(j).faculty,
                            self._room_is_assigned(self._variables(i).room),
                            self._room_is_assigned(self._variables(j).room),
                            self._variables(i).room == self._variables(j).room,
                        ),
                        1,
                        0,
                    )
                )
                if i.course_id != j.course_id:
                    packing_rooms.append(
                        z3.If(
                            z3.And(
                                self._room_is_assigned(self._variables(i).room),
                                self._room_is_assigned(self._variables(j).room),
                                self._variables(i).room == self._variables(j).room,
                                self._function_data.room_next_to[self._room_overlap_key(i, j)](
                                    self._variables(i).time,
                                    self._variables(j).time,
                                ),
                            ),
                            1,
                            0,
                        )
                    )
            if set(i.labs) & set(j.labs):
                same_labs.append(
                    z3.If(
                        z3.And(
                            self._variables(i).faculty == self._variables(j).faculty,
                            self._variables(i).lab == self._variables(j).lab,
                        ),
                        1,
                        0,
                    )
                )
                if i.course_id != j.course_id:
                    packing_labs.append(
                        z3.If(
                            z3.And(
                                self._variables(i).lab == self._variables(j).lab,
                                self._function_data.lab_next_to(self._variables(i).time, self._variables(j).time),
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
            result = s.check()
            if result == z3.sat:
                generation_time = time.time() - start_time
                logger.debug(f"Schedule {i + 1} generation took {generation_time:.2f}s")
                yield self._get_schedule(s.model())
                if i < self._limit - 1:
                    self._update(s)
                    i += 1
            else:
                if result == z3.unsat:
                    self._enumeration_completion_reason = "solution_space_exhausted"
                else:
                    reason = s.reason_unknown().lower()
                    self._enumeration_completion_reason = (
                        "solver_timeout" if "timeout" in reason or "canceled" in reason else "solver_unknown"
                    )
                generation_time = time.time() - start_time
                if i == 0:
                    logger.error("No solution found")
                else:
                    logger.warning("No more solutions found")
                logger.debug(f"Final check took {generation_time:.2f} seconds")
                break
