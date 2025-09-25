import itertools
import json
import time
from collections import defaultdict
from collections.abc import Callable, Generator
from dataclasses import dataclass
from functools import cache
from typing import cast

import z3  # type: ignore
from bidict import frozenbidict
from pydantic import BaseModel

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


def load_config_from_file[T: BaseModel](
    config_cls: type[T],
    filename: str,
) -> T:
    """
    Load scheduler configuration from a JSON file.

    **Args:**
    - config_cls: The class of the configuration to load
    - filename: The name of the file to load the configuration from

    **Returns:**
    The loaded configuration

    **Example:**
    >>> load_config_from_file(CombinedConfig, "config.json")
    """
    with open(filename, encoding="utf-8") as f:
        data = json.load(f)
    return config_cls(**data)


def get_faculty_availability(
    faculty_config: FacultyConfig,
) -> list[TimeInstance]:
    """
    Calculate the availability of a faculty as a list of `TimeInstance` objects.

    **Args:**
    - faculty_config: The configuration of the faculty

    **Returns:**
    The availability of the faculty as a list of `TimeInstance` objects
    """
    days: list[Day] = [Day.MON, Day.TUE, Day.WED, Day.THU, Day.FRI]
    result: list[TimeInstance] = list()
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
    """Structured data for function constraints and their references."""

    constraints: list[z3.BoolRef]
    overlaps: z3.FuncDeclRef
    lab_overlaps: z3.FuncDeclRef
    lecture_next_to: z3.FuncDeclRef
    faculty_available: z3.FuncDeclRef
    lab_next_to: z3.FuncDeclRef


@dataclass
class _Z3SortsAndConstants:
    """Structured data for Z3 sorts and their corresponding constant mappings."""

    time_slot_sort: z3.SortRef
    time_slot_constants: frozenbidict[TimeSlot, z3.ExprRef]
    faculty_sort: z3.SortRef
    faculty_constants: frozenbidict[str, z3.ExprRef]
    room_sort: z3.SortRef
    room_constants: frozenbidict[str, z3.ExprRef]
    lab_sort: z3.SortRef
    lab_constants: frozenbidict[str, z3.ExprRef]


class Scheduler:
    """
    Scheduler class for generating schedules.
    """

    def _initialize_faculty_data(self, config) -> None:
        """Initialize faculty-related data structures and preferences."""
        for faculty_data in config.faculty:
            faculty_name = faculty_data.name
            self._faculty.add(faculty_name)
            self._faculty_maximum_credits[faculty_name] = faculty_data.maximum_credits
            self._faculty_minimum_credits[faculty_name] = faculty_data.minimum_credits
            self._faculty_unique_course_limits[faculty_name] = faculty_data.unique_course_limit
            self._faculty_course_preferences[faculty_name] = faculty_data.course_preferences
            self._faculty_room_preferences[faculty_name] = faculty_data.room_preferences
            self._faculty_lab_preferences[faculty_name] = faculty_data.lab_preferences
            self._faculty_availability[faculty_name] = get_faculty_availability(faculty_data)

    def _initialize_courses(self, config) -> tuple[list[Course], set[int]]:
        """Initialize courses and return them along with required credits."""
        courses: list[Course] = []
        required_credits = set()
        course_counts: dict[str, int] = defaultdict(int)

        for c in config.courses:
            course_counts[c.course_id] += 1
            required_credits.add(c.credits)
            course_faculty = c.faculty
            if not course_faculty:
                for faculty_data in config.faculty:
                    if c.course_id in faculty_data.course_preferences:
                        course_faculty.append(faculty_data.name)

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

        return courses, required_credits

    def _initialize_time_slots(self, time_slot_config, required_credits: set[int]) -> None:
        """Initialize time slots and create ranges for different credit levels."""
        self._time_slot_generator = TimeSlotGenerator(time_slot_config)
        self._ranges: dict[int, tuple[int, int]] = dict()
        self._slots: list[TimeSlot] = list()

        for creds in sorted(required_credits):
            low = len(self._slots)
            self._slots.extend(self._time_slot_generator.time_slots(creds))
            self._ranges[creds] = (low, len(self._slots) - 1)

    def _create_z3_enumsorts(self) -> _Z3SortsAndConstants:
        """Create Z3 EnumSorts for time slots, faculty, rooms, and labs."""

        def sanitize(name):
            return name.replace(" ", "_")

        # Create TimeSlot EnumSort
        time_slot_names = [sanitize(str(slot)) for slot in self._slots]
        time_slot_sort, time_slot_constants = z3.EnumSort("TimeSlot", time_slot_names, ctx=self._ctx)
        time_slot_constants_dict = frozenbidict(
            {time_slot: time_slot_constants[i] for i, time_slot in enumerate(self._slots)}
        )

        # Create Faculty EnumSort
        faculty_names = [sanitize(faculty) for faculty in self._faculty]
        faculty_sort, faculty_constants = z3.EnumSort("Faculty", faculty_names, ctx=self._ctx)
        faculty_constants_dict = frozenbidict(
            {faculty: faculty_constants[i] for i, faculty in enumerate(self._faculty)},
        )

        # Create Room EnumSort
        room_names = [sanitize(room) for room in self._rooms]
        room_sort, room_constants = z3.EnumSort("Room", room_names, ctx=self._ctx)
        room_constants_dict = frozenbidict(
            {room: room_constants[i] for i, room in enumerate(self._rooms)},
        )

        # Create Lab EnumSort
        lab_names = [sanitize(lab) for lab in self._labs]
        lab_sort, lab_constants = z3.EnumSort("Lab", lab_names, ctx=self._ctx)
        lab_constants_dict = frozenbidict(
            {lab: lab_constants[i] for i, lab in enumerate(self._labs)},
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
        """Create Z3 variables for each course."""
        for course in self._courses:
            course.time = z3.Const(f"{str(course)}_time", z3_data.time_slot_sort)
            course.faculty = z3.Const(f"{str(course)}_faculty", z3_data.faculty_sort)
            course.room = z3.Const(f"{str(course)}_room", z3_data.room_sort)
            course.lab = z3.Const(f"{str(course)}_lab", z3_data.lab_sort)

    def __init__(self, full_config: CombinedConfig):
        """
        Initializes the scheduler with all the necessary constraints and variables.

        **Args:**
        - full_config: `CombinedConfig` object containing all the configuration
                       settings including the scheduler config, time slot config,
                       limit, and optimizer flags

        **Raises:**
        - ValueError: If the optimizer flags are invalid
        """
        # Extract configuration
        config = full_config.config
        time_slot_config = full_config.time_slot_config
        self._optimizer_flags = full_config.optimizer_flags
        self._limit = full_config.limit

        # Initialize Z3 context
        self._ctx = z3.Context()

        # Initialize data structures
        self._faculty: set[str] = set()
        self._faculty_maximum_credits: dict[str, int] = dict()
        self._faculty_minimum_credits: dict[str, int] = dict()
        self._faculty_unique_course_limits: dict[str, int] = dict()
        self._faculty_course_preferences: dict[str, dict[str, int]] = dict()
        self._faculty_room_preferences: dict[str, dict[str, int]] = dict()
        self._faculty_lab_preferences: dict[str, dict[str, int]] = dict()
        self._faculty_availability: dict[str, list[TimeInstance]] = dict()
        self._initialize_faculty_data(config)

        # Initialize courses and time slots
        self._rooms = set(config.rooms)
        self._labs = set(config.labs)
        self._courses, required_credits = self._initialize_courses(config)
        self._initialize_time_slots(time_slot_config, required_credits)

        # Create Z3 structures
        z3_data = self._create_z3_enumsorts()
        self._create_course_variables(z3_data)

        # Build function constraints and get the function references
        function_data = self._build_function_constraints(z3_data)

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

    @cache
    def _simplify(self, x: z3.ExprRef) -> z3.BoolRef:
        """Cached simplification to avoid redundant computation"""
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
            c_i = z3_data.time_slot_constants[slot_i]
            c_j = z3_data.time_slot_constants[slot_j]
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
            c = z3_data.time_slot_constants[slot]
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
            faculty_constant = z3_data.faculty_constants[faculty]
            for slot in self._slots:
                slot_constant = z3_data.time_slot_constants[slot]
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

        **Args:**
        - z3_data: `_Z3SortsAndConstants` object containing the Z3 sorts and constants

        **Returns:**
        - `list[z3.BoolRef]` containing the faculty constraints
        """
        # Pre-compute course groupings to reduce repeated calculations
        faculty_course_map: defaultdict[str, list[Course]] = defaultdict(list)
        for c in self._courses:
            for faculty in c.faculties:
                faculty_course_map[faculty].append(c)

        # Add faculty credit and unique course limits - batch generation
        faculty_constraints: list[z3.BoolRef] = []
        for faculty in self._faculty:
            faculty_courses = faculty_course_map.get(faculty, [])
            faculty_constant = z3_data.faculty_constants[faculty]
            if faculty_courses:
                min_credits = self._faculty_minimum_credits[faculty]
                max_credits = self._faculty_maximum_credits[faculty]
                credit_sum = z3.Sum([z3.If(c.faculty == faculty_constant, c.credits, 0) for c in faculty_courses])
                # ensure that each faculty is assigned between min and max credits
                faculty_constraints.append(
                    cast(
                        z3.BoolRef,
                        z3.And(credit_sum >= min_credits, credit_sum <= max_credits),
                    )
                )

                # Unique course limit constraint - only generate if needed
                unique_limit = self._faculty_unique_course_limits[faculty]

                # Group courses by their unique identifier (subject + number)
                unique_courses: defaultdict[str, list[Course]] = defaultdict(list)
                for c in faculty_courses:
                    unique_courses[c.course_id].append(c)

                # Only create constraint if there are multiple unique courses
                if len(unique_courses) > unique_limit:
                    teaches_course: list[z3.BoolRef] = []
                    for course_group in unique_courses.values():
                        teaches_course.append(
                            cast(
                                z3.BoolRef,
                                z3.Or([c.faculty == faculty_constant for c in course_group]),
                            )
                        )
                    # ensure that each faculty is assigned <= unique course limit
                    limit = cast(
                        z3.BoolRef,
                        self._simplify(z3.Sum([z3.If(tc, 1, 0) for tc in teaches_course]) <= unique_limit),
                    )
                    faculty_constraints.append(limit)

        return faculty_constraints

    def _build_course_constraints(
        self,
        overlaps: z3.FuncDeclRef,
        faculty_available: z3.FuncDeclRef,
        z3_data: _Z3SortsAndConstants,
    ) -> list[z3.BoolRef]:
        """
        Create individual course constraints.

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
                    conflict_constraints.append(cast(z3.BoolRef, z3.Not(overlaps(c.time, d.time))))

            # faculty availability constraint
            course_constraint_list: list[z3.BoolRef] = [
                cast(z3.BoolRef, faculty_available(c.faculty, c.time)),
            ]

            # Get valid time slots for this credit level
            start, stop = self._ranges[c.credits]
            valid_time_slots = {i for i, _ in enumerate(self._slots) if start <= i <= stop}
            if valid_time_slots:
                # Constrain time to valid slots for this credit level
                course_constraint_list.append(
                    cast(
                        z3.BoolRef,
                        z3.Or([c.time == z3_data.time_slot_constants[self._slots[i]] for i in valid_time_slots]),
                    )
                )

            if c.labs:
                # we must assign to a lab when we have options
                course_constraint_list.append(
                    cast(
                        z3.BoolRef,
                        z3.Or([c.lab == z3_data.lab_constants[lab] for lab in self._labs if lab in c.labs]),
                    )
                )
            if c.rooms:
                # we must assign to a room when we have options
                course_constraint_list.append(
                    cast(
                        z3.BoolRef,
                        z3.Or([c.room == z3_data.room_constants[room] for room in self._rooms if room in c.rooms]),
                    )
                )
            if c.faculties:
                # we must assign to a faculty from the candidates
                course_constraint_list.append(
                    cast(
                        z3.BoolRef,
                        z3.Or([c.faculty == z3_data.faculty_constants[faculty] for faculty in c.faculties]),
                    )
                )
            if conflict_constraints:
                course_constraint_list.append(cast(z3.BoolRef, z3.And(conflict_constraints)))

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

            # Enforce same room usage when both courses can use the same rooms
            if set(i.rooms) & set(j.rooms):
                resource.append(
                    cast(
                        z3.BoolRef,
                        z3.Implies(
                            i.room == j.room,
                            z3.Not(overlaps(i.time, j.time)),
                        ),
                    )
                )
                if i.course_id == j.course_id:
                    # when a faculty teaches two sections of the same course,
                    # they must use the same room
                    constraint_parts.append(cast(z3.BoolRef, i.room == j.room))

            # Enforce same lab usage when both courses have labs and can use the same labs
            if set(i.labs) & set(j.labs):
                resource.append(
                    cast(
                        z3.BoolRef,
                        z3.Implies(
                            i.lab == j.lab,
                            z3.Not(lab_overlaps(i.time, j.time)),
                        ),
                    )
                )
                if i.course_id == j.course_id:
                    # when a faculty teaches two sections of the same course,
                    # they must use the same lab
                    constraint_parts.append(cast(z3.BoolRef, i.lab == j.lab))

            # Prevent time overlap for courses taught by same faculty
            constraint_parts.append(cast(z3.BoolRef, z3.Not(overlaps(i.time, j.time))))
            if i.course_id == j.course_id:
                # when a faculty teaches two sections of the same course,
                # they must be next to each other
                constraint_parts.append(
                    cast(
                        z3.BoolRef,
                        z3.And(
                            lecture_next_to(i.time, j.time),
                            lab_next_to(i.time, j.time),
                        ),
                    )
                )
            else:
                # when a faculty teaches two sections of different courses,
                # they must not be next to each other
                constraint_parts.append(
                    cast(
                        z3.BoolRef,
                        z3.And(
                            z3.Not(lecture_next_to(i.time, j.time)),
                            z3.Not(lab_next_to(i.time, j.time)),
                        ),
                    )
                )

            if resource:
                # add all resource constraints (room, lab, etc.)
                resource_constraints.append(cast(z3.BoolRef, z3.And(resource)))
            # add all course constraints when faculty is the same
            resource_constraints.append(
                cast(
                    z3.BoolRef,
                    z3.Implies(i.faculty == j.faculty, z3.And(constraint_parts)),
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

            if time is None or faculty is None or room is None:
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
            logger.info("Created all optimization goals")
        else:
            logger.info("Skipping optimization goals")

        for i in range(self._limit):
            start_time = time.time()
            if s.check() == z3.sat:
                generation_time = time.time() - start_time
                logger.info(f"Schedule {i + 1} generation took {generation_time:.2f}s")
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
                logger.info(f"Final check took {generation_time:.2f} seconds")
                break
