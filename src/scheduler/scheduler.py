import itertools
import json
import threading
import time
from collections import defaultdict
from collections.abc import Callable
from functools import cache
from typing import cast

import z3  # type: ignore
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

DEFAULT_MIN_OVERLAP = 45


def load_config_from_file[T: BaseModel](
    config_cls: type[T],
    filename: str,
) -> T:
    """Load scheduler configuration from a JSON file."""
    with open(filename, encoding="utf-8") as f:
        data = json.load(f)
    return config_cls(**data)


def get_faculty_availability(
    faculty_config: FacultyConfig,
) -> list[TimeInstance]:
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


class Scheduler:
    _init_lock = threading.Lock()

    def __init__(self, full_config: CombinedConfig):
        """
        Initialize the scheduler.

        Args:
            config: Configuration object containing courses, faculty, rooms, and labs
            time_slot_config: Time slot configuration object
        """

        config = full_config.config
        time_slot_config = full_config.time_slot_config
        self._optimizer_flags = full_config.optimizer_flags
        self._limit = full_config.limit

        self._ctx = z3.Context()

        # Create faculty instances first
        self._faculty: set[str] = set()
        self._faculty_maximum_credits: dict[str, int] = dict()
        self._faculty_minimum_credits: dict[str, int] = dict()
        self._faculty_unique_course_limits: dict[str, int] = dict()
        self._faculty_course_preferences: dict[str, dict[str, int]] = dict()
        self._faculty_room_preferences: dict[str, dict[str, int]] = dict()
        self._faculty_lab_preferences: dict[str, dict[str, int]] = dict()
        self._faculty_availability: dict[str, list[TimeInstance]] = dict()

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

        self._rooms: set[str] = set(config.rooms)

        self._labs: set[str] = set(config.labs)

        self._courses: list[Course] = []

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
                ctx=self._ctx,
            )
            self._courses.append(course)

        self._time_slot_generator: TimeSlotGenerator = TimeSlotGenerator(time_slot_config)

        self._ranges: dict[int, tuple[int, int]] = dict()
        self._slots: list[TimeSlot] = list()

        with self._init_lock:
            for creds in sorted(required_credits):
                low = TimeSlot.max_id() + 1
                for s in self._time_slot_generator.time_slots(creds, min_overlap=DEFAULT_MIN_OVERLAP):
                    self._slots.append(s)
                self._ranges[creds] = (low, TimeSlot.max_id())
                low = TimeSlot.max_id() + 1

        # Create EnumSorts for each type
        self._create_enum_sorts()

        self._build_constraints()

    def _create_enum_sorts(self):
        """Create EnumSorts for each type to replace IntSort usage."""
        # Create TimeSlot EnumSort (still use IDs for uniqueness)
        time_slot_names = [f"ts_{slot.id}" for slot in self._slots]
        self._time_slot_sort, time_slot_constants = z3.EnumSort("TimeSlot", time_slot_names, ctx=self._ctx)
        self._time_slot_constants = {slot.id: time_slot_constants[i] for i, slot in enumerate(self._slots)}

        # Helper to sanitize names for EnumSort
        def sanitize(name):
            return name.replace(" ", "_")

        # Create Faculty EnumSort using names
        faculty_names = [sanitize(faculty) for faculty in self._faculty]
        self._faculty_sort, faculty_constants = z3.EnumSort("Faculty", faculty_names, ctx=self._ctx)
        self._faculty_constants = {faculty: faculty_constants[i] for i, faculty in enumerate(self._faculty)}
        self._faculty_constant_to_name = {faculty_constants[i]: faculty for i, faculty in enumerate(self._faculty)}

        # Create Room EnumSort using names
        room_names = [sanitize(room) for room in self._rooms]
        self._room_sort, room_constants = z3.EnumSort("Room", room_names, ctx=self._ctx)
        self._room_constants = {room: room_constants[i] for i, room in enumerate(self._rooms)}
        self._room_constant_to_name = {room_constants[i]: room for i, room in enumerate(self._rooms)}

        # Create Lab EnumSort using names
        lab_names = [sanitize(lab) for lab in self._labs]
        self._lab_sort, lab_constants = z3.EnumSort("Lab", lab_names, ctx=self._ctx)
        self._lab_constants = {lab: lab_constants[i] for i, lab in enumerate(self._labs)}
        self._lab_constant_to_name = {lab_constants[i]: lab for i, lab in enumerate(self._labs)}

        # Create course variables using EnumSorts
        for course in self._courses:
            course._time = z3.Const(f"{str(course)}_time", self._time_slot_sort)
            course._faculty = z3.Const(f"{str(course)}_faculty", self._faculty_sort)
            course._room = z3.Const(f"{str(course)}_room", self._room_sort)
            course._lab = z3.Const(f"{str(course)}_lab", self._lab_sort)

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
        self, name: str, *, ctx: z3.Context | None = None
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        z3fn = z3.Function(
            name,
            self._time_slot_sort,
            self._time_slot_sort,
            z3.BoolSort(ctx=ctx),
        )

        true: list[tuple[z3.BoolRef, z3.BoolRef]] = []
        false: list[tuple[z3.BoolRef, z3.BoolRef]] = []
        for slot_i in self._slots:
            c_i = self._time_slot_constants[slot_i.id]
            if self._cached_slot_relationship(name, slot_i, slot_i):
                true.append((c_i, c_i))
            else:
                false.append((c_i, c_i))

        for slot_i, slot_j in itertools.combinations(self._slots, 2):
            c_i = self._time_slot_constants[slot_i.id]
            c_j = self._time_slot_constants[slot_j.id]
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
        name: str,
        fn: Callable[[TimeSlot], bool],
        *,
        ctx: z3.Context | None = None,
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        z3fn = z3.Function(name, self._time_slot_sort, z3.BoolSort(ctx=ctx))

        true: list[z3.BoolRef] = []
        false: list[z3.BoolRef] = []
        for slot in self._slots:
            c = self._time_slot_constants[slot.id]
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
        self, name: str, *, ctx: z3.Context | None = None
    ) -> tuple[z3.FuncDeclRef, list[z3.BoolRef]]:
        z3fn = z3.Function(
            name,
            self._faculty_sort,
            self._time_slot_sort,
            z3.BoolSort(ctx=ctx),
        )

        availability = {}
        for faculty in self._faculty:
            faculty_times = self._faculty_availability[faculty]
            availability[faculty] = {slot.id: slot.in_time_ranges(faculty_times) for slot in self._slots}

        constraints: list[z3.BoolRef] = []
        for faculty in self._faculty:
            true: list[tuple[z3.BoolRef, z3.BoolRef]] = []
            false: list[tuple[z3.BoolRef, z3.BoolRef]] = []
            faculty_constant = self._faculty_constants[faculty]
            for slot in self._slots:
                slot_constant = self._time_slot_constants[slot.id]
                if availability[faculty][slot.id]:
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

    def _build_constraints(self):
        # abstract function constraints
        overlaps, overlaps_C = self._z3ify_time_constraint("overlaps", ctx=self._ctx)
        lab_overlaps, lab_overlaps_C = self._z3ify_time_constraint("lab_overlaps", ctx=self._ctx)
        lecture_next_to, lecture_next_to_C = self._z3ify_time_constraint("lecture_next_to", ctx=self._ctx)
        faculty_available, faculty_available_C = self._z3ify_faculty_time_constraint("faculty_available", ctx=self._ctx)
        lab_next_to, lab_next_to_C = self._z3ify_time_constraint("lab_next_to", ctx=self._ctx)

        self._lab_next_to = lab_next_to
        self._lecture_next_to = lecture_next_to

        function_constraints: list[z3.BoolRef] = []
        function_constraints.extend(overlaps_C)
        function_constraints.extend(lab_overlaps_C)
        function_constraints.extend(lecture_next_to_C)
        function_constraints.extend(lab_next_to_C)
        function_constraints.extend(faculty_available_C)

        # Pre-compute course groupings to reduce repeated calculations
        faculty_course_map: defaultdict[str, list[Course]] = defaultdict(list)
        for c in self._courses:
            for faculty in c.faculties:
                faculty_course_map[faculty].append(c)

        # Add faculty credit and unique course limits - batch generation
        faculty_constraints: list[z3.BoolRef] = []
        for faculty in self._faculty:
            faculty_courses = faculty_course_map.get(faculty, [])
            faculty_constant = self._faculty_constants[faculty]
            if faculty_courses:
                min_credits = self._faculty_minimum_credits[faculty]
                max_credits = self._faculty_maximum_credits[faculty]
                credit_sum = z3.Sum([z3.If(c.faculty() == faculty_constant, c.credits, 0) for c in faculty_courses])
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
                                z3.Or([c.faculty() == faculty_constant for c in course_group]),
                            )
                        )
                    # ensure that each faculty is assigned <= unique course limit
                    limit = cast(
                        z3.BoolRef,
                        self._simplify(z3.Sum([z3.If(tc, 1, 0) for tc in teaches_course]) <= unique_limit),
                    )
                    faculty_constraints.append(limit)

        # Course constraints with optimized conflict checking - batch generation
        course_constraints: list[z3.BoolRef] = []
        for c in self._courses:
            # conflict constraints
            conflict_constraints: list[z3.BoolRef] = [
                cast(z3.BoolRef, z3.Not(overlaps(c.time(), d.time())))
                for d in self._courses
                if d != c and d.course_id in c.conflicts
            ]

            # faculty availability constraint
            course_constraint_list: list[z3.BoolRef] = [
                cast(z3.BoolRef, faculty_available(c.faculty(), c.time())),
            ]

            # Get valid time slots for this credit level
            start, stop = self._ranges[c.credits]
            valid_time_slots = [slot for slot in self._slots if start <= cast(int, slot.id) <= stop]
            if valid_time_slots:
                # Constrain time to valid slots for this credit level
                course_constraint_list.append(
                    cast(
                        z3.BoolRef,
                        z3.Or([c.time() == self._time_slot_constants[slot.id] for slot in valid_time_slots]),
                    )
                )

            if c.labs:
                # we must assign to a lab when we have options
                course_constraint_list.append(
                    cast(
                        z3.BoolRef,
                        z3.Or([c.lab() == self._lab_constants[lab] for lab in self._labs if lab in c.labs]),
                    )
                )
            if c.rooms:
                # we must assign to a room when we have options
                course_constraint_list.append(
                    cast(
                        z3.BoolRef,
                        z3.Or([c.room() == self._room_constants[room] for room in self._rooms if room in c.rooms]),
                    )
                )
            if c.faculties:
                # we must assign to a faculty from the candidates
                course_constraint_list.append(
                    cast(
                        z3.BoolRef,
                        z3.Or([c.faculty() == self._faculty_constants[faculty] for faculty in c.faculties]),
                    )
                )
            if conflict_constraints:
                course_constraint_list.append(cast(z3.BoolRef, z3.And(conflict_constraints)))

            course_constraints.append(cast(z3.BoolRef, z3.And(course_constraint_list)))

        # Faculty-specific constraints - ALL course pairs must be checked for faculty overlap
        course_pairs = list(itertools.combinations(self._courses, 2))
        resource_constraints: list[z3.BoolRef] = []

        for i, j in course_pairs:
            resource: list[z3.BoolRef] = []
            constraint_parts: list[z3.BoolRef] = []

            # Enforce same room usage when both courses can use the same rooms
            if set(i.rooms) & set(j.rooms):
                resource.append(
                    cast(
                        z3.BoolRef,
                        z3.Implies(
                            i.room() == j.room(),
                            z3.Not(overlaps(i.time(), j.time())),
                        ),
                    )
                )
                if i.course_id == j.course_id:
                    # when a faculty teaches two sections of the same course,
                    # they must use the same room
                    constraint_parts.append(cast(z3.BoolRef, i.room() == j.room()))

            # Enforce same lab usage when both courses have labs and can use the same labs
            if set(i.labs) & set(j.labs):
                resource.append(
                    cast(
                        z3.BoolRef,
                        z3.Implies(
                            i.lab() == j.lab(),
                            z3.Not(lab_overlaps(i.time(), j.time())),
                        ),
                    )
                )
                if i.course_id == j.course_id:
                    # when a faculty teaches two sections of the same course,
                    # they must use the same lab
                    constraint_parts.append(cast(z3.BoolRef, i.lab() == j.lab()))

            # Prevent time overlap for courses taught by same faculty
            constraint_parts.append(cast(z3.BoolRef, z3.Not(overlaps(i.time(), j.time()))))
            if i.course_id == j.course_id:
                # when a faculty teaches two sections of the same course,
                # they must be next to each other
                constraint_parts.append(
                    cast(
                        z3.BoolRef,
                        z3.And(
                            lecture_next_to(i.time(), j.time()),
                            lab_next_to(i.time(), j.time()),
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
                            z3.Not(lecture_next_to(i.time(), j.time())),
                            z3.Not(lab_next_to(i.time(), j.time())),
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
                    z3.Implies(i.faculty() == j.faculty(), z3.And(constraint_parts)),
                )
            )

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

        self._constraints = all_constraints

    def _get_schedule(self, model: z3.ModelRef) -> list["CourseInstance"]:
        """
        Internal method to convert a Z3 model to a schedule of CourseInstance objects.

        Args:
            model: The Z3 model containing assignments

        Returns:
            List of CourseInstance objects representing the schedule
        """

        schedule = []
        for course in self._courses:
            time = TimeSlot.get(int(str(model.eval(course.time())).split("_")[1]))
            faculty = self._faculty_constant_to_name.get(model.eval(course.faculty()), None)
            room = self._room_constant_to_name.get(model.eval(course.room()), None)
            lab = self._lab_constant_to_name.get(model.eval(course.lab()), None)

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
        m: z3.ModelRef = s.model()
        rearranged = []
        per_course = []
        # group courses by faculty first
        for _, group_iter in itertools.groupby(self._courses, key=lambda x: m[x.faculty()]):
            group = list(group_iter)
            for _, cs_iter in itertools.groupby(group, key=lambda x: x.course_id):
                cs = list(cs_iter)
                if len(cs) > 1:
                    rearranged.append(
                        z3.And(
                            [
                                z3.And(i.time() != m[j.time()], j.time() != m[i.time()])
                                for i, j in itertools.combinations(cs, 2)
                            ]
                        )
                    )
                for c in cs:
                    per_instance = []
                    per_instance.append(c.time() == m[c.time()])
                    if c.rooms:
                        per_instance.append(c.room() == m[c.room()])
                    if c.labs:
                        per_instance.append(c.lab() == m[c.lab()])
                    per_course.append(z3.Not(z3.And(per_instance)))

        if rearranged:
            logger.debug(f"Adding 1 course rearrangement constraint with {len(rearranged)} predicates")
            s.add(z3.And(rearranged))
        if per_course:
            logger.debug(f"Adding 1 per-course constraint with {len(per_course)} predicates")
            s.add(z3.Or(per_course))

    def get_models(self):
        """
        Generate schedule models.

        Args:
            limit: Maximum number of schedules to generate (default: 10)
            optimizer_config: Configuration for the optimizer (default: None)

        Yields:
            List of CourseInstance objects representing a complete schedule
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

                faculty_constant = self._faculty_constants[faculty_name]
                for course in self._courses:
                    if course.course_id in preferences:
                        # Use preference value directly
                        # (1-5 scale where 5 is strongly prefer, 1 is weakest)
                        preference_value = preferences[course.course_id]
                        term = z3.If(
                            course.faculty() == faculty_constant,
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

                faculty_constant = self._faculty_constants[faculty_name]
                for course in self._courses:
                    for room in course.rooms:
                        room_constant = self._room_constants[room]
                        if room in preferences:
                            preference_value = preferences[room]
                            term = z3.If(
                                z3.And(
                                    course.faculty() == faculty_constant,
                                    course.room() == room_constant,
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

                faculty_constant = self._faculty_constants[faculty_name]
                for course in self._courses:
                    for lab in course.labs:
                        if lab in preferences:
                            preference_value = preferences[lab]
                            term = z3.If(
                                z3.And(
                                    course.faculty() == faculty_constant,
                                    course.lab() == self._lab_constants[lab],
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
                            z3.And(i.faculty() == j.faculty(), i.room() == j.room()),
                            1,
                            0,
                        )
                    )
                    if i.course_id != j.course_id:
                        packing_rooms.append(
                            z3.If(
                                z3.And(
                                    i.room() == j.room(),
                                    self._lecture_next_to(i.time(), j.time()),
                                ),
                                1,
                                0,
                            )
                        )
                if set(i.labs) & set(j.labs):
                    same_labs.append(z3.If(z3.And(i.faculty() == j.faculty(), i.lab() == j.lab()), 1, 0))
                    if i.course_id != j.course_id:
                        packing_labs.append(
                            z3.If(
                                z3.And(
                                    i.lab() == j.lab(),
                                    self._lab_next_to(i.time(), j.time()),
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

            logger.info("Created all optimization goals")
        else:
            logger.info(
                "Skipping optimization goals",
            )

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
