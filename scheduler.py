import json
import itertools
import sys
from typing import Any, Callable, Dict, Iterable, List, Tuple, Optional

import json_fix
import z3
from pydantic import BaseModel, Field

# Configure Z3 to use parallel solving with advanced optimization parameters
z3.set_param("parallel.enable", True)
z3.set_param("parallel.threads.max", 8)  # Reduced from 16 for better efficiency

# Optimized Z3 parameters for faster solving
z3.set_param("sat.restart.max", 50)  # Reduced restart limit
z3.set_param("sat.gc.increment", 1000)  # More aggressive GC
z3.set_param("sat.gc.initial", 5000)  # Lower initial GC threshold
z3.set_param("smt.arith.solver", 6)  # Fast arithmetic solver
z3.set_param("smt.arith.nl.order", True)  # Order non-linear terms
z3.set_param("sat.phase", "caching")  # Use phase caching
z3.set_param("sat.branching.heuristic", "vsids")  # VSIDS heuristic
z3.set_param("smt.core.minimize", False)  # Disable for speed
z3.set_param("smt.relevancy", 1)  # Minimal relevancy
z3.set_param("model.compact", True)  # Compact models
z3.set_param("auto_config", False)  # Disable auto-config for predictable performance

from course import Course
from lab import Lab
from room import Room
from faculty import Faculty
from time_slot import Day, Duration, TimeInstance, TimePoint, TimeSlot
from config import time_slots


# Pydantic models for JSON configuration
class CourseConfig(BaseModel):
    course_id: str
    credits: int
    room: List[str]
    lab: List[str]
    conflicts: List[str]
    faculty: Optional[List[str]] = (
        None  # Optional override - if not specified, derive from preferences
    )


class FacultyConfig(BaseModel):
    maximum_credits: int = Field(default=12)
    minimum_credits: int = Field(default=12)
    unique_course_limit: int = Field(default=2)
    times: Dict[str, List[str]]  # {day_name: ["HH:MM-HH:MM", ...]}
    preferences: Dict[str, int] = Field(default_factory=dict)


class SchedulerConfig(BaseModel):
    rooms: List[str]
    labs: List[str]
    courses: List[CourseConfig]
    faculty: Dict[str, FacultyConfig]


def load_from_file(filename: str) -> SchedulerConfig:
    with open(filename) as f:
        data = json.load(f)
    return SchedulerConfig(**data)


class Scheduler:

    def __init__(self, config: SchedulerConfig):
        # Enhanced cache for simplification and precomputed values
        self._simplify_cache = {}
        self._slot_relationship_cache = {}

        LOOKUP: List[str] = [
            "credits",
            "course_id",
            "lab",
            "room",
            "faculty",
            "conflicts",
        ]

        # Create faculty instances first
        self.faculty_instances: Dict[str, Faculty] = dict()
        self.faculty_maximum_credits: Dict[str, int] = dict()
        self.faculty_minimum_credits: Dict[str, int] = dict()
        self.faculty_unique_course_limits: Dict[str, int] = dict()
        self.faculty_preferences: Dict[str, Dict[str, int]] = dict()
        for faculty_name, faculty_data in config.faculty.items():
            self.faculty_instances[faculty_name] = Faculty(faculty_name)
            self.faculty_maximum_credits[faculty_name] = faculty_data.maximum_credits
            self.faculty_minimum_credits[faculty_name] = faculty_data.minimum_credits
            self.faculty_unique_course_limits[faculty_name] = (
                faculty_data.unique_course_limit
            )
            self.faculty_preferences[faculty_name] = faculty_data.preferences

        self.rooms: Dict[str, Room] = dict((r, Room(r)) for r in config.rooms)

        self.labs: Dict[str, Lab] = dict((l, Lab(l)) for l in config.labs)

        self.courses: List[Course] = []
        # Pre-compute required credits to optimize slot generation
        required_credits = set()
        for c in config.courses:
            required_credits.add(c.credits)
            # Determine faculty for this course
            if c.faculty is not None:
                # Use explicit faculty list as override
                course_faculty = c.faculty
            else:
                # Automatically determine faculty from preferences
                course_faculty = []
                for faculty_name, faculty_config in config.faculty.items():
                    if c.course_id in faculty_config.preferences:
                        course_faculty.append(faculty_name)

            course_args = [
                c.credits,
                c.course_id,
                c.lab,
                c.room,
                course_faculty,
                c.conflicts,
            ]
            self.courses.append(Course(*course_args))

        Time = Tuple[int, int]
        Range = Tuple[Time, Time]
        DayRanges = List[Range]

        def get_info(faculty_config: FacultyConfig) -> List[TimeInstance]:
            days: List[Day] = [Day.MON, Day.TUE, Day.WED, Day.THU, Day.FRI]
            result: List[TimeInstance] = list()
            for day in days:
                day_name = day.name
                times = faculty_config.times.get(day_name, [])
                for time_range in times:
                    # Parse "HH:MM-HH:MM" format
                    start_str, end_str = time_range.split("-")
                    start_hour, start_minute = map(int, start_str.split(":"))
                    end_hour, end_minute = map(int, end_str.split(":"))

                    start_time: TimePoint = TimePoint.make_from(
                        start_hour, start_minute
                    )
                    end_time: TimePoint = TimePoint.make_from(end_hour, end_minute)
                    duration: Duration = end_time - start_time
                    result.append(TimeInstance(day, start_time, duration))
            return result

        self.faculty_availability: dict[str, List[TimeInstance]] = {
            faculty_name: get_info(faculty_config)
            for faculty_name, faculty_config in config.faculty.items()
        }

        def generate_slots() -> Tuple[Dict[int, Tuple[int, int]], List[TimeSlot]]:
            ranges: Dict[int, Tuple[int, int]] = dict()
            slots: List[TimeSlot] = list()
            low = TimeSlot.min_id()
            # Only generate slots for credits actually needed
            for credits in sorted(required_credits):
                for s in time_slots(credits):
                    slots.append(s)
                high = TimeSlot.max_id()
                ranges[credits] = (low, high)
                low = TimeSlot.max_id() + 1
            return ranges, slots

        ranges, slots = generate_slots()
        self.ranges = ranges
        self.slots = slots

        # Reduce verbose output for performance
        print(
            f"Generated {len(slots)} time slots for credits: {sorted(required_credits)}",
            file=sys.stderr,
        )

        # Pre-filter slots based on faculty availability to reduce constraint space
        self._prefilter_slots()

        # Update ranges after pre-filtering to only include valid slot IDs
        self._update_ranges_after_filtering()

        self.constraints, self.soft_constraints = self._build()

    def _prefilter_slots(self):
        """Pre-filter time slots to remove those that are impossible given faculty availability"""
        # This is an optimization to reduce the constraint space upfront
        valid_slots = []

        for slot in self.slots:
            # Check if at least one faculty member can teach at this time
            slot_feasible = False
            for faculty_name, faculty_times in self.faculty_availability.items():
                if slot.in_time_ranges(faculty_times):
                    slot_feasible = True
                    break

            if slot_feasible:
                valid_slots.append(slot)

        removed_count = len(self.slots) - len(valid_slots)
        if removed_count > 0:
            print(
                f"Pre-filtered {removed_count} infeasible time slots", file=sys.stderr
            )
            self.slots = valid_slots

    def _update_ranges_after_filtering(self):
        """Update slot ranges after pre-filtering to only include valid slot IDs"""
        # Group remaining slots by credits
        slots_by_credits = {}
        for slot in self.slots:
            # Determine credits by checking which range this slot was originally in
            slot_credits = None
            for credits, (start, stop) in self.ranges.items():
                if start <= slot.id <= stop:
                    slot_credits = credits
                    break

            if slot_credits is not None:
                if slot_credits not in slots_by_credits:
                    slots_by_credits[slot_credits] = []
                slots_by_credits[slot_credits].append(slot.id)

        # Update ranges to only include valid slot IDs
        for credits in self.ranges.keys():
            if credits in slots_by_credits:
                valid_ids = sorted(slots_by_credits[credits])
                if valid_ids:
                    self.ranges[credits] = (min(valid_ids), max(valid_ids))
                    # Store the actual valid IDs for constraint generation
                    setattr(self, f"_valid_slot_ids_{credits}", valid_ids)
                else:
                    # No valid slots for this credit level
                    self.ranges[credits] = (0, -1)  # Invalid range
                    setattr(self, f"_valid_slot_ids_{credits}", [])
            else:
                self.ranges[credits] = (0, -1)  # Invalid range
                setattr(self, f"_valid_slot_ids_{credits}", [])

    def _simplify(self, x):
        """Cached simplification to avoid redundant computation"""
        x_str = str(x)
        if x_str not in self._simplify_cache:
            self._simplify_cache[x_str] = z3.simplify(
                x, cache_all=True, rewrite_patterns=False
            )
        return self._simplify_cache[x_str]

    def _cached_slot_relationship(
        self, fn_name: str, slot_i: TimeSlot, slot_j: TimeSlot
    ) -> bool:
        """Cache expensive slot relationship computations"""
        cache_key = (fn_name, slot_i.id, slot_j.id)
        if cache_key not in self._slot_relationship_cache:
            if fn_name == "overlaps":
                result = slot_i.overlaps(slot_j)
            elif fn_name == "lab_overlaps":
                result = slot_i.lab_overlaps(slot_j)
            elif fn_name == "labs_on_same_day":
                result = slot_i.labs_on_same_day(slot_j)
            elif fn_name == "next_to":
                result = slot_i.next_to(slot_j)
            elif fn_name == "next_to_tues_wed":
                result = slot_i.next_to_tues_wed(slot_j)
            elif fn_name == "not_next_to":
                result = slot_i.not_next_to(slot_j)
            else:
                raise ValueError(f"Unknown relationship function: {fn_name}")
            self._slot_relationship_cache[cache_key] = result
        return self._slot_relationship_cache[cache_key]

    def _z3ify_time_constraint_optimized(
        self, name: str, fn: Callable[[TimeSlot, TimeSlot], bool]
    ) -> Tuple[z3.Function, List[z3.ArithRef]]:
        z3fn = z3.Function(name, z3.IntSort(), z3.IntSort(), z3.BoolSort())

        # Pre-compute all slot evaluations and group by result
        true_pairs = []
        false_pairs = []

        # Process combinations more efficiently with caching
        for i, slot_i in enumerate(self.slots):
            for j, slot_j in enumerate(self.slots[i + 1 :], i + 1):
                if self._cached_slot_relationship(name, slot_i, slot_j):
                    true_pairs.extend([(slot_i.id, slot_j.id), (slot_j.id, slot_i.id)])
                else:
                    false_pairs.extend([(slot_i.id, slot_j.id), (slot_j.id, slot_i.id)])

        # Handle diagonal (self-relations) - always true for most relationships
        for slot in self.slots:
            true_pairs.append((slot.id, slot.id))

        # Generate constraints in batches for better Z3 performance
        constraints = []

        # Batch true constraints
        for sid_i, sid_j in true_pairs:
            constraints.append(z3fn(z3.IntVal(sid_i), z3.IntVal(sid_j)))

        # Batch false constraints
        for sid_i, sid_j in false_pairs:
            constraints.append(z3.Not(z3fn(z3.IntVal(sid_i), z3.IntVal(sid_j))))

        # Minimal simplification - only on smaller batches
        return z3fn, constraints

    def _z3ify_time_constraint(
        self, name: str, fn: Callable[[TimeSlot, TimeSlot], bool]
    ) -> Tuple[z3.Function, List[z3.ArithRef]]:
        return self._z3ify_time_constraint_optimized(name, fn)

    def _z3ify_time_slot_fn(
        self, name: str, fn: Callable[[TimeSlot], bool]
    ) -> Tuple[z3.Function, List[z3.ArithRef]]:
        z3fn = z3.Function(name, z3.IntSort(), z3.BoolSort())

        # Pre-compute slot evaluations and batch constraints
        true_slots = []
        false_slots = []

        for slot in self.slots:
            if fn(slot):
                true_slots.append(slot.id)
            else:
                false_slots.append(slot.id)

        constraints = []
        # Batch positive constraints
        for slot_id in true_slots:
            constraints.append(z3fn(z3.IntVal(slot_id)))

        # Batch negative constraints
        for slot_id in false_slots:
            constraints.append(z3.Not(z3fn(z3.IntVal(slot_id))))

        return z3fn, constraints

    def _z3ify_faculty_time_constraint(
        self, name: str
    ) -> Tuple[z3.Function, List[z3.ArithRef]]:
        z3fn = z3.Function(name, z3.IntSort(), z3.IntSort(), z3.BoolSort())

        constraints = []
        # Pre-compute faculty availability for all slots to avoid repeated computation
        faculty_slot_availability = {}
        for faculty_name, faculty in self.faculty_instances.items():
            faculty_times = self.faculty_availability[faculty_name]
            faculty_slot_availability[faculty_name] = {
                slot.id: slot.in_time_ranges(faculty_times) for slot in self.slots
            }

        # Batch constraint generation by availability
        available_pairs = []
        unavailable_pairs = []

        for faculty_name, faculty in self.faculty_instances.items():
            faculty_id = faculty.id
            for slot in self.slots:
                slot_id = slot.id
                if faculty_slot_availability[faculty_name][slot_id]:
                    available_pairs.append((faculty_id, slot_id))
                else:
                    unavailable_pairs.append((faculty_id, slot_id))

        # Generate constraints in batches
        for faculty_id, slot_id in available_pairs:
            constraints.append(z3fn(z3.IntVal(faculty_id), z3.IntVal(slot_id)))

        for faculty_id, slot_id in unavailable_pairs:
            constraints.append(z3.Not(z3fn(z3.IntVal(faculty_id), z3.IntVal(slot_id))))

        return z3fn, constraints

    def _build(self):
        # abstract function constraints
        overlaps, overlaps_C = self._z3ify_time_constraint(
            "overlaps", TimeSlot.overlaps
        )

        lab_overlaps, lab_overlaps_C = self._z3ify_time_constraint(
            "lab_overlaps", TimeSlot.lab_overlaps
        )

        labs_on_same_day, labs_on_same_day_C = self._z3ify_time_constraint(
            "labs_on_same_day", TimeSlot.labs_on_same_day
        )

        next_to, next_to_C = self._z3ify_time_constraint("next_to", TimeSlot.next_to)

        next_to_tues_wed, next_to_tues_wed_C = self._z3ify_time_constraint(
            "next_to_tues_wed", TimeSlot.next_to_tues_wed
        )

        not_next_to, not_next_to_C = self._z3ify_time_constraint(
            "not_next_to", TimeSlot.not_next_to
        )

        has_lab, has_lab_C = self._z3ify_time_slot_fn("has_lab", TimeSlot.has_lab)

        lab_starts_with_lecture, lab_starts_with_lecture_C = self._z3ify_time_slot_fn(
            "lab_starts_with_lecture", TimeSlot.lab_starts_with_lecture
        )

        faculty_available, faculty_available_C = self._z3ify_faculty_time_constraint(
            "faculty_available"
        )

        fn_constraints = (
            overlaps_C
            + lab_overlaps_C
            + labs_on_same_day_C
            + next_to_C
            + not_next_to_C
            + has_lab_C
            + faculty_available_C
        )
        soft_fn_constraints = lab_starts_with_lecture_C + next_to_tues_wed_C

        def hard_constraints():
            # Pre-compute course groupings to reduce repeated calculations
            faculty_course_map = {}
            for c in self.courses:
                for faculty_name in c.faculties:
                    if faculty_name not in faculty_course_map:
                        faculty_course_map[faculty_name] = []
                    faculty_course_map[faculty_name].append(c)

            # Add faculty credit and unique course limits - batch generation
            faculty_constraints = []
            for faculty_name, faculty in self.faculty_instances.items():
                faculty_courses = faculty_course_map.get(faculty_name, [])
                if faculty_courses:
                    min_credits = self.faculty_minimum_credits[faculty_name]
                    max_credits = self.faculty_maximum_credits[faculty_name]
                    mapping = [
                        (c.faculty() == faculty.id, c.credits) for c in faculty_courses
                    ]
                    faculty_constraints.append(z3.PbGe(mapping, min_credits))
                    faculty_constraints.append(z3.PbLe(mapping, max_credits))

                    # Unique course limit constraint - only generate if needed
                    unique_limit = self.faculty_unique_course_limits[faculty_name]
                    if unique_limit < float("inf"):
                        # Group courses by their unique identifier (subject + number)
                        unique_courses = {}
                        for c in faculty_courses:
                            if c.course_id not in unique_courses:
                                unique_courses[c.course_id] = []
                            unique_courses[c.course_id].append(c)

                        # Only create constraint if there are multiple unique courses
                        if len(unique_courses) > unique_limit:
                            teaches_course = []
                            for course_group in unique_courses.values():
                                teaches_course.append(
                                    z3.Or(
                                        [
                                            c.faculty() == faculty.id
                                            for c in course_group
                                        ]
                                    )
                                )
                            faculty_constraints.append(
                                z3.PbLe(
                                    [(tc, 1) for tc in teaches_course], unique_limit
                                )
                            )

            # Yield faculty constraints in batch
            for constraint in faculty_constraints:
                yield self._simplify(constraint)

            # Pre-compute conflict mapping for efficiency
            conflict_map = {}
            for c in self.courses:
                for conflict_id in c.conflicts:
                    if conflict_id not in conflict_map:
                        conflict_map[conflict_id] = []
                    conflict_map[conflict_id].append(c)

            # Course constraints with optimized conflict checking - batch generation
            course_constraints = []
            for c in self.courses:
                # Get valid slot IDs for this course's credit level after pre-filtering
                valid_slot_ids = getattr(self, f"_valid_slot_ids_{c.credits}", [])

                # Build conflict constraints more efficiently
                conflict_constraints = []
                for conflict_id in c.conflicts:
                    if conflict_id in conflict_map:
                        for d in conflict_map[conflict_id]:
                            if d != c and d.course_id == conflict_id:
                                conflict_constraints.append(
                                    z3.Not(overlaps(c.time(), d.time()))
                                )

                course_constraint_list = []
                # basic timeslot constraint - only allow valid slot IDs after filtering
                if valid_slot_ids:
                    course_constraint_list.append(
                        z3.Or(
                            [
                                c.time() == z3.IntVal(slot_id)
                                for slot_id in valid_slot_ids
                            ]
                        )
                    )
                if c.labs:
                    # we must assign to a lab when we have options
                    course_constraint_list.append(
                        z3.Or(
                            [
                                c.lab() == lab.id
                                for name, lab in self.labs.items()
                                if name in c.labs
                            ]
                        )
                    )
                if c.rooms:
                    # we must assign to a room when we have options
                    course_constraint_list.append(
                        z3.Or(
                            [
                                c.room() == room.id
                                for name, room in self.rooms.items()
                                if name in c.rooms
                            ]
                        )
                    )
                if c.faculties:
                    # we must assign to a faculty from the candidates
                    course_constraint_list.append(
                        z3.Or(
                            [
                                c.faculty() == faculty.id
                                for name, faculty in self.faculty_instances.items()
                                if name in c.faculties
                            ]
                        )
                    )
                if conflict_constraints:
                    # check the other courses time slot constraint(s)
                    course_constraint_list.append(z3.And(conflict_constraints))
                # check the faculty time constraint - ensure assigned faculty is available at assigned time
                course_constraint_list.append(faculty_available(c.faculty(), c.time()))
                course_constraints.append(z3.And(course_constraint_list))

            # Yield course constraints in batch
            for constraint in course_constraints:
                yield self._simplify(constraint)

            # Faculty-specific constraints - ALL course pairs must be checked for faculty overlap
            course_pairs = list(itertools.combinations(self.courses, 2))
            faculty_pair_constraints = []

            for i, j in course_pairs:
                same_faculty_condition = i.faculty() == j.faculty()

                no_overlap_constraint = z3.Not(overlaps(i.time(), j.time()))

                constraint_parts = [no_overlap_constraint]

                if i.course_id == j.course_id:

                    # Enforce adjacency for same course sections with same faculty
                    constraint_parts.append(next_to(i.time(), j.time()))

                    # Enforce same room usage when both courses can use the same rooms
                    if set(i.rooms) & set(j.rooms):
                        constraint_parts.append(i.room() == j.room())

                    # Enforce same lab usage when both courses have labs and can use the same labs
                    if set(i.labs) & set(j.labs):
                        constraint_parts.append(i.lab() == j.lab())

                else:
                    # Different courses with same faculty should not be adjacent
                    constraint_parts.append(not_next_to(i.time(), j.time()))

                faculty_pair_constraints.append(
                    z3.Implies(same_faculty_condition, z3.And(constraint_parts))
                )

            # Yield faculty pair constraints in batch
            for constraint in faculty_pair_constraints:
                yield self._simplify(constraint)

            # Resource overlap constraints - prevent double-booking of rooms and labs
            resource_constraints = []
            for i, j in course_pairs:
                constraint_parts = []

                # Room overlap check - if any two courses use the same room, they cannot overlap in time
                if set(i.rooms) & set(
                    j.rooms
                ):  # Only if they can potentially share rooms
                    constraint_parts.append(
                        z3.Implies(
                            i.room() == j.room(), z3.Not(overlaps(i.time(), j.time()))
                        )
                    )

                # Lab overlap check - if any two courses use the same lab, their labs cannot overlap
                if set(i.labs) & set(j.labs):  # Only if they can potentially share labs
                    constraint_parts.append(
                        z3.Implies(
                            i.lab() == j.lab(), z3.Not(lab_overlaps(i.time(), j.time()))
                        )
                    )

                if constraint_parts:
                    resource_constraints.append(z3.And(constraint_parts))

            # Yield resource constraints in batch
            for constraint in resource_constraints:
                yield self._simplify(constraint)

        def soft_constraints():

            # Group courses by assigned faculty for soft constraints
            soft_constraint_list = []
            for i, j in itertools.combinations(self.courses, 2):
                # When two courses are assigned the same faculty and are the same course
                soft_constraint_list.append(
                    z3.Implies(
                        z3.And(i.faculty() == j.faculty(), i.course_id == j.course_id),
                        # useful for fall schedules -- ensures no T/W split between different sections for labs
                        z3.Not(next_to_tues_wed(i.time(), j.time())),
                    )
                )

            # For single sections of a course with a given faculty
            for c in self.courses:
                if c.labs:
                    # if we only have a single course, make sure the lab start time aligns with lecture start time
                    soft_constraint_list.append(lab_starts_with_lecture(c.time()))

            for constraint in soft_constraint_list:
                yield self._simplify(constraint)

        # Generate constraints without excessive simplification
        print("Generating hard constraints...", file=sys.stderr)
        C = list(hard_constraints())
        print(f"Generated {len(C)} hard constraints", file=sys.stderr)

        print("Generating soft constraints...", file=sys.stderr)
        S = list(soft_constraints())
        print(f"Generated {len(S)} soft constraints", file=sys.stderr)

        hard = soft_fn_constraints + fn_constraints + C
        soft = S

        return hard, soft

    def get_models(self, limit=10, optimize_preferences=True):
        def update(
            i: int, s: z3.Optimize
        ) -> Iterable[Tuple[int, z3.ModelRef, z3.Statistics]]:
            m: z3.ModelRef = s.model()
            stat: z3.Statistics = s.statistics()

            yield i, m, stat

            def constraints():
                # Group courses by assigned faculty and course ID for permutations
                for i, j in itertools.combinations(self.courses, 2):
                    # When two courses are assigned the same faculty and are the same course
                    if m[i.faculty()] == m[j.faculty()] and i.course_id == j.course_id:
                        ordered = [i, j]
                        if ordered[0].labs:
                            yield z3.Or(
                                [
                                    z3.And(
                                        [
                                            z3.And(
                                                act_time == exp.time(),
                                                act_room == exp.room(),
                                                act_lab == exp.lab(),
                                                act_faculty == exp.faculty(),
                                            )
                                            for (
                                                act_time,
                                                act_room,
                                                act_lab,
                                                act_faculty,
                                            ), exp in zip(
                                                (
                                                    (
                                                        m[c.time()],
                                                        m[c.room()],
                                                        m[c.lab()],
                                                        m[c.faculty()],
                                                    )
                                                    for c in ordered
                                                ),
                                                r,
                                            )
                                        ]
                                    )
                                    for r in itertools.permutations(ordered)
                                ]
                            )
                        else:
                            yield z3.Or(
                                [
                                    z3.And(
                                        [
                                            z3.And(
                                                act_time == exp.time(),
                                                act_room == exp.room(),
                                                act_faculty == exp.faculty(),
                                            )
                                            for (
                                                act_time,
                                                act_room,
                                                act_faculty,
                                            ), exp in zip(
                                                (
                                                    (
                                                        m[c.time()],
                                                        m[c.room()],
                                                        m[c.faculty()],
                                                    )
                                                    for c in ordered
                                                ),
                                                r,
                                            )
                                        ]
                                    )
                                    for r in itertools.permutations(ordered)
                                ]
                            )

            s.add(self._simplify(z3.Not(z3.And(*constraints()))))

        s = z3.Optimize()

        # Optimized solver configuration for faster solving
        s.set("timeout", 120000)  # Reduced to 2 minutes for faster iteration
        s.set("maxsat_engine", "wmax")  # Use MaxRes engine for optimization
        s.set("priority", "lex")  # Lexicographic priority for multiple objectives
        s.set("opt.enable_sat", True)  # Enable SAT solver optimization
        s.set("opt.enable_core_rotate", False)  # Disable expensive core rotation
        s.set("opt.enable_lns", False)  # Disable local neighborhood search for speed
        s.set(
            "opt.maxres.hill_climb", True
        )  # Enable hill climbing for better solutions
        s.set("opt.maxres.max_num_cores", 32)  # Reduced core generation
        s.set("opt.maxres.max_core_size", 8)  # Smaller core size for faster processing
        s.set("opt.maxres.pivot_on_correction_set", False)  # Disable for speed
        s.set("opt.maxres.add_upper_bound_block", True)  # Better bounds

        # Add constraints with larger batching for better performance
        constraint_batch_size = 128
        constraints = self.constraints
        print(
            f"Adding {len(constraints)} constraints to solver in batches of {constraint_batch_size}",
            file=sys.stderr,
        )

        for i in range(0, len(constraints), constraint_batch_size):
            batch = constraints[i : i + constraint_batch_size]
            s.add(batch)

        soft_constraints = self.soft_constraints
        print(
            f"Added {len(soft_constraints)} soft constraints to solver in batches of {constraint_batch_size}",
            file=sys.stderr,
        )

        for i in range(0, len(soft_constraints), constraint_batch_size):
            batch = soft_constraints[i : i + constraint_batch_size]
            s.add_soft(batch)

        # Add faculty preferences as optimization goals with improved caching - only if requested
        if optimize_preferences:
            preference_terms = []
            faculty_id_cache = {
                name: faculty.id for name, faculty in self.faculty_instances.items()
            }

            total_preferences = 0
            for faculty_name, preferences in self.faculty_preferences.items():
                if not preferences:  # Skip faculty with no preferences
                    continue

                faculty_id = faculty_id_cache[faculty_name]
                for course in self.courses:
                    if course.course_id in preferences:
                        # Use preference value directly (1-5 scale where 5 is strongly prefer, 1 is weakest)
                        preference_value = preferences[course.course_id]
                        term = z3.If(
                            course.faculty() == faculty_id, preference_value, 0
                        )
                        preference_terms.append(term)
                        total_preferences += 1

            if preference_terms:
                print(
                    f"Adding {total_preferences} faculty preference optimization goals",
                    file=sys.stderr,
                )
                # Improved batching for large numbers of preferences
                if len(preference_terms) > 30:
                    # For large numbers of preferences, create smaller sub-sums for better performance
                    batch_size = 15
                    sub_sums = []
                    for i in range(0, len(preference_terms), batch_size):
                        batch = preference_terms[i : i + batch_size]
                        sub_sums.append(z3.Sum(batch))
                    s.maximize(z3.Sum(sub_sums))
                else:
                    # Maximize the sum of preference values
                    s.maximize(z3.Sum(preference_terms))
        else:
            print(
                "Skipping faculty preference optimization for faster solving",
                file=sys.stderr,
            )

        i = 0
        while i < limit and s.check() == z3.sat:
            for j, m, stat in update(i, s):
                yield j, m, stat
            i += 1


def concretize(map: Dict):
    def iter():
        for k, v in map.items():
            if k == "room":
                yield (k, Room.get(map["room"]).name)
            elif k == "lab":
                if v:
                    yield (
                        k,
                        {
                            "room": Lab.get(map["lab"]).name,
                            "time": TimeSlot.get(map["time"]).lab_time(),
                        },
                    )
            elif k == "time":
                yield (k, list(t for t in TimeSlot.get(map["time"])._times))
            elif k == "faculty":
                yield (k, Faculty.get(map["faculty"]).name)
            else:
                yield (k, v)

    return dict(iter())


def generate_models(data, limit, optimize_preferences=True):
    config = load_from_file(data)
    s = Scheduler(config)

    def all():
        for _, m, _ in s.get_models(limit, optimize_preferences):
            yield list(concretize(c.evaluate(m)) for c in s.courses)

    return json.dumps(list(all()), separators=(",", ":"))


if __name__ == "__main__":

    if len(sys.argv) < 2:
        print(
            f"Usage: {sys.argv[0]} <json_config> [limit=10] [json] [--no-preferences]"
        )
        exit(1)

    config_file = sys.argv[1]

    limit = 10 if len(sys.argv) == 2 else int(sys.argv[2])

    dump_json = len(sys.argv) >= 4 and "json" in sys.argv[3:]

    optimize_preferences = "--no-preferences" not in sys.argv

    if dump_json:
        print(generate_models(config_file, limit, optimize_preferences))
        exit(0)

    print(
        f"> Using limit={limit}, optimize_preferences={optimize_preferences}",
        file=sys.stderr,
    )
    config = load_from_file(config_file)
    sched = Scheduler(config)
    print(f"> Created all constraints", file=sys.stderr)

    for i, m, s in sched.get_models(limit, optimize_preferences):
        print(f"Model {i}:", file=sys.stderr)
        print("  ", end="", file=sys.stderr)
        for j in s.keys():
            print(f"{j}:{s.get_key_value(j)}  ", end="", file=sys.stderr)
        print("\n", file=sys.stderr)

        print("\n".join(c.csv(m) for c in sched.courses))

        try:
            print(file=sys.stderr)
            input()
            print(file=sys.stderr)
            print("> Getting next model...", file=sys.stderr)
        except:
            exit(0)
