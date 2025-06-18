from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
import json
import itertools
from itertools import product
import logging
import threading
from typing import Callable, Dict, List, Tuple, Optional

import click
import z3
import json_fix  # type: ignore

from .models import (
    Course,
    Lab,
    Room,
    Faculty,
    Day,
    Duration,
    TimeInstance,
    TimePoint,
    TimeSlot,
)
from .config import SchedulerConfig, FacultyConfig, TimeBlock, TimeSlotConfig

# Configure logging
logging.basicConfig(level=logging.DEBUG)
logger = logging.getLogger(__name__)


def load_from_file(filename: str) -> SchedulerConfig:
    """Load scheduler configuration from a JSON file."""
    with open(filename, encoding="utf-8") as f:
        data = json.load(f)
    return SchedulerConfig(**data)


class TimeSlotConfiguration:
    """Configuration for time slots."""

    def __init__(self, time_slots_file: str):
        with open(time_slots_file, "r") as f:
            raw_config = json.load(f)
        self.config = TimeSlotConfig(**raw_config)
        self.config.model_validate(raw_config)

    def _parse_time(self, time_str: str) -> int:
        """Convert time string (HH:MM) to minutes since midnight."""
        hour, minute = map(int, time_str.split(":"))
        return hour * 60 + minute

    def _generate_day_slots(
        self,
        day: str,
        duration: int,
        time_blocks: List[TimeBlock],
        start_time: Optional[str] = None,
    ) -> List[TimeInstance]:
        """Generate all possible time slots for a given day and duration."""
        day_slots = []
        for block in time_blocks:
            block_start = self._parse_time(block.start)
            block_end = self._parse_time(block.end)

            if start_time:
                pattern_start = self._parse_time(start_time)
                if pattern_start < block_start or pattern_start + duration > block_end:
                    continue
                block_start = pattern_start

            current_start = block_start
            while current_start + duration <= block_end:
                time_instance = TimeInstance(
                    day=Day[day],
                    start=TimePoint.make_from(current_start // 60, current_start % 60),
                    duration=Duration(duration=duration),
                )
                day_slots.append(time_instance)
                current_start += block.spacing

        return day_slots

    def _validate_time_combination(
        self, time_combination: List[TimeInstance], min_overlap: int
    ) -> bool:
        """
        Validate a time combination by checking:
        1. No overlapping meetings on the same day
        2. Sufficient overlap between different days
        Returns True if the combination is valid.
        """
        for i, t1 in enumerate(time_combination):
            for j, t2 in enumerate(time_combination):
                if i != j:
                    # Check for same-day overlaps
                    if t1.day == t2.day:
                        if (
                            t1.start < t2.start + t2.duration
                            and t2.start < t1.start + t1.duration
                        ):
                            return False
                    # Check for sufficient overlap between different days
                    else:
                        t1_start = t1.start.value
                        t1_end = t1_start + t1.duration.value
                        t2_start = t2.start.value
                        t2_end = t2_start + t2.duration.value

                        overlap_start = max(t1_start, t2_start)
                        overlap_end = min(t1_end, t2_end)
                        overlap_minutes = overlap_end - overlap_start

                        if overlap_minutes < min_overlap:
                            return False
        return True

    def _has_matching_start_times(self, time_combination: List[TimeInstance]) -> bool:
        """Check if at least two meetings start at the same time."""
        if len(time_combination) < 2:
            return True
        start_times = Counter(t.start.value for t in time_combination)
        return max(start_times.values()) >= 2

    @lru_cache(maxsize=1024)
    def time_slots(self, credits: int, *, min_overlap: int = 45) -> list[TimeSlot]:

        # Find matching class patterns for the requested credits
        matching_patterns = [
            p for p in self.config.classes if p.credits == credits and not p.disabled
        ]
        if not matching_patterns:
            return []

        result = []
        for pattern in matching_patterns:
            # Generate all possible time slots for each meeting in the pattern
            meeting_slots = []
            for meeting in pattern.meetings:
                day_slots = self._generate_day_slots(
                    day=meeting.day,
                    duration=meeting.duration,
                    time_blocks=self.config.times.get(meeting.day, []),
                    start_time=pattern.start_time,
                )
                meeting_slots.append(day_slots)

            # Generate and validate all possible combinations
            for time_combination in product(*meeting_slots):
                # Skip if there are same-day overlaps or insufficient overlap between days
                if not self._validate_time_combination(time_combination, min_overlap):
                    continue

                # Skip if there aren't at least two meetings starting at the same time
                if not self._has_matching_start_times(time_combination):
                    continue

                # Find lab index if any
                lab_index = None
                for i, meeting in enumerate(pattern.meetings):
                    if meeting.lab:
                        lab_index = i
                        break

                # Create TimeSlot with this combination
                result.append(
                    TimeSlot(times=list(time_combination), lab_index=lab_index)
                )

        return result


class Scheduler:
    _init_lock = threading.Lock()

    def __init__(self, config: SchedulerConfig, time_slots_config_file: str):
        """
        Initialize the scheduler.

        Args:
            config: Configuration object containing courses, faculty, rooms, and labs
            time_slots_config_file: Path to the time slots configuration file
        """
        with self._init_lock:
            self._ctx = z3.Context()

            # Configure Z3 to use parallel solving with advanced optimization parameters
            z3.set_param("parallel.enable", True)
            z3.set_param("parallel.threads.max", 8)  # Reduced from 16 for efficiency

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
            z3.set_param("auto_config", False)  # Disable auto-config for performance

            # Enhanced cache for simplification and precomputed values
            self._simplify_cache = {}
            self._slot_relationship_cache = {}

            # Create faculty instances first
            self.faculty_instances: Dict[str, Faculty] = dict()
            self.faculty_maximum_credits: Dict[str, int] = dict()
            self.faculty_minimum_credits: Dict[str, int] = dict()
            self.faculty_unique_course_limits: Dict[str, int] = dict()
            self.faculty_preferences: Dict[str, Dict[str, int]] = dict()

            self._min_ids: Dict[type, int] = dict()
            self._max_ids: Dict[type, int] = dict()

            self._min_ids[Faculty] = Faculty.max_id() + 1
            for faculty_data in config.faculty:
                faculty_name = faculty_data.name
                self.faculty_instances[faculty_name] = Faculty(name=faculty_name)
                self.faculty_maximum_credits[faculty_name] = (
                    faculty_data.maximum_credits
                )
                self.faculty_minimum_credits[faculty_name] = (
                    faculty_data.minimum_credits
                )
                self.faculty_unique_course_limits[faculty_name] = (
                    faculty_data.unique_course_limit
                )
                self.faculty_preferences[faculty_name] = faculty_data.preferences
            self._max_ids[Faculty] = Faculty.max_id() + 1

            self._min_ids[Room] = Room.max_id() + 1
            self.rooms: Dict[str, Room] = dict((r, Room(name=r)) for r in config.rooms)
            self._max_ids[Room] = Room.max_id()

            self._min_ids[Lab] = Lab.max_id() + 1
            self.labs: Dict[str, Lab] = dict(
                (lab, Lab(name=lab)) for lab in config.labs
            )
            self._max_ids[Lab] = Lab.max_id()

            self.courses: List[Course] = []

            required_credits = set()
            for c in config.courses:
                required_credits.add(c.credits)
                course_faculty = c.faculty
                if not course_faculty:
                    for faculty_data in config.faculty:
                        if c.course_id in faculty_data.preferences:
                            course_faculty.append(faculty_data.name)

                self.courses.append(
                    Course(
                        credits=c.credits,
                        course_id=c.course_id,
                        labs=c.lab,
                        rooms=c.room,
                        conflicts=c.conflicts,
                        faculties=course_faculty,
                        ctx=self._ctx,
                    )
                )

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
                        result.append(
                            TimeInstance(day=day, start=start_time, duration=duration)
                        )
                return result

            self.faculty_availability: dict[str, List[TimeInstance]] = {
                faculty_data.name: get_info(faculty_data)
                for faculty_data in config.faculty
            }

            def generate_slots() -> Tuple[Dict[int, Tuple[int, int]], List[TimeSlot]]:
                ranges: Dict[int, Tuple[int, int]] = dict()
                slots: List[TimeSlot] = list()
                low = TimeSlot.min_id()
                # Only generate slots for credits actually needed
                time_slot_config = TimeSlotConfiguration(time_slots_config_file)

                for creds in sorted(required_credits):
                    for s in time_slot_config.time_slots(creds):
                        slots.append(s)
                    high = TimeSlot.max_id()
                    ranges[creds] = (low, high)
                    low = TimeSlot.max_id() + 1
                return ranges, slots

            ranges, slots = generate_slots()
            self.ranges = ranges
            self.slots = slots

            self._min_ids[TimeSlot] = min(c[0] for c in self.ranges.values())
            self._max_ids[TimeSlot] = max(c[1] for c in self.ranges.values())

            self.constraints, self.soft_constraints = self._build()

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

    def _z3ify_time_constraint(
        self, name: str
    ) -> Tuple[z3.Function, List[z3.ArithRef]]:
        z3fn = z3.Function(
            name,
            z3.IntSort(ctx=self._ctx),
            z3.IntSort(ctx=self._ctx),
            z3.BoolSort(ctx=self._ctx),
        )

        true = [(slot.id, slot.id) for slot in self.slots]
        false = []
        for slot_i, slot_j in itertools.combinations(self.slots, 2):
            if self._cached_slot_relationship(name, slot_i, slot_j):
                true.extend([(slot_i.id, slot_j.id), (slot_j.id, slot_i.id)])
            else:
                false.extend([(slot_i.id, slot_j.id), (slot_j.id, slot_i.id)])

        constraints = []
        constraints.append(z3.And([z3fn(sid_i, sid_j) for sid_i, sid_j in true]))
        constraints.append(
            z3.And([z3.Not(z3fn(sid_i, sid_j)) for sid_i, sid_j in false])
        )

        return z3fn, constraints

    def _z3ify_time_slot_fn(
        self, name: str, fn: Callable[[TimeSlot], bool]
    ) -> Tuple[z3.Function, List[z3.ArithRef]]:
        z3fn = z3.Function(name, z3.IntSort(ctx=self._ctx), z3.BoolSort(ctx=self._ctx))

        true = []
        false = []
        for slot in self.slots:
            if fn(slot):
                true.append(slot.id)
            else:
                false.append(slot.id)

        constraints = []
        constraints.append(z3.And([z3fn(slot_id) for slot_id in true]))
        constraints.append(z3.And([z3.Not(z3fn(slot_id)) for slot_id in false]))
        return z3fn, constraints

    def _z3ify_faculty_time_constraint(
        self, name: str
    ) -> Tuple[z3.Function, List[z3.ArithRef]]:
        z3fn = z3.Function(
            name,
            z3.IntSort(ctx=self._ctx),
            z3.IntSort(ctx=self._ctx),
            z3.BoolSort(ctx=self._ctx),
        )

        availability = {}
        for faculty_name, faculty in self.faculty_instances.items():
            faculty_times = self.faculty_availability[faculty_name]
            availability[faculty_name] = {
                slot.id: slot.in_time_ranges(faculty_times) for slot in self.slots
            }

        constraints = []
        for faculty_name, faculty in self.faculty_instances.items():
            true = []
            false = []
            faculty_id = faculty.id
            for slot in self.slots:
                slot_id = slot.id
                if availability[faculty_name][slot_id]:
                    true.append((faculty_id, slot_id))
                else:
                    false.append((faculty_id, slot_id))
            if true:
                constraints.append(
                    z3.And([z3fn(faculty_id, slot_id) for faculty_id, slot_id in true])
                )
            if false:
                constraints.append(
                    z3.And(
                        [
                            z3.Not(z3fn(faculty_id, slot_id))
                            for faculty_id, slot_id in false
                        ]
                    )
                )

        return z3fn, constraints

    def _build(self):
        # abstract function constraints
        overlaps, overlaps_C = self._z3ify_time_constraint("overlaps")
        lab_overlaps, lab_overlaps_C = self._z3ify_time_constraint("lab_overlaps")
        next_to, next_to_C = self._z3ify_time_constraint("next_to")
        not_next_to, not_next_to_C = self._z3ify_time_constraint("not_next_to")
        faculty_available, faculty_available_C = self._z3ify_faculty_time_constraint(
            "faculty_available"
        )

        fn_constraints = (
            overlaps_C
            + lab_overlaps_C
            + next_to_C
            + not_next_to_C
            + faculty_available_C
        )

        logger.debug(f"Added {len(fn_constraints)} function constraints")

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
                    faculty_constraints.append(
                        z3.And(
                            z3.PbGe(mapping, min_credits), z3.PbLe(mapping, max_credits)
                        )
                    )

                    # Unique course limit constraint - only generate if needed
                    unique_limit = self.faculty_unique_course_limits[faculty_name]

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
                                z3.Or([c.faculty() == faculty.id for c in course_group])
                            )
                        limit = self._simplify(
                            z3.PbLe([(tc, 1) for tc in teaches_course], unique_limit)
                        )
                        faculty_constraints.append(limit)

            # Yield faculty constraints in batch
            for c in faculty_constraints:
                yield self._simplify(c)

            # Course constraints with optimized conflict checking - batch generation
            course_constraints = []
            for c in self.courses:
                conflict_constraints = []
                for d in self.courses:
                    if d != c and d.course_id in c.conflicts:
                        conflict_constraints.append(
                            z3.Not(overlaps(c.time(), d.time()))
                        )

                course_constraint_list = []

                start, stop = self.ranges[c.credits]
                # basic timeslot constraint - allow all slots for this credit level
                if stop >= start:
                    course_constraint_list.append(
                        z3.And(
                            start <= c.time(),
                            c.time() <= stop,
                        )
                    )
                if c.labs:
                    # we must assign to a lab when we have options
                    course_constraint_list.append(
                        z3.And(
                            self._min_ids[Lab] <= c.lab(),
                            c.lab() <= self._max_ids[Lab],
                            z3.Or(
                                [
                                    c.lab() == lab.id
                                    for name, lab in self.labs.items()
                                    if name in c.labs
                                ]
                            ),
                        )
                    )
                if c.rooms:
                    # we must assign to a room when we have options
                    course_constraint_list.append(
                        z3.And(
                            self._min_ids[Room] <= c.room(),
                            c.room() <= self._max_ids[Room],
                            z3.Or(
                                [
                                    c.room() == room.id
                                    for name, room in self.rooms.items()
                                    if name in c.rooms
                                ]
                            ),
                        )
                    )
                if c.faculties:
                    # we must assign to a faculty from the candidates
                    course_constraint_list.append(
                        z3.And(
                            self._min_ids[Faculty] <= c.faculty(),
                            c.faculty() <= self._max_ids[Faculty],
                            z3.Or(
                                [
                                    c.faculty() == faculty.id
                                    for name, faculty in self.faculty_instances.items()
                                    if name in c.faculties
                                ]
                            ),
                        )
                    )
                if conflict_constraints:
                    course_constraint_list.append(z3.And(conflict_constraints))

                # check the faculty time constraint - ensure assigned faculty is available at assigned time
                course_constraint_list.append(faculty_available(c.faculty(), c.time()))
                course_constraints.append(z3.And(course_constraint_list))

            for c in course_constraints:
                yield self._simplify(c)

            # Faculty-specific constraints - ALL course pairs must be checked for faculty overlap
            course_pairs = list(itertools.combinations(self.courses, 2))
            resource_constraints = []

            for i, j in course_pairs:

                resource = []
                constraint_parts = []

                # Enforce same room usage when both courses can use the same rooms
                if set(i.rooms) & set(j.rooms):
                    resource.append(
                        z3.Implies(
                            i.room() == j.room(),
                            z3.Not(overlaps(i.time(), j.time())),
                        )
                    )
                    if i.course_id == j.course_id:
                        constraint_parts.append(i.room() == j.room())

                # Enforce same lab usage when both courses have labs and can use the same labs
                if set(i.labs) & set(j.labs):
                    resource.append(
                        z3.Implies(
                            i.lab() == j.lab(),
                            z3.Not(lab_overlaps(i.time(), j.time())),
                        )
                    )
                    if i.course_id == j.course_id:
                        constraint_parts.append(i.lab() == j.lab())

                # Prevent time overlap for courses taught by same faculty
                constraint_parts.append(
                    z3.And(
                        z3.Not(overlaps(i.time(), j.time())),
                        z3.If(
                            i.course_id == j.course_id,
                            next_to(i.time(), j.time()),
                            not_next_to(i.time(), j.time()),
                        ),
                    )
                )

                resource_constraints.append(
                    z3.And(
                        *resource,
                        z3.Implies(
                            i.faculty() == j.faculty(), z3.And(constraint_parts)
                        ),
                    )
                )

            # Yield resource constraints in batch
            for constraint in resource_constraints:
                yield self._simplify(constraint)

        # Generate constraints without excessive simplification
        C = list(hard_constraints())
        logger.debug(f"Added {len(C)} hard constraints")

        hard = fn_constraints + C

        return hard, []

    def _update(self, s: z3.Optimize):
        m: z3.ModelRef = s.model()
        constraints = []

        @dataclass
        class ModelAssignment:
            time: z3.ArithRef
            faculty: z3.ArithRef
            lab: z3.ArithRef
            room: z3.ArithRef

        def get_course_assignments(course: Course) -> ModelAssignment:
            """Get the actual assignments for a course from the model."""
            return ModelAssignment(
                time=m[course.time()],
                faculty=m[course.faculty()],
                lab=m[course.lab()],
                room=m[course.room()],
            )

        rearranged = []
        per_course = []
        # group courses by faculty first
        for _, group in itertools.groupby(self.courses, key=lambda x: m[x.faculty()]):
            group = list(group)
            for _, cs in itertools.groupby(group, key=lambda x: x.course_id):
                cs = list(cs)
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
            logger.debug(
                f"Adding 1 course rearrangement constraint with {len(rearranged)} predicates"
            )
            s.add(z3.And(rearranged))
        if per_course:
            logger.debug(
                f"Adding 1 per-course constraint with {len(per_course)} predicates"
            )
            s.add(z3.Or(per_course))

    def get_models(self, limit=10, optimize=True):
        s = z3.Optimize(ctx=self._ctx)

        # Optimized solver configuration for faster solving
        s.set("timeout", 300000)  # Increased to 5 minutes
        s.set("maxsat_engine", "wmax")  # Use MaxRes engine for optimization
        s.set("priority", "lex")  # Lexicographic priority for multiple objectives
        s.set("opt.enable_sat", True)  # Enable SAT solver optimization
        s.set("opt.enable_core_rotate", False)  # Disable expensive core rotation
        s.set("opt.enable_lns", False)  # Disable local neighborhood search for speed
        s.set("opt.maxres.hill_climb", True)
        s.set("opt.maxres.max_num_cores", 32)  # Reduced core generation
        s.set("opt.maxres.max_core_size", 8)  # Smaller core size for faster processing
        s.set("opt.maxres.pivot_on_correction_set", False)  # Disable for speed
        s.set("opt.maxres.add_upper_bound_block", True)  # Better bounds

        for c in self.constraints:
            s.add(c)

        # Add faculty preferences as optimization goals with improved caching - only if requested
        if optimize:
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
                logger.debug(
                    f"Adding {total_preferences} faculty preference optimization goals",
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
                    s.maximize(z3.Sum(preference_terms))

            same_rooms = []
            for i, j in itertools.combinations(self.courses, 2):
                if set(i.rooms) & set(j.rooms):
                    same_rooms.append(
                        z3.If(
                            z3.And(i.faculty() == j.faculty(), i.room() == j.room()),
                            1,
                            0,
                        )
                    )
            if same_rooms:
                logger.debug(f"Adding {len(same_rooms)} same room optimization goals")
                s.maximize(z3.Sum(same_rooms))

            same_labs = []
            for i, j in itertools.combinations(self.courses, 2):
                if set(i.labs) & set(j.labs):
                    same_labs.append(
                        z3.If(
                            z3.And(i.faculty() == j.faculty(), i.lab() == j.lab()), 1, 0
                        )
                    )
            if same_labs:
                logger.debug(f"Adding {len(same_labs)} same lab optimization goals")
                s.maximize(z3.Sum(same_labs))

            logger.info("Created all optimization goals")
        else:
            logger.info(
                "Skipping optimization goals",
            )

        for i in range(limit):
            if s.check() == z3.sat:
                yield s.model()
                self._update(s)
                i += 1
            else:
                if i == 0:
                    logger.error("No solution found")
                else:
                    logger.warning("No more solutions found")
                break


class CSVWriter:
    """Writer class for CSV output with consistent interface."""

    def __init__(self, filename: str = None):
        self.filename = filename
        self.schedules = []

    def __enter__(self):
        return self

    def add_schedule(self, courses: List[Course], model: z3.ModelRef) -> None:
        """Add a schedule to be written."""
        schedule_data = "\n".join(c.instance(model).csv() for c in courses)
        if self.filename:
            self.schedules.append(schedule_data)
        else:
            click.echo(schedule_data)

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        """Write all accumulated schedules."""
        if self.filename:
            content = "\n\n".join(self.schedules)
            with open(self.filename, "w", encoding="utf-8") as f:
                f.write(content)
            click.echo(f"CSV output written to {self.filename}")


class JSONWriter:
    """Writer class for JSON output with consistent interface."""

    def __init__(self, filename: str = None):
        self.filename = filename
        self.schedules = []

    def __enter__(self):
        return self

    def add_schedule(self, courses: List[Course], model: z3.ModelRef) -> None:
        """Add a schedule to be written."""

        schedule_data = [c.instance(model) for c in courses]
        if self.filename:
            self.schedules.append(schedule_data)
        else:
            click.echo(json.dumps(schedule_data, separators=(",", ":")))

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        """Write all accumulated schedules as one JSON array."""
        if self.filename:
            content = json.dumps(self.schedules, separators=(",", ":"))
            with open(self.filename, "w", encoding="utf-8") as f:
                f.write(content)
            click.echo(f"JSON output written to {self.filename}")


def _get_writer(format: str, output_file: str) -> JSONWriter | CSVWriter:
    if format == "json":
        return JSONWriter(output_file)
    else:
        return CSVWriter(output_file)


@click.command()
@click.argument("config", type=click.Path(exists=True), required=True)
@click.option(
    "--timeslot-config",
    "-t",
    type=click.Path(exists=True),
    default="time_slots.json",
    help="Path to the time slot configuration file",
)
@click.option("--limit", "-l", default=10, help="Maximum number of models to generate")
@click.option(
    "--format",
    "-f",
    type=click.Choice(["csv", "json"]),
    default="csv",
    help="Output format",
)
@click.option("--output", "-o", help="Output basename (extension added automatically)")
@click.option(
    "--optimize",
    "-O",
    is_flag=True,
    help="Enable optimization of preferences (slower)",
)
def main(
    config: str,
    timeslot_config: str,
    limit: int,
    format: str,
    output: str,
    optimize: bool,
):
    """Generate course schedules using constraint satisfaction solving."""

    logger.info(f"Using limit={limit}, optimize={optimize}")
    config = load_from_file(config)

    sched = Scheduler(config, timeslot_config)
    logger.info("Created all constraints")

    # Determine output filename
    output_file = f"{output}.{format}" if output else None

    # Create appropriate writer
    with _get_writer(format, output_file) as writer:
        for i, m in enumerate(sched.get_models(limit, optimize)):
            logger.info(f"Model {i + 1} generated")
            writer.add_schedule(sched.courses, m)

            # For interactive mode (no output file), prompt user
            if not output and i + 1 < limit:
                if not click.confirm("Generate next model?", default=True):
                    break


if __name__ == "__main__":
    main()
