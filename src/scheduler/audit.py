"""Independent schedule validation, summaries, and objective scoring."""

import itertools
from collections import defaultdict
from copy import deepcopy

from .config import OptimizerFlags
from .contracts import (
    ConstraintDiagnostic,
    FacultyWorkloadDiagnostic,
    ObjectiveScoreDiagnostic,
    ResourceUsageDiagnostic,
    ScheduleAudit,
)
from .models import Course, CourseInstance, Day, Duration, TimeInstance, TimeSlot
from .problem import SchedulingProblem


class ScheduleAuditor:
    """Audit decoded schedules without consulting a Z3 model."""

    def __init__(self, problem: SchedulingProblem):
        self._problem = problem
        self._optimizer_flags = problem.optimizer_flags
        self._faculty = problem.faculty
        self._courses = deepcopy(problem.courses)
        self._courses_by_name = {str(course): course for course in self._courses}
        self._max_time_gap = Duration(duration=problem.full_config.time_slot_config.max_time_gap)
        self._course_config_paths = problem.course_config_paths
        self._room_capacities = {name: policy.capacity for name, policy in problem.room_policies.items()}
        self._lab_capacities = {name: policy.capacity for name, policy in problem.lab_policies.items()}
        self._room_features = {name: policy.features for name, policy in problem.room_policies.items()}
        self._lab_features = {name: policy.features for name, policy in problem.lab_policies.items()}
        self._room_availability = {name: policy.availability for name, policy in problem.room_policies.items()}
        self._lab_availability = {name: policy.availability for name, policy in problem.lab_policies.items()}
        self._room_config_paths = {name: policy.config_path for name, policy in problem.room_policies.items()}
        self._lab_config_paths = {name: policy.config_path for name, policy in problem.lab_policies.items()}
        policies = problem.faculty_policies
        self._faculty_config_paths = {name: policy.config_path for name, policy in policies.items()}
        self._faculty_maximum_credits = {name: policy.maximum_credits for name, policy in policies.items()}
        self._faculty_maximum_days = {name: policy.maximum_days for name, policy in policies.items()}
        self._faculty_minimum_credits = {name: policy.minimum_credits for name, policy in policies.items()}
        self._faculty_unique_course_limits = {name: policy.unique_course_limit for name, policy in policies.items()}
        self._faculty_course_preferences = {name: policy.course_preferences for name, policy in policies.items()}
        self._faculty_room_preferences = {name: policy.room_preferences for name, policy in policies.items()}
        self._faculty_lab_preferences = {name: policy.lab_preferences for name, policy in policies.items()}
        self._faculty_mandatory_days = {name: set(policy.mandatory_days) for name, policy in policies.items()}
        self._faculty_availability = {name: list(policy.availability) for name, policy in policies.items()}

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
            "course_room_capacity": "capacity",
            "course_room_features": "required_room_features",
            "course_room_availability": "room",
            "course_faculty_eligibility": "faculty",
            "course_lab_capacity": "capacity",
            "course_lab_features": "required_lab_features",
            "course_lab_availability": "lab",
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
            if subject in self._room_config_paths and kind == "course_room_capacity":
                locations.append(self._room_config_paths[subject] + "/capacity")
            if subject in self._room_config_paths and kind == "course_room_features":
                locations.append(self._room_config_paths[subject] + "/features")
            if subject in self._room_config_paths and kind == "course_room_availability":
                locations.append(self._room_config_paths[subject] + "/times")
            if subject in self._lab_config_paths and kind == "course_lab_capacity":
                locations.append(self._lab_config_paths[subject] + "/capacity")
            if subject in self._lab_config_paths and kind == "course_lab_features":
                locations.append(self._lab_config_paths[subject] + "/features")
            if subject in self._lab_config_paths and kind == "course_lab_availability":
                locations.append(self._lab_config_paths[subject] + "/times")
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
        return self._problem.compatible_slots(course)

    @staticmethod
    def _times_available(times: tuple[TimeInstance, ...], availability: tuple[TimeInstance, ...] | None) -> bool:
        if availability is None:
            return True
        return all(
            any(
                meeting.day == window.day and window.start <= meeting.start and meeting.stop <= window.stop
                for window in availability
            )
            for meeting in times
        )

    def _room_times(self, instance: CourseInstance) -> tuple[TimeInstance, ...]:
        times = [
            time
            for index, time in enumerate(instance.time.times)
            if index != instance.time.lab_index and time.delivery == "in_person"
        ]
        lab_time = instance.time.lab_time()
        course = self._courses_by_name.get(str(instance.course))
        if course is not None and course.reserve_room_during_lab and lab_time is not None:
            times.append(lab_time)
        return tuple(times)

    @staticmethod
    def _meetings_next_to(
        left: tuple[TimeInstance, ...],
        right: tuple[TimeInstance, ...],
        max_time_gap,
    ) -> bool:
        """Return whether two physical occupancy sets contain an adjacent pair."""
        return any(TimeSlot._diff_between_slots(first, second) <= max_time_gap for first in left for second in right)

    def _labs_next_to(self, left: TimeSlot, right: TimeSlot) -> bool:
        """Reproduce configured lab adjacency without trusting decoded slot policy."""
        first = left.lab_time()
        second = right.lab_time()
        if first is None or second is None:
            return False
        if first.day != second.day:
            return (
                first.start < second.stop
                and second.start < first.stop
                and abs(first.start - second.start) <= self._max_time_gap
            )
        return TimeSlot._diff_between_slots(first, second) <= self._max_time_gap

    def audit_schedule(self, schedule: list["CourseInstance"]) -> ScheduleAudit:
        """Independently audit one emitted schedule and explain its soft scores.

        Args:
            schedule: Decoded assignments expected to cover every configured course.

        Returns:
            Independent hard-rule findings, workload and resource summaries, and
            scores and explanations for every enabled objective.

        Raises:
            None.

        Behavior:
            Reconstructs coverage by course name, validates every assignment and
            cross-course relation without consulting Z3, aggregates workload and
            collision data, then recalculates soft scores. This catches solver,
            decoding, serialization, and downstream-mutation errors.
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
            requires_room = self._problem._slot_requires_room(
                instance.time,
                reserve_room_during_lab=course.reserve_room_during_lab,
            )
            if (requires_room and instance.room not in course.rooms) or (
                not requires_room and instance.room is not None
            ):
                violations.append(
                    self._make_diagnostic(
                        "course_room_eligibility",
                        (str(course), str(instance.room)),
                        f"Course {course} is assigned ineligible room {instance.room}",
                    )
                )
            assigned_room = instance.room
            room_capacity = self._room_capacities.get(assigned_room) if assigned_room is not None else None
            if room_capacity is not None and room_capacity < course.capacity:
                assert assigned_room is not None
                violations.append(
                    self._make_diagnostic(
                        "course_room_capacity",
                        (str(course), assigned_room),
                        f"Course {course} requires capacity {course.capacity}, but room {assigned_room} "
                        f"has capacity {room_capacity}",
                    )
                )
            if assigned_room in self._room_features and not (
                course.required_room_features <= self._room_features[assigned_room]
            ):
                violations.append(
                    self._make_diagnostic(
                        "course_room_features",
                        (str(course), str(assigned_room)),
                        f"Room {assigned_room} does not provide all features required by {course}",
                    )
                )
            if assigned_room in self._room_availability and not self._times_available(
                self._room_times(instance), self._room_availability[assigned_room]
            ):
                violations.append(
                    self._make_diagnostic(
                        "course_room_availability",
                        (str(course), str(assigned_room)),
                        f"Course {course} falls outside room {assigned_room}'s availability",
                    )
                )

            assigned_lab = instance.lab
            if assigned_lab not in course.labs and not (assigned_lab is None and not course.labs):
                violations.append(
                    self._make_diagnostic(
                        "course_lab_eligibility",
                        (str(course), str(assigned_lab)),
                        f"Course {course} uses ineligible lab {assigned_lab}",
                    )
                )
            if assigned_lab in course.labs:
                lab_capacity = self._lab_capacities.get(assigned_lab)
                if lab_capacity is not None and lab_capacity < course.capacity:
                    violations.append(
                        self._make_diagnostic(
                            "course_lab_capacity",
                            (str(course), assigned_lab),
                            f"Course {course} requires {course.capacity} lab seats, but "
                            f"lab {assigned_lab} has {lab_capacity}",
                        )
                    )
                if assigned_lab in self._lab_features and not (
                    course.required_lab_features <= self._lab_features[assigned_lab]
                ):
                    violations.append(
                        self._make_diagnostic(
                            "course_lab_features",
                            (str(course), assigned_lab),
                            f"Lab {assigned_lab} does not provide all features required by {course}",
                        )
                    )
                lab_time = instance.time.lab_time()
                if (
                    lab_time is not None
                    and assigned_lab in self._lab_availability
                    and not self._times_available((lab_time,), self._lab_availability[assigned_lab])
                ):
                    violations.append(
                        self._make_diagnostic(
                            "course_lab_availability",
                            (str(course), assigned_lab),
                            f"Course {course} falls outside lab {assigned_lab}'s availability",
                        )
                    )

            if instance.time not in self._compatible_slots(course):
                violations.append(
                    self._make_diagnostic(
                        "course_time_pattern",
                        (str(course),),
                        f"Course {course} uses a meeting pattern incompatible with its credits, "
                        "modality, or lab requirement",
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
            canonical = [self._courses_by_name.get(str(instance.course)) for instance in assigned]
            credits = sum(course.credits for course in canonical if course is not None)
            days = tuple(sorted({time.day.name for instance in assigned for time in instance.time.times}))
            course_ids = {course.course_id for course in canonical if course is not None}
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
            for day in sorted(mandatory - {Day[day] for day in days}):
                violations.append(
                    self._make_diagnostic(
                        "faculty_mandatory_day",
                        (faculty, day.name),
                        f"Faculty {faculty} is not scheduled on mandatory day {day.name}",
                    )
                )

        usage: list[ResourceUsageDiagnostic] = []
        rooms: defaultdict[str, list[CourseInstance]] = defaultdict(list)
        for instance in schedule:
            if instance.room is not None:
                rooms[instance.room].append(instance)
        for resource, assignments in sorted(rooms.items()):
            collisions: list[ConstraintDiagnostic] = []
            for first, second in itertools.combinations(assignments, 2):
                if any(
                    TimeSlot._overlaps(left, right)
                    for left in self._room_times(first)
                    for right in self._room_times(second)
                ):
                    collisions.append(
                        self._make_diagnostic(
                            "shared_room_overlap",
                            (str(first.course), str(second.course), resource),
                            f"Courses {first.course} and {second.course} overlap while using room {resource}",
                        )
                    )
            usage.append(
                ResourceUsageDiagnostic(
                    kind="room",
                    resource=resource,
                    assignments=tuple(str(instance.course) for instance in assignments),
                    collisions=tuple(collisions),
                    capacity=self._room_capacities.get(resource),
                    maximum_assigned_section_capacity=max(
                        (
                            course.capacity
                            for instance in assignments
                            if (course := self._courses_by_name.get(str(instance.course))) is not None
                        ),
                        default=0,
                    ),
                    capacity_violations=tuple(
                        violation
                        for violation in violations
                        if violation.kind == "course_room_capacity" and resource in violation.subjects
                    ),
                )
            )
            violations.extend(collisions)

        labs: defaultdict[str, list[CourseInstance]] = defaultdict(list)
        for instance in schedule:
            if instance.lab is not None:
                labs[instance.lab].append(instance)
        for resource, assignments in sorted(labs.items()):
            collisions = []
            for first, second in itertools.combinations(assignments, 2):
                first_lab_time = first.time.lab_time()
                second_lab_time = second.time.lab_time()
                if (
                    first_lab_time is not None
                    and second_lab_time is not None
                    and TimeSlot._overlaps(first_lab_time, second_lab_time)
                ):
                    collisions.append(
                        self._make_diagnostic(
                            "shared_lab_overlap",
                            (str(first.course), str(second.course), resource),
                            f"Courses {first.course} and {second.course} overlap in lab {resource}",
                        )
                    )
            usage.append(
                ResourceUsageDiagnostic(
                    kind="lab",
                    resource=resource,
                    assignments=tuple(str(instance.course) for instance in assignments),
                    collisions=tuple(collisions),
                    capacity=self._lab_capacities.get(resource),
                    maximum_assigned_section_capacity=max(
                        (
                            course.capacity
                            for instance in assignments
                            if (course := self._courses_by_name.get(str(instance.course))) is not None
                        ),
                        default=0,
                    ),
                    capacity_violations=tuple(
                        violation
                        for violation in violations
                        if violation.kind == "course_lab_capacity" and resource in violation.subjects
                    ),
                )
            )
            violations.extend(collisions)

        for first, second in itertools.combinations(schedule, 2):
            left = self._courses_by_name.get(str(first.course))
            right = self._courses_by_name.get(str(second.course))
            if left is None or right is None:
                continue
            if (right.course_id in left.conflicts or left.course_id in right.conflicts) and first.time.overlaps(
                second.time
            ):
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
                if (
                    set(left.rooms) & set(right.rooms)
                    and first.room is not None
                    and second.room is not None
                    and first.room != second.room
                ):
                    violations.append(
                        self._make_diagnostic(
                            "same_course_room",
                            (str(left), str(right)),
                            f"Sections {left} and {right} taught by one faculty use different rooms",
                        )
                    )
                if set(left.labs) & set(right.labs) and first.lab != second.lab:
                    violations.append(
                        self._make_diagnostic(
                            "same_course_lab",
                            (str(left), str(right)),
                            f"Sections {left} and {right} taught by one faculty use different labs",
                        )
                    )
                if not self._meetings_next_to(
                    tuple(first.time.times),
                    tuple(second.time.times),
                    self._max_time_gap,
                ):
                    violations.append(
                        self._make_diagnostic(
                            "same_course_lecture_adjacency",
                            (str(left), str(right)),
                            f"Sections {left} and {right} taught by one faculty are not adjacent",
                        )
                    )
                if left.labs and right.labs and not self._labs_next_to(first.time, second.time):
                    violations.append(
                        self._make_diagnostic(
                            "same_course_lab_adjacency",
                            (str(left), str(right)),
                            f"Sections {left} and {right} taught by one faculty do not have adjacent labs",
                        )
                    )
            else:
                if self._meetings_next_to(
                    tuple(first.time.times),
                    tuple(second.time.times),
                    self._max_time_gap,
                ):
                    violations.append(
                        self._make_diagnostic(
                            "different_course_lecture_separation",
                            (str(left), str(right)),
                            f"Different courses {left} and {right} taught by one faculty are adjacent",
                        )
                    )
                if left.labs and right.labs and self._labs_next_to(first.time, second.time):
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
                course = self._courses_by_name.get(str(instance.course))
                if course is None:
                    continue
                preferences = (
                    self._faculty_course_preferences
                    if target == "course"
                    else self._faculty_room_preferences
                    if target == "room"
                    else self._faculty_lab_preferences
                )
                selected_value = course.course_id if target == "course" else getattr(instance, target)
                assigned = (
                    preferences.get(instance.faculty, {}).get(selected_value, 0) if selected_value is not None else 0
                )
                score += assigned
                candidate_values = (
                    (course.course_id,)
                    if target == "course"
                    else tuple(course.rooms)
                    if target == "room"
                    else tuple(course.labs)
                )
                potential = [
                    preferences.get(faculty, {}).get(value, 0)
                    for faculty in course.faculties
                    for value in candidate_values
                ]
                best = max(potential, default=0)
                upper_bound += best
                if assigned < best:
                    outcomes.append(
                        self._make_diagnostic(
                            "preference_not_selected",
                            (str(course), instance.faculty, objective),
                            f"Course {course} receives {assigned}/{best} "
                            f"available {objective} preference points; hard constraints or competing objectives "
                            "selected a lower-scoring eligible assignment",
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
                first_course = self._courses_by_name.get(str(first.course))
                second_course = self._courses_by_name.get(str(second.course))
                if first_course is None or second_course is None:
                    continue
                first_candidates = getattr(first_course, f"{resource}s")
                second_candidates = getattr(second_course, f"{resource}s")
                if not set(first_candidates) & set(second_candidates):
                    continue
                if resource == "room" and (
                    not any(
                        self._problem._slot_requires_room(
                            slot,
                            reserve_room_during_lab=first_course.reserve_room_during_lab,
                        )
                        for slot in self._compatible_slots(first_course)
                    )
                    or not any(
                        self._problem._slot_requires_room(
                            slot,
                            reserve_room_during_lab=second_course.reserve_room_during_lab,
                        )
                        for slot in self._compatible_slots(second_course)
                    )
                ):
                    continue
                if objective.startswith("pack_") and first_course.course_id == second_course.course_id:
                    continue
                if resource == "lab":
                    same_resource = first.lab == second.lab
                    satisfactions = [
                        first.faculty == second.faculty and same_resource
                        if objective == "same_lab"
                        else same_resource and self._labs_next_to(first.time, second.time)
                    ]
                else:
                    same_resource = first.room is not None and second.room is not None and first.room == second.room
                    satisfactions = [
                        first.faculty == second.faculty and same_resource
                        if objective == "same_room"
                        else same_resource
                        and self._meetings_next_to(
                            self._room_times(first),
                            self._room_times(second),
                            self._max_time_gap,
                        )
                    ]
                for satisfied in satisfactions:
                    upper_bound += 1
                    score += int(satisfied)
                    if not satisfied:
                        outcomes.append(
                            self._make_diagnostic(
                                "objective_pair_not_selected",
                                (str(first_course), str(second_course), objective),
                                f"Pair {first_course}/{second_course} does not receive the {objective} point; "
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
