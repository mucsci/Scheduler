"""Independent schedule validation, summaries, and objective scoring."""

import itertools
from collections import defaultdict

from .config import OptimizerFlags
from .contracts import (
    ConstraintDiagnostic,
    FacultyWorkloadDiagnostic,
    ObjectiveScoreDiagnostic,
    ResourceUsageDiagnostic,
    ScheduleAudit,
)
from .models import Course, CourseInstance, Day, TimeSlot
from .problem import SchedulingProblem


class ScheduleAuditor:
    """Audit decoded schedules without consulting a Z3 model."""

    def __init__(self, problem: SchedulingProblem):
        self._problem = problem
        self._optimizer_flags = problem.optimizer_flags
        self._faculty = problem.faculty
        self._courses = problem.courses
        self._course_config_paths = problem.course_config_paths
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
        return self._problem.compatible_slots(course)

    def audit_schedule(self, schedule: list["CourseInstance"]) -> ScheduleAudit:
        """Independently audit one emitted schedule and explain its soft scores.

        Args:
            schedule: Decoded assignments expected to cover every configured course.

        Returns:
            Independent hard-rule findings, workload and resource summaries, and
            scores and explanations for every enabled objective.

        Raises:
            KeyError: If a preference-enabled assignment names unknown faculty.

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
