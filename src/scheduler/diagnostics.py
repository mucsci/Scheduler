"""Feasibility diagnostics, provenance, unsat cores, and verified repairs."""

import itertools
import time
from collections import defaultdict
from collections.abc import Callable
from typing import Literal

import z3

from .contracts import (
    CandidateDomainDiagnostic,
    CapacityDiagnostic,
    ConstraintDiagnostic,
    DayFeasibilityDiagnostic,
    ProvenanceEdge,
    RelaxationSuggestion,
    RepairSetDiagnostic,
    ScheduleDiagnosis,
)
from .models import Course, Day, TimeInstance, TimeSlot
from .problem import SchedulingProblem
from .solver import DiagnosticConstraintArtifact, SolverArtifacts

MAX_REJECTED_PATTERN_DIAGNOSTICS = 128
MAX_RESOURCE_CAPACITY_REJECTION_DIAGNOSTICS = 128
MAX_PAIR_PATTERN_COMPARISONS = 4_096


class DiagnosticEngine:
    """Explain feasibility using normalized data and immutable solver artifacts."""

    def __init__(
        self,
        problem: SchedulingProblem,
        artifacts: SolverArtifacts,
        *,
        solver_timeout_ms: int | None = None,
    ):
        self._problem = problem
        self._solver_timeout_ms = solver_timeout_ms
        self._ctx = artifacts.context
        self._function_data = artifacts.relations
        self._diagnostic_constraints = artifacts.diagnostic_constraints
        self._faculty = problem.faculty
        self._courses = problem.courses
        self._slots = problem.slots
        self._ranges = problem.slot_ranges
        self._course_config_paths = problem.course_config_paths
        self._course_faculty_origins = problem.course_faculty_origins
        self._courses_by_name = {str(course): course for course in self._courses}
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
        self._faculty_minimum_credits = {name: policy.minimum_credits for name, policy in policies.items()}
        self._faculty_unique_course_limits = {name: policy.unique_course_limit for name, policy in policies.items()}
        self._faculty_mandatory_days = {name: set(policy.mandatory_days) for name, policy in policies.items()}
        self._faculty_availability = {name: list(policy.availability) for name, policy in policies.items()}

    def diagnose(self) -> ScheduleDiagnosis:
        """Explain hard-constraint feasibility without running soft objectives.

        Args:
            None.

        Returns:
            A complete public diagnosis containing status, static analyses,
            provenance, and bounded core and repair data when unsatisfiable.

        Raises:
            z3.Z3Exception: If Z3 cannot create or execute a feasibility solver.

        Behavior:
            Checks tracked hard rules, subset-minimizes an UNSAT core, performs
            bounded alternative-core and repair searches, derives supporting facts
            and relaxations, and always records timing, timeout, and completeness.
        """
        started_at = time.perf_counter()
        status, conflicts, core_indexes, reason = self._diagnostic_core()
        core_is_minimal: bool | None = None
        if status == "unsatisfiable":
            conflicts, core_indexes, core_is_minimal = self._minimize_core(core_indexes)
        candidate_domains = self._candidate_domains()
        capacity_analysis = self._capacity_analysis()
        day_feasibility = self._day_feasibility()
        preflight_findings = self._preflight_findings(candidate_domains, capacity_analysis)
        if status == "unsatisfiable":
            alternatives, alternatives_complete = self._alternative_cores(core_indexes)
            repair_sets, repair_sets_complete = self._repair_sets()
            supporting_facts = self._supporting_facts(conflicts)
            suggestions = self._relaxation_suggestions(conflicts, supporting_facts)
            provenance = self._provenance(candidate_domains, conflicts)
            elapsed_ms = round((time.perf_counter() - started_at) * 1000)
            return ScheduleDiagnosis(
                status=status,
                conflicting_constraints=conflicts,
                alternative_conflict_sets=alternatives,
                supporting_facts=supporting_facts,
                relaxation_suggestions=suggestions,
                repair_sets=repair_sets,
                candidate_domains=candidate_domains,
                capacity_analysis=capacity_analysis,
                day_feasibility=day_feasibility,
                preflight_findings=preflight_findings,
                provenance=provenance,
                configuration_fingerprint=self._configuration_fingerprint(),
                core_is_minimal=core_is_minimal,
                alternative_cores_complete=alternatives_complete,
                repair_sets_complete=repair_sets_complete,
                diagnostic_completeness="bounded_unsat_cores",
                elapsed_ms=elapsed_ms,
                solver_timeout_ms=self._solver_timeout_ms,
            )
        provenance = self._provenance(candidate_domains, ())
        elapsed_ms = round((time.perf_counter() - started_at) * 1000)
        return ScheduleDiagnosis(
            status=status,
            candidate_domains=candidate_domains,
            capacity_analysis=capacity_analysis,
            day_feasibility=day_feasibility,
            preflight_findings=preflight_findings,
            provenance=provenance,
            configuration_fingerprint=self._configuration_fingerprint(),
            diagnostic_completeness="preflight_only" if status == "unknown" else "hard_constraint_feasibility",
            elapsed_ms=elapsed_ms,
            solver_timeout_ms=self._solver_timeout_ms,
            reason=reason,
        )

    def _configuration_fingerprint(self) -> str:
        """Return a stable, non-secret identity for the diagnostic input."""
        return self._problem.configuration_fingerprint()

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
            "course_room_capacity_shortfall": "capacity",
            "course_room_candidate_capacity": "capacity",
            "course_room_features": "required_room_features",
            "course_room_feature_shortfall": "required_room_features",
            "course_room_availability": "room",
            "course_room_resource_shortfall": "room",
            "course_faculty_eligibility": "faculty",
            "course_lab_capacity": "capacity",
            "course_lab_capacity_shortfall": "capacity",
            "course_lab_candidate_capacity": "capacity",
            "course_lab_features": "required_lab_features",
            "course_lab_feature_shortfall": "required_lab_features",
            "course_lab_availability": "lab",
            "course_lab_resource_shortfall": "lab",
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
            if subject in self._room_config_paths and "room" in kind and "capacity" in kind:
                locations.append(self._room_config_paths[subject] + "/capacity")
            if subject in self._room_config_paths and "room" in kind and "feature" in kind:
                locations.append(self._room_config_paths[subject] + "/features")
            if subject in self._room_config_paths and "room" in kind and "availability" in kind:
                locations.append(self._room_config_paths[subject] + "/times")
            if subject in self._lab_config_paths and "lab" in kind and "capacity" in kind:
                locations.append(self._lab_config_paths[subject] + "/capacity")
            if subject in self._lab_config_paths and "lab" in kind and "feature" in kind:
                locations.append(self._lab_config_paths[subject] + "/features")
            if subject in self._lab_config_paths and "lab" in kind and "availability" in kind:
                locations.append(self._lab_config_paths[subject] + "/times")
        if kind in {"course_room_capacity", "course_room_capacity_shortfall"} and subjects:
            course = self._courses_by_name.get(subjects[0])
            if course is not None:
                locations.extend(self._room_config_paths[room] + "/capacity" for room in course.rooms)
        if kind in {"course_lab_capacity", "course_lab_capacity_shortfall"} and subjects:
            course = self._courses_by_name.get(subjects[0])
            if course is not None:
                locations.extend(self._lab_config_paths[lab] + "/capacity" for lab in course.labs)
        if kind in {"course_room_features", "course_room_feature_shortfall"} and subjects:
            course = self._courses_by_name.get(subjects[0])
            if course is not None:
                locations.extend(self._room_config_paths[room] + "/features" for room in course.rooms)
        if kind in {"course_lab_features", "course_lab_feature_shortfall"} and subjects:
            course = self._courses_by_name.get(subjects[0])
            if course is not None:
                locations.extend(self._lab_config_paths[lab] + "/features" for lab in course.labs)
        if kind == "course_room_availability" and subjects:
            course = self._courses_by_name.get(subjects[0])
            if course is not None:
                locations.extend(self._room_config_paths[room] + "/times" for room in course.rooms)
        if kind == "course_lab_availability" and subjects:
            course = self._courses_by_name.get(subjects[0])
            if course is not None:
                locations.extend(self._lab_config_paths[lab] + "/times" for lab in course.labs)
        if kind == "course_room_resource_shortfall" and subjects:
            course = self._courses_by_name.get(subjects[0])
            if course is not None:
                locations.extend(
                    self._room_config_paths[room] + suffix
                    for room in course.rooms
                    for suffix in ("/capacity", "/features", "/times")
                )
        if kind == "course_lab_resource_shortfall" and subjects:
            course = self._courses_by_name.get(subjects[0])
            if course is not None:
                locations.extend(
                    self._lab_config_paths[lab] + suffix
                    for lab in course.labs
                    for suffix in ("/capacity", "/features", "/times")
                )
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

    def _lab_time_available(self, slot: TimeSlot, availability: tuple[TimeInstance, ...] | None) -> bool:
        lab_time = slot.lab_time()
        return lab_time is not None and self._times_available((lab_time,), availability)

    @staticmethod
    def _room_times(course: Course, slot: TimeSlot) -> tuple[TimeInstance, ...]:
        """Return meetings that occupy the course's lecture room for one slot."""
        times = list(slot.physical_lecture_times())
        lab_time = slot.lab_time()
        if course.reserve_room_during_lab and lab_time is not None:
            times.append(lab_time)
        return tuple(times)

    @staticmethod
    def _meetings_overlap(left: tuple[TimeInstance, ...], right: tuple[TimeInstance, ...]) -> bool:
        """Return whether any two meetings in the supplied occupancy sets overlap."""
        return any(TimeSlot._overlaps(first, second) for first in left for second in right)

    def _room_is_required_for_all_patterns(self, course: Course) -> bool:
        """Return whether every compatible pattern requires a lecture room."""
        compatible_slots = self._compatible_slots(course)
        return bool(compatible_slots) and all(
            self._problem._slot_requires_room(
                slot,
                reserve_room_during_lab=course.reserve_room_during_lab,
            )
            for slot in compatible_slots
        )

    @staticmethod
    def _any_pattern_pair(
        first_slots: tuple[TimeSlot, ...],
        second_slots: tuple[TimeSlot, ...],
        predicate: Callable[[TimeSlot, TimeSlot], bool],
    ) -> bool | None:
        """Return a witness for a pair relation, or ``None`` if the safe scan cap is reached."""
        total = len(first_slots) * len(second_slots)
        for comparisons, (first, second) in enumerate(itertools.product(first_slots, second_slots), start=1):
            if predicate(first, second):
                return True
            if comparisons >= MAX_PAIR_PATTERN_COMPARISONS and comparisons < total:
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
                if slot not in credit_slots:
                    reason = "credit count"
                elif slot.has_lab() != bool(course.labs):
                    reason = "lab requirement"
                elif self._problem._slot_modality(slot) != course.modality:
                    reason = "delivery modality"
                else:
                    reason = "lecture-room occupancy"
                rejected_patterns.append(
                    self._make_diagnostic(
                        "rejected_time_pattern",
                        (str(course),),
                        f"Course {course} rejects pattern {slot} because its {reason} does not match",
                    )
                )
            compatible_rooms = tuple(room for room in course.rooms if self._room_capacities[room] >= course.capacity)
            compatible_labs = tuple(lab for lab in course.labs if self._lab_capacities[lab] >= course.capacity)
            feature_compatible_rooms = tuple(
                room for room in course.rooms if course.required_room_features <= self._room_features[room]
            )
            feature_compatible_labs = tuple(
                lab for lab in course.labs if course.required_lab_features <= self._lab_features[lab]
            )
            rejected_rooms = [room for room in course.rooms if room not in compatible_rooms]
            rejected_labs = [lab for lab in course.labs if lab not in compatible_labs]
            room_capacity_rejections = tuple(
                self._make_diagnostic(
                    "course_room_candidate_capacity",
                    (str(course), room),
                    f"Room {room} has capacity {self._room_capacities[room]}, below course {course}'s "
                    f"required capacity {course.capacity}",
                )
                for room in rejected_rooms[:MAX_RESOURCE_CAPACITY_REJECTION_DIAGNOSTICS]
            )
            lab_capacity_rejections = tuple(
                self._make_diagnostic(
                    "course_lab_candidate_capacity",
                    (str(course), lab),
                    f"Lab {lab} has capacity {self._lab_capacities[lab]}, below course {course}'s "
                    f"required capacity {course.capacity}",
                )
                for lab in rejected_labs[:MAX_RESOURCE_CAPACITY_REJECTION_DIAGNOSTICS]
            )
            domains.append(
                CandidateDomainDiagnostic(
                    course=str(course),
                    locations=(self._course_config_paths[str(course)],),
                    faculty_candidates=tuple(course.faculties),
                    faculty_origin=self._course_faculty_origins[str(course)],
                    room_candidates=tuple(course.rooms),
                    lab_candidates=tuple(course.labs),
                    section_capacity=course.capacity,
                    capacity_compatible_room_candidates=compatible_rooms,
                    capacity_compatible_lab_candidates=compatible_labs,
                    room_capacity_rejections=room_capacity_rejections,
                    room_capacity_rejection_count=len(rejected_rooms),
                    room_capacity_rejections_truncated=len(rejected_rooms) > len(room_capacity_rejections),
                    lab_capacity_rejections=lab_capacity_rejections,
                    lab_capacity_rejection_count=len(rejected_labs),
                    lab_capacity_rejections_truncated=len(rejected_labs) > len(lab_capacity_rejections),
                    compatible_time_patterns=tuple(map(str, compatible_slots)),
                    availability_by_faculty=tuple(availability),
                    rejected_patterns=tuple(rejected_patterns),
                    rejected_pattern_count=rejected_pattern_count,
                    rejected_patterns_truncated=rejected_pattern_count > len(rejected_patterns),
                    modality=course.modality,
                    required_room_features=tuple(sorted(course.required_room_features)),
                    required_lab_features=tuple(sorted(course.required_lab_features)),
                    feature_compatible_room_candidates=feature_compatible_rooms,
                    feature_compatible_lab_candidates=feature_compatible_labs,
                    reserve_room_during_lab=course.reserve_room_during_lab,
                )
            )
        return tuple(domains)

    def _capacity_analysis(self) -> tuple[CapacityDiagnostic, ...]:
        """Evaluate cheap necessary conditions and forced-resource bottlenecks."""
        diagnostics: list[CapacityDiagnostic] = []
        for course in self._courses:
            if course.rooms and self._room_is_required_for_all_patterns(course):
                diagnostics.append(
                    CapacityDiagnostic(
                        kind="course_room_capacity_coverage",
                        subjects=(str(course), *course.rooms),
                        message=f"Largest allowed room capacity available to course {course}",
                        required=course.capacity,
                        available=max(self._room_capacities[room] for room in course.rooms),
                        locations=(
                            self._course_config_paths[str(course)] + "/capacity",
                            *(self._room_config_paths[room] + "/capacity" for room in course.rooms),
                        ),
                    )
                )
            if course.labs:
                diagnostics.append(
                    CapacityDiagnostic(
                        kind="course_lab_capacity_coverage",
                        subjects=(str(course), *course.labs),
                        message=f"Largest allowed lab capacity available to course {course}",
                        required=course.capacity,
                        available=max(self._lab_capacities[lab] for lab in course.labs),
                        locations=(
                            self._course_config_paths[str(course)] + "/capacity",
                            *(self._lab_config_paths[lab] + "/capacity" for lab in course.labs),
                        ),
                    )
                )
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
            for mandatory_day in sorted(self._faculty_mandatory_days[faculty]):
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
            if (
                first.rooms == second.rooms
                and len(first.rooms) == 1
                and self._room_is_required_for_all_patterns(first)
                and self._room_is_required_for_all_patterns(second)
            ):
                requirements.append(
                    (
                        "forced_shared_room_separation",
                        self._any_pattern_pair(
                            first_slots,
                            second_slots,
                            lambda left, right, first_course=first, second_course=second: (
                                not self._meetings_overlap(
                                    self._room_times(first_course, left),
                                    self._room_times(second_course, right),
                                )
                            ),
                        ),
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
                room_candidate_is_forced = resource_kind != "room" or self._room_is_required_for_all_patterns(course)
                if len(candidates) == 1 and len(compatible_slots) == 1 and room_candidate_is_forced:
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
            course = self._courses_by_name[domain.course]
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
            room_is_required = self._room_is_required_for_all_patterns(course)
            if room_is_required and not domain.feature_compatible_room_candidates:
                findings.append(
                    self._make_diagnostic(
                        "course_room_feature_shortfall",
                        (domain.course, *course.rooms),
                        f"No allowed room provides all features required by {domain.course}: "
                        f"{sorted(course.required_room_features)}",
                    )
                )
            if course.labs and not domain.feature_compatible_lab_candidates:
                findings.append(
                    self._make_diagnostic(
                        "course_lab_feature_shortfall",
                        (domain.course, *course.labs),
                        f"No allowed lab provides all features required by {domain.course}: "
                        f"{sorted(course.required_lab_features)}",
                    )
                )

            compatible_slots = self._compatible_slots(course)
            if room_is_required and not any(
                self._room_capacities[room] >= course.capacity
                and course.required_room_features <= self._room_features[room]
                and any(
                    self._times_available(
                        self._room_times(course, slot),
                        self._room_availability[room],
                    )
                    for slot in compatible_slots
                )
                for room in course.rooms
            ):
                findings.append(
                    self._make_diagnostic(
                        "course_room_resource_shortfall",
                        (domain.course, *course.rooms),
                        "No allowed room simultaneously satisfies capacity, features, and availability for "
                        f"{domain.course}",
                    )
                )
            if course.labs and not any(
                self._lab_capacities[lab] >= course.capacity
                and course.required_lab_features <= self._lab_features[lab]
                and any(self._lab_time_available(slot, self._lab_availability[lab]) for slot in compatible_slots)
                for lab in course.labs
            ):
                findings.append(
                    self._make_diagnostic(
                        "course_lab_resource_shortfall",
                        (domain.course, *course.labs),
                        f"No allowed lab simultaneously satisfies capacity, features, and availability for "
                        f"{domain.course}",
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
                finding_kind = {
                    "course_room_capacity_coverage": "course_room_capacity_shortfall",
                    "course_lab_capacity_coverage": "course_lab_capacity_shortfall",
                }.get(capacity.kind, "capacity_shortfall")
                findings.append(
                    self._make_diagnostic(
                        finding_kind,
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
                    source=course_path + "/required_room_features",
                    target=f"candidate-domain:{domain.course}",
                    relationship="filters_room_features",
                    subjects=(domain.course,),
                )
            )
            edges.append(
                ProvenanceEdge(
                    source=course_path + "/required_lab_features",
                    target=f"candidate-domain:{domain.course}",
                    relationship="filters_lab_features",
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
            edges.append(
                ProvenanceEdge(
                    source=course_path + "/capacity",
                    target=f"candidate-domain:{domain.course}",
                    relationship="defines_section_capacity",
                    subjects=(domain.course,),
                )
            )
            compatible_rooms = set(domain.capacity_compatible_room_candidates)
            for room in domain.room_candidates:
                edges.append(
                    ProvenanceEdge(
                        source=self._room_config_paths[room] + "/capacity",
                        target=f"candidate:{domain.course}:room:{room}",
                        relationship=(
                            "satisfies_section_capacity" if room in compatible_rooms else "below_section_capacity"
                        ),
                        subjects=(domain.course, room),
                    )
                )
                edges.append(
                    ProvenanceEdge(
                        source=self._room_config_paths[room] + "/features",
                        target=f"candidate:{domain.course}:room:{room}",
                        relationship=(
                            "satisfies_required_features"
                            if room in domain.feature_compatible_room_candidates
                            else "missing_required_features"
                        ),
                        subjects=(domain.course, room),
                    )
                )
                edges.append(
                    ProvenanceEdge(
                        source=self._room_config_paths[room] + "/times",
                        target=f"candidate:{domain.course}:room:{room}",
                        relationship="defines_resource_availability",
                        subjects=(domain.course, room),
                    )
                )
            compatible_labs = set(domain.capacity_compatible_lab_candidates)
            for lab in domain.lab_candidates:
                edges.append(
                    ProvenanceEdge(
                        source=self._lab_config_paths[lab] + "/capacity",
                        target=f"candidate:{domain.course}:lab:{lab}",
                        relationship=(
                            "satisfies_section_capacity" if lab in compatible_labs else "below_section_capacity"
                        ),
                        subjects=(domain.course, lab),
                    )
                )
                edges.append(
                    ProvenanceEdge(
                        source=self._lab_config_paths[lab] + "/features",
                        target=f"candidate:{domain.course}:lab:{lab}",
                        relationship=(
                            "satisfies_required_features"
                            if lab in domain.feature_compatible_lab_candidates
                            else "missing_required_features"
                        ),
                        subjects=(domain.course, lab),
                    )
                )
                edges.append(
                    ProvenanceEdge(
                        source=self._lab_config_paths[lab] + "/times",
                        target=f"candidate:{domain.course}:lab:{lab}",
                        relationship="defines_resource_availability",
                        subjects=(domain.course, lab),
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
    ) -> tuple[
        Literal["satisfiable", "unsatisfiable", "unknown"],
        tuple[ConstraintDiagnostic, ...],
        frozenset[int],
        str | None,
    ]:
        """Return one labeled unsat core, optionally relaxing selected tracked rules."""
        solver = z3.Solver(ctx=self._ctx)
        if self._solver_timeout_ms is not None:
            solver.set(timeout=self._solver_timeout_ms)

        # Generated function tables are required for correctness, but they are
        # implementation details rather than useful user-facing explanations.
        solver.add(self._function_data.constraints)
        tracked_constraints: dict[str, tuple[int, DiagnosticConstraintArtifact]] = {}
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

    def _minimize_core(
        self,
        core_indexes: frozenset[int],
    ) -> tuple[tuple[ConstraintDiagnostic, ...], frozenset[int], bool]:
        """Shrink a solver-provided core to a subset-minimal business-rule core."""
        active = set(core_indexes)
        complete = True
        for index in tuple(sorted(active)):
            candidate = frozenset(active - {index})
            status, _core, _indexes, _reason = self._diagnostic_core(active_indexes=candidate)
            if status == "unsatisfiable":
                active.remove(index)
            elif status == "unknown":
                complete = False
        minimized = frozenset(active)
        constraints = tuple(
            self._make_diagnostic(
                self._diagnostic_constraints[index].kind,
                self._diagnostic_constraints[index].subjects,
                self._diagnostic_constraints[index].message,
            )
            for index in sorted(minimized)
        )
        return constraints, minimized, complete

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
        pending = [frozenset({index}) for index in sorted(primary_core_indexes)]
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
            minimized_core, minimized_indexes, minimized_completely = self._minimize_core(core_indexes)
            if not minimized_completely:
                complete = False
                continue
            if minimized_indexes in seen:
                continue
            seen.add(minimized_indexes)
            alternatives.append(minimized_core)
            for index in sorted(minimized_indexes):
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
            for index in sorted(core_indexes):
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

            if len(course.rooms) == 1 and self._room_is_required_for_all_patterns(course):
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

            if any(
                diagnostic.kind == "course_room_capacity" and diagnostic.subjects[0] == str(course)
                for diagnostic in conflicts
            ):
                for room in course.rooms:
                    facts.append(
                        ConstraintDiagnostic(
                            kind="course_room_candidate_capacity",
                            subjects=(str(course), room),
                            message=(
                                f"Room {room} provides capacity {self._room_capacities[room]} for course {course}, "
                                f"which requires {course.capacity}"
                            ),
                        )
                    )
            if any(
                diagnostic.kind == "course_lab_capacity" and diagnostic.subjects[0] == str(course)
                for diagnostic in conflicts
            ):
                for lab in course.labs:
                    facts.append(
                        ConstraintDiagnostic(
                            kind="course_lab_candidate_capacity",
                            subjects=(str(course), lab),
                            message=(
                                f"Lab {lab} provides capacity {self._lab_capacities[lab]} for course "
                                f"{course}, which requires {course.capacity}"
                            ),
                        )
                    )

            compatible_patterns = self._compatible_slots(course)
            if len(compatible_patterns) == 1:
                facts.append(
                    ConstraintDiagnostic(
                        kind="forced_course_time_pattern",
                        subjects=(str(course),),
                        message=f"Course {course} has exactly one compatible meeting pattern",
                    )
                )

        for faculty in (name for name in self._faculty if name in constrained_faculty):
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
                    days = sorted({time.day.name for slot in self._compatible_slots(course) for time in slot.times})
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
                compatible = self._compatible_slots(course)
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
            elif conflict.kind in {"course_room_features", "course_lab_features"} and conflict.subjects:
                resource_kind = "room" if conflict.kind == "course_room_features" else "lab"
                course = self._courses_by_name[conflict.subjects[0]]
                required = (
                    sorted(course.required_room_features)
                    if resource_kind == "room"
                    else sorted(course.required_lab_features)
                )
                suggestions.append(
                    RelaxationSuggestion(
                        kind=f"provide_required_{resource_kind}_features",
                        subjects=conflict.subjects,
                        message=(
                            f"Add an allowed {resource_kind} providing {required}, add those features to an allowed "
                            f"resource, or remove requirements that are not essential"
                        ),
                    )
                )
            elif conflict.kind in {"course_room_availability", "course_lab_availability"} and conflict.subjects:
                resource_kind = "room" if conflict.kind == "course_room_availability" else "lab"
                suggestions.append(
                    RelaxationSuggestion(
                        kind=f"expand_{resource_kind}_availability",
                        subjects=conflict.subjects,
                        message=(
                            f"Expand an allowed {resource_kind}'s availability, add another available candidate, "
                            "or enable a compatible meeting pattern"
                        ),
                    )
                )
            elif conflict.kind in {"course_room_capacity", "course_lab_capacity"} and conflict.subjects:
                course_name = conflict.subjects[0]
                course = self._courses_by_name[course_name]
                resource_kind = "room" if conflict.kind == "course_room_capacity" else "lab"
                candidates = course.rooms if resource_kind == "room" else course.labs
                capacities = self._room_capacities if resource_kind == "room" else self._lab_capacities
                required_capacity = course.capacity
                suggestions.extend(
                    (
                        RelaxationSuggestion(
                            kind=f"add_capacity_compatible_{resource_kind}_candidate",
                            subjects=(course_name,),
                            message=(
                                f"Add an allowed {resource_kind} with capacity of at least {required_capacity} "
                                f"for course {course}"
                            ),
                        ),
                        RelaxationSuggestion(
                            kind=f"increase_{resource_kind}_capacity",
                            subjects=(course_name, *candidates),
                            message=(
                                f"Correct or increase an allowed {resource_kind}'s capacity to at least "
                                f"{required_capacity}; current capacities are "
                                + ", ".join(f"{name}={capacities[name]}" for name in candidates)
                            ),
                        ),
                        RelaxationSuggestion(
                            kind="reduce_section_capacity",
                            subjects=(course_name,),
                            message=(
                                f"Reduce the configured demand from {required_capacity} to no more than "
                                f"{max(capacities[name] for name in candidates)}"
                            ),
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
