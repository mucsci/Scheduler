"""Normalized, solver-independent scheduling problem representation."""

from collections import defaultdict
from dataclasses import dataclass, field

from .config import CombinedConfig, CourseModality, FacultyConfig, OptimizerFlags
from .configuration import _configuration_fingerprint
from .models import Course, Day, TimeInstance, TimePoint, TimeSlot
from .time_slot_generator import TimeSlotGenerator


def get_faculty_availability(faculty_config: FacultyConfig) -> list[TimeInstance]:
    """Expand one faculty configuration into normalized availability intervals.

    Args:
        faculty_config: Validated faculty policy containing weekday time ranges.

    Returns:
        Time instances in deterministic weekday and configured-range order.

    Raises:
        ValueError: If a time string cannot be parsed into hour and minute components.

    Behavior:
        Iterates every scheduler weekday, converts each configured range into a
        start point plus duration, and omits weekdays without availability.
    """
    result: list[TimeInstance] = []
    for day in Day:
        for time_range in faculty_config.times.get(day.name, []):
            start_hour, start_minute = map(int, time_range.start.split(":"))
            end_hour, end_minute = map(int, time_range.end.split(":"))
            start_time = TimePoint.make_from(start_hour, start_minute)
            end_time = TimePoint.make_from(end_hour, end_minute)
            result.append(
                TimeInstance(
                    day=day,
                    start=start_time,
                    duration=end_time - start_time,
                )
            )
    return result


@dataclass(frozen=True)
class FacultyPolicy:
    """Normalized workload, availability, and preference policy for one faculty member.

    Fields:
        name: Unique faculty label.
        minimum_credits: Required minimum assigned credits.
        maximum_credits: Allowed maximum assigned credits.
        maximum_days: Allowed maximum number of teaching weekdays.
        unique_course_limit: Allowed number of distinct course identifiers.
        mandatory_days: Weekdays on which this faculty must teach.
        availability: Normalized intervals in which assignments may occur.
        course_preferences: Course preference scores keyed by course identifier.
        room_preferences: Room preference scores keyed by room label.
        lab_preferences: Lab preference scores keyed by lab label.
        config_path: JSON Pointer to the source faculty configuration.
    """

    name: str
    minimum_credits: int
    maximum_credits: int
    maximum_days: int
    unique_course_limit: int
    mandatory_days: frozenset[Day]
    availability: tuple[TimeInstance, ...]
    course_preferences: dict[str, int]
    room_preferences: dict[str, int]
    lab_preferences: dict[str, int]
    config_path: str


@dataclass(frozen=True)
class ResourcePolicy:
    """Normalized capacity and provenance for one physical resource.

    Fields:
        kind: Resource category, either ``room`` or ``lab``.
        name: Stable configured name used by references and solver symbols.
        capacity: Maximum student capacity of the resource.
        features: Immutable facility/equipment feature tags.
        availability: Optional normalized availability; null means unrestricted.
        config_path: JSON Pointer to the source resource configuration.
    """

    kind: str
    name: str
    capacity: int
    features: frozenset[str]
    availability: tuple[TimeInstance, ...] | None
    config_path: str


@dataclass(frozen=True)
class CoursePolicy:
    """Normalized, immutable eligibility and provenance policy for one course section.

    Fields:
        name: Display identifier including the generated section number.
        course_id: Base configured course identifier.
        section: One-based section number among matching course identifiers.
        credits: Credit value used to select meeting-pattern domains.
        capacity: Expected enrollment that assigned resources must accommodate.
        section_id: Explicit section suffix, when configured.
        modality: Required delivery-mode composition.
        labs: Eligible labs; empty means the course has no lab meeting.
        rooms: Eligible rooms.
        conflicts: Base course identifiers that must not overlap.
        faculties: Eligible faculty after explicit or preference-derived resolution.
        config_path: JSON Pointer to the source course configuration.
        faculty_origin: Whether faculty eligibility was configured or derived.
        required_room_features: Features required on the assigned room.
        required_lab_features: Features required on every assigned lab.
        reserve_room_during_lab: Whether the lab meeting occupies the lecture room.
    """

    name: str
    course_id: str
    section: int
    credits: int
    capacity: int
    section_id: str | None
    modality: str
    labs: tuple[str, ...]
    rooms: tuple[str, ...]
    conflicts: tuple[str, ...]
    faculties: tuple[str, ...]
    config_path: str
    faculty_origin: str
    required_room_features: frozenset[str]
    required_lab_features: frozenset[str]
    reserve_room_during_lab: bool


@dataclass
class SchedulingProblem:
    """All normalized scheduling data shared by solving, diagnostics, and auditing.

    Fields:
        full_config: Original validated combined configuration.
        courses: Compatibility course objects containing normalized public schedule metadata.
        course_policies: Immutable normalized course policies keyed by display name.
        faculty: Faculty labels in configuration order.
        faculty_policies: Normalized faculty policies keyed by name.
        rooms: Global room labels in configuration order.
        labs: Global lab labels in configuration order.
        room_policies: Normalized room policies keyed by name.
        lab_policies: Normalized lab policies keyed by name.
        slots: Generated time-slot domain across required credit values.
        slot_ranges: Inclusive slot-index range for each credit value.
        course_config_paths: Course display names mapped to source JSON Pointers.
        course_faculty_origins: Course display names mapped to faculty derivation mode.
        optimizer_flags: Enabled optimization objectives as supplied; the solver registers them in fixed order.
        limit: Maximum number of schedules requested by the caller.
    """

    full_config: CombinedConfig
    courses: list[Course]
    course_policies: dict[str, CoursePolicy]
    faculty: list[str]
    faculty_policies: dict[str, FacultyPolicy]
    rooms: list[str]
    labs: list[str]
    room_policies: dict[str, ResourcePolicy]
    lab_policies: dict[str, ResourcePolicy]
    slots: list[TimeSlot]
    slot_ranges: dict[int, tuple[int, int]]
    course_config_paths: dict[str, str]
    course_faculty_origins: dict[str, str]
    optimizer_flags: list[OptimizerFlags]
    limit: int
    _compatible_slots_by_course: dict[str, tuple[TimeSlot, ...]] = field(default_factory=dict)

    @classmethod
    def from_config(cls, full_config: CombinedConfig) -> "SchedulingProblem":
        """Normalize validated configuration without constructing any Z3 objects.

        Args:
            full_config: Validated scheduler, time-slot, limit, and optimizer configuration.

        Returns:
            A normalized problem with policies, provenance paths, and time domains.

        Raises:
            pydantic.ValidationError: If a caller bypassed assignment validation
                and mutated the supplied configuration into an invalid state.
            ValueError: If a configured time value cannot be normalized.

        Behavior:
            Preserves configuration ordering, assigns deterministic section numbers,
            derives only explicitly-null faculty lists from preferences, generates
            slot ranges once per required credit value, and copies mutable inputs.
        """
        full_config = CombinedConfig.model_validate(full_config.model_dump(mode="python"))
        config = full_config.config

        def resource_availability(resource) -> tuple[TimeInstance, ...] | None:
            if resource.times is None:
                return None
            instances: list[TimeInstance] = []
            for day in Day:
                for time_range in resource.times.get(day.name, []):
                    start_hour, start_minute = map(int, time_range.start.split(":"))
                    end_hour, end_minute = map(int, time_range.end.split(":"))
                    start = TimePoint.make_from(start_hour, start_minute)
                    end = TimePoint.make_from(end_hour, end_minute)
                    instances.append(TimeInstance(day=day, start=start, duration=end - start))
            return tuple(instances)

        room_policies = {
            room.name: ResourcePolicy(
                kind="room",
                name=room.name,
                capacity=room.capacity,
                features=frozenset(room.features),
                availability=resource_availability(room),
                config_path=f"/config/rooms/{index}",
            )
            for index, room in enumerate(config.rooms)
        }
        lab_policies = {
            lab.name: ResourcePolicy(
                kind="lab",
                name=lab.name,
                capacity=lab.capacity,
                features=frozenset(lab.features),
                availability=resource_availability(lab),
                config_path=f"/config/labs/{index}",
            )
            for index, lab in enumerate(config.labs)
        }
        faculty_policies: dict[str, FacultyPolicy] = {}
        faculty_names: list[str] = []
        for index, faculty_config in enumerate(config.faculty):
            name = faculty_config.name
            faculty_names.append(name)
            faculty_policies[name] = FacultyPolicy(
                name=name,
                minimum_credits=faculty_config.minimum_credits,
                maximum_credits=faculty_config.maximum_credits,
                maximum_days=faculty_config.maximum_days,
                unique_course_limit=faculty_config.unique_course_limit,
                mandatory_days=frozenset(
                    Day[day] if isinstance(day, str) else day for day in faculty_config.mandatory_days
                ),
                availability=tuple(get_faculty_availability(faculty_config)),
                course_preferences=dict(faculty_config.course_preferences),
                room_preferences=dict(faculty_config.room_preferences),
                lab_preferences=dict(faculty_config.lab_preferences),
                config_path=f"/config/faculty/{index}",
            )

        courses: list[Course] = []
        required_credits: set[int] = set()
        course_counts: dict[str, int] = defaultdict(int)
        course_config_paths: dict[str, str] = {}
        course_faculty_origins: dict[str, str] = {}
        course_policies: dict[str, CoursePolicy] = {}
        for index, course_config in enumerate(config.courses):
            course_counts[course_config.course_id] += 1
            required_credits.add(course_config.credits)
            course_faculty = (
                list(course_config.faculty)
                if course_config.faculty is not None
                else [
                    policy.name
                    for policy in faculty_policies.values()
                    if course_config.course_id in policy.course_preferences
                ]
            )
            course = Course(
                credits=course_config.credits,
                capacity=course_config.capacity,
                course_id=course_config.course_id,
                section=course_counts[course_config.course_id],
                labs=list(course_config.lab),
                rooms=list(course_config.room),
                conflicts=list(course_config.conflicts),
                faculties=course_faculty,
                section_id=course_config.section_id,
                modality=course_config.modality.value,
                required_room_features=frozenset(course_config.required_room_features),
                required_lab_features=frozenset(course_config.required_lab_features),
                reserve_room_during_lab=course_config.reserve_room_during_lab,
            )
            courses.append(course)
            course_config_paths[str(course)] = f"/config/courses/{index}"
            course_faculty_origins[str(course)] = (
                "derived_from_preferences" if course_config.faculty is None else "configured"
            )
            course_policies[str(course)] = CoursePolicy(
                name=str(course),
                course_id=course.course_id,
                section=course.section,
                credits=course.credits,
                capacity=course.capacity,
                section_id=course.section_id,
                modality=course.modality,
                labs=tuple(course.labs),
                rooms=tuple(course.rooms),
                conflicts=tuple(course.conflicts),
                faculties=tuple(course.faculties),
                config_path=course_config_paths[str(course)],
                faculty_origin=course_faculty_origins[str(course)],
                required_room_features=course.required_room_features,
                required_lab_features=course.required_lab_features,
                reserve_room_during_lab=course.reserve_room_during_lab,
            )

        generator = TimeSlotGenerator(full_config.time_slot_config)
        slots: list[TimeSlot] = []
        slot_ranges: dict[int, tuple[int, int]] = {}
        for credits in sorted(required_credits):
            low = len(slots)
            slots.extend(generator.time_slots(credits))
            slot_ranges[credits] = (low, len(slots) - 1)

        problem = cls(
            full_config=full_config,
            courses=courses,
            course_policies=course_policies,
            faculty=faculty_names,
            faculty_policies=faculty_policies,
            rooms=list(room_policies),
            labs=list(lab_policies),
            room_policies=room_policies,
            lab_policies=lab_policies,
            slots=slots,
            slot_ranges=slot_ranges,
            course_config_paths=course_config_paths,
            course_faculty_origins=course_faculty_origins,
            optimizer_flags=list(full_config.optimizer_flags),
            limit=full_config.limit,
        )
        return problem

    def compatible_slots(self, course: Course) -> tuple[TimeSlot, ...]:
        """Return the cached time domain matching all course pattern requirements.

        Args:
            course: Normalized course whose compatible domain is requested.

        Returns:
            An immutable tuple of slots with matching credits, lab presence,
            modality, and lecture-room occupancy requirements.

        Raises:
            KeyError: If the course credit value has no generated slot range.

        Behavior:
            Computes a course domain on first access, preserves global slot ordering,
            caches it by section display name, and returns the same tuple thereafter.
        """
        course_name = str(course)
        cached = self._compatible_slots_by_course.get(course_name)
        if cached is not None:
            return cached
        start, stop = self.slot_ranges[course.credits]
        compatible = tuple(
            slot
            for index, slot in enumerate(self.slots)
            if start <= index <= stop
            and slot.has_lab() == bool(course.labs)
            and self._slot_modality(slot) == course.modality
            and (
                bool(course.rooms)
                or not self._slot_requires_room(slot, reserve_room_during_lab=course.reserve_room_during_lab)
            )
        )
        self._compatible_slots_by_course[course_name] = compatible
        return compatible

    @staticmethod
    def _slot_modality(slot: TimeSlot) -> str:
        modes = {time.delivery for time in slot.times}
        if modes == {"in_person"}:
            return CourseModality.IN_PERSON.value
        if modes == {"online"}:
            return CourseModality.ONLINE.value
        return CourseModality.HYBRID.value

    @staticmethod
    def _slot_requires_room(slot: TimeSlot, *, reserve_room_during_lab: bool) -> bool:
        if slot.physical_lecture_times():
            return True
        return reserve_room_during_lab and slot.lab_time() is not None

    def configuration_fingerprint(self) -> str:
        """Calculate the stable fingerprint used by diagnostic responses.

        Args:
            None.

        Returns:
            Lowercase SHA-256 hex digest of canonical JSON configuration data.

        Raises:
            TypeError: If an unexpected configuration value is not JSON serializable.

        Behavior:
            Serializes the original validated configuration with sorted keys and
            compact separators so equivalent payloads produce identical identities.
        """
        return _configuration_fingerprint(self.full_config)
