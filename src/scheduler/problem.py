"""Normalized, solver-independent scheduling problem representation."""

import hashlib
import json
from collections import defaultdict
from dataclasses import dataclass, field

from .config import CombinedConfig, FacultyConfig, OptimizerFlags
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
class CoursePolicy:
    """Normalized, immutable eligibility and provenance policy for one course section.

    Fields:
        name: Display identifier including the generated section number.
        course_id: Base configured course identifier.
        section: One-based section number among matching course identifiers.
        credits: Credit value used to select meeting-pattern domains.
        labs: Eligible labs; empty means the course has no lab meeting.
        rooms: Eligible rooms.
        conflicts: Base course identifiers that must not overlap.
        faculties: Eligible faculty after explicit or preference-derived resolution.
        config_path: JSON Pointer to the source course configuration.
        faculty_origin: Whether faculty eligibility was configured or derived.
    """

    name: str
    course_id: str
    section: int
    credits: int
    labs: tuple[str, ...]
    rooms: tuple[str, ...]
    conflicts: tuple[str, ...]
    faculties: tuple[str, ...]
    config_path: str
    faculty_origin: str


@dataclass
class SchedulingProblem:
    """All normalized scheduling data shared by solving, diagnostics, and auditing.

    Fields:
        full_config: Original validated combined configuration.
        courses: Compatibility course objects populated with solver mirrors later.
        course_policies: Immutable normalized course policies keyed by display name.
        faculty: Faculty labels in configuration order.
        faculty_policies: Normalized faculty policies keyed by name.
        rooms: Global room labels in configuration order.
        labs: Global lab labels in configuration order.
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
            ValueError: If a configured time value cannot be normalized.

        Behavior:
            Preserves configuration ordering, assigns deterministic section numbers,
            derives only explicitly-null faculty lists from preferences, generates
            slot ranges once per required credit value, and copies mutable inputs.
        """
        config = full_config.config
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
                course_id=course_config.course_id,
                section=course_counts[course_config.course_id],
                labs=list(course_config.lab),
                rooms=list(course_config.room),
                conflicts=list(course_config.conflicts),
                faculties=course_faculty,
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
                labs=tuple(course.labs),
                rooms=tuple(course.rooms),
                conflicts=tuple(course.conflicts),
                faculties=tuple(course.faculties),
                config_path=course_config_paths[str(course)],
                faculty_origin=course_faculty_origins[str(course)],
            )

        generator = TimeSlotGenerator(full_config.time_slot_config)
        slots: list[TimeSlot] = []
        slot_ranges: dict[int, tuple[int, int]] = {}
        for credits in sorted(required_credits):
            low = len(slots)
            slots.extend(generator.time_slots(credits))
            slot_ranges[credits] = (low, len(slots) - 1)

        return cls(
            full_config=full_config,
            courses=courses,
            course_policies=course_policies,
            faculty=faculty_names,
            faculty_policies=faculty_policies,
            rooms=list(config.rooms),
            labs=list(config.labs),
            slots=slots,
            slot_ranges=slot_ranges,
            course_config_paths=course_config_paths,
            course_faculty_origins=course_faculty_origins,
            optimizer_flags=list(full_config.optimizer_flags),
            limit=full_config.limit,
        )

    def compatible_slots(self, course: Course) -> tuple[TimeSlot, ...]:
        """Return the cached time domain matching a course's credits and lab semantics.

        Args:
            course: Normalized course whose compatible domain is requested.

        Returns:
            An immutable tuple of slots with matching credits and lab presence.

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
            if start <= index <= stop and slot.has_lab() == bool(course.labs)
        )
        self._compatible_slots_by_course[course_name] = compatible
        return compatible

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
        payload = json.dumps(self.full_config.model_dump(mode="json"), sort_keys=True, separators=(",", ":"))
        return hashlib.sha256(payload.encode()).hexdigest()
