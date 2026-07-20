from contextlib import contextmanager
from enum import StrEnum
from typing import Annotated, Literal

from pydantic import (
    BaseModel,
    ConfigDict,
    Field,
    PositiveInt,
    ValidationError,
    ValidationInfo,
    field_validator,
    model_validator,
)
from pydantic_core import InitErrorDetails, PydanticCustomError

type TimeString = Annotated[
    str,
    Field(
        pattern=r"^([0-1][0-9]|2[0-3]):[0-5][0-9]$",
        description="Time in HH:MM format",
        frozen=True,
        json_schema_extra={"example": "10:00"},
    ),
]
"""
TimeString is a string in the format of HH:MM.

**Usage:**
```python
from scheduler.config import TimeString
value: TimeString = "10:00"
```
"""

# TimeRangeString is a string in the format of HH:MM-HH:MM.
type TimeRangeString = Annotated[
    str,
    Field(
        pattern=r"^([0-1][0-9]|2[0-3]):[0-5][0-9]-([0-1][0-9]|2[0-3]):[0-5][0-9]$",
        description="Time range in HH:MM-HH:MM format",
        frozen=True,
        json_schema_extra={"example": "10:00-12:00"},
    ),
]

"""
TimeRangeString is a string in the format of HH:MM-HH:MM.

**Usage:**
```python
from scheduler.config import TimeRangeString
value: TimeRangeString = "10:00-12:00"
```
"""

# Preference is an integer score between 0 and 10.
type Preference = Annotated[
    int,
    Field(
        ge=0,
        le=10,
        description="Preference score between 0 and 10",
        json_schema_extra={"example": 5},
    ),
]

"""
Preference is an integer score between 0 and 10.

**Usage:**
```python
from scheduler.config import Preference
score: Preference = 5
```
"""

type Day = Annotated[
    Literal["MON", "TUE", "WED", "THU", "FRI"],
    Field(
        description="Day of the week",
        frozen=True,
        json_schema_extra={"example": "MON"},
    ),
]

"""
Day is a day of the week (must be one of: MON, TUE, WED, THU, FRI).

**Usage:**
```python
from scheduler.config import Day
d: Day = "MON"
```
"""

type Room = Annotated[
    str,
    Field(
        frozen=True,
        description="Room name",
        json_schema_extra={"example": "Room 101"},
    ),
]

"""
Room is a room name.

**Usage:**
```python
from scheduler.config import Room
r: Room = "Room 101"
```
"""

type Lab = Annotated[
    str,
    Field(
        frozen=True,
        description="Lab name",
        json_schema_extra={"example": "Lab 101"},
    ),
]

"""
Lab is a lab name.

**Usage:**
```python
from scheduler.config import Lab
lab: Lab = "Lab 101"
```
"""

type Course = Annotated[
    str,
    Field(
        frozen=True,
        description="Course name",
        json_schema_extra={"example": "CS 101"},
    ),
]

"""
Course is a course name.

**Usage:**
```python
from scheduler.config import Course
cid: Course = "CS 101"
```
"""

type Faculty = Annotated[
    str,
    Field(
        frozen=True,
        description="Faculty name",
        json_schema_extra={"example": "Dr. Smith"},
    ),
]

"""
Faculty is a faculty name.

**Usage:**
```python
from scheduler.config import Faculty
name: Faculty = "Dr. Smith"
```
"""


class StrictBaseModel(BaseModel):
    """
    Base class for all models which need strict validation.

    **Usage:**
    ```python
    class MyConfig(StrictBaseModel):
        ...
    ```

    **Fields:**
    - model_config: Configuration for the model
    """

    model_config = ConfigDict(extra="forbid", strict=True, validate_assignment=True)
    """
    Configuration for the model which forbids extra fields, is strict, and validates on assignment (@private)
    """

    @contextmanager
    def edit_mode(self):
        """
        Apply a group of configuration changes atomically after validation.

        Args:
            None. The context manager operates on this model instance.

        Returns:
            A context manager that yields a deep, independently editable copy of
            this model.

        Raises:
            ValidationError: If the edited copy does not satisfy the model's
                field or cross-field validation rules. The original model is
                unchanged when validation fails.

        Behavior:
            A deep copy is yielded so nested containers may be edited safely.
            When the context exits normally, the copy is reconstructed through
            the concrete model class to run all Pydantic validation. Only a
            successfully validated state is copied back to the original object;
            exceptions raised inside the context bypass the commit naturally.
        """
        # Create a working copy for editing
        working_copy = self.model_copy(deep=True)
        yield working_copy
        # Validate the working copy by creating a new instance
        try:
            validated_copy = self.__class__(**working_copy.model_dump())
            # If validation passes, update the original object
            self.__dict__.update(validated_copy.__dict__)
        except ValidationError as e:
            # Validation failed, rollback is automatic (working_copy is discarded)
            raise e


class TimeBlock(StrictBaseModel):
    """
    Represents a time block within a day.

    **Usage:**
    ```python
    TimeBlock(start="09:00", spacing=60, end="17:00")
    ```
    """

    start: TimeString = Field(description="Start time of the time block", json_schema_extra={"example": "10:00"})
    """
    Start time of the time block
    """

    spacing: PositiveInt = Field(description="Time spacing between slots in minutes", json_schema_extra={"example": 60})
    """
    Time spacing between slots in minutes
    """

    end: TimeString = Field(description="End time of the time block", json_schema_extra={"example": "17:00"})
    """
    End time of the time block
    """

    @model_validator(mode="after")
    def _validate_end_after_start(self):
        """
        Validate that the end time is after the start time.

        **Usage:**
        ```python
        TimeBlock(start="09:00", spacing=60, end="17:00")
        # end must be after start
        ```
        """
        start_minutes = int(self.start.split(":")[0]) * 60 + int(self.start.split(":")[1])
        end_minutes = int(self.end.split(":")[0]) * 60 + int(self.end.split(":")[1])
        if end_minutes <= start_minutes:
            raise ValueError("End time must be after start time")
        return self


class TimeRange(StrictBaseModel):
    """
    A time range with start and end times, ensuring start < end.

    **Usage:**
    ```python
    TimeRange(start="09:00", end="17:00")
    ```
    """

    start: TimeString = Field(description="Start time of the time range", json_schema_extra={"example": "10:00"})
    """
    Start time of the time range
    """
    end: TimeString = Field(description="End time of the time range", json_schema_extra={"example": "17:00"})
    """
    End time of the time range
    """

    @model_validator(mode="after")
    def _validate_end_after_start(self):
        """
        Validate that the end time is after the start time.

        **Usage:**
        ```python
        TimeRange(start="09:00", end="17:00")
        # end must be after start
        ```
        """
        start_minutes = int(self.start.split(":")[0]) * 60 + int(self.start.split(":")[1])
        end_minutes = int(self.end.split(":")[0]) * 60 + int(self.end.split(":")[1])
        if end_minutes <= start_minutes:
            raise ValueError("End time must be after start time")
        return self

    def __str__(self) -> str:
        return f"{self.start}-{self.end}"

    @classmethod
    def from_string(cls, time_range_str: TimeRangeString) -> "TimeRange":
        """
        Parse a compact clock range into a validated ``TimeRange`` instance.

        Args:
            time_range_str: Range expressed as ``HH:MM-HH:MM`` using 24-hour
                clock values.

        Returns:
            A validated instance whose ``start`` and ``end`` fields contain the
            two parsed clock strings.

        Raises:
            ValueError: If the input cannot be split into exactly two values,
                either clock value is invalid, or the end is not after the start.
            ValidationError: If construction fails Pydantic validation.

        Behavior:
            The value is split at the hyphen and passed through the normal model
            constructor. Parsing therefore uses exactly the same clock-format and
            ordering rules as configuration loaded from JSON.
        """
        start, end = time_range_str.split("-")
        return cls(start=start, end=end)


class DeliveryMode(StrEnum):
    """Delivery mode for one generated meeting."""

    IN_PERSON = "in_person"
    ONLINE = "online"


class CourseModality(StrEnum):
    """Required mixture of meeting delivery modes for a course section."""

    IN_PERSON = "in_person"
    ONLINE = "online"
    HYBRID = "hybrid"


class _ResourceConfig(StrictBaseModel):
    """Shared validated shape for a schedulable physical resource."""

    name: str = Field(
        min_length=1,
        description="Unique, nonblank resource name used by course references and schedule output",
    )
    """Unique resource name used by configuration references and generated schedules."""

    capacity: PositiveInt = Field(description="Maximum number of students the resource can accommodate")
    """Positive student capacity available to an assigned course section."""

    features: set[str] = Field(
        default_factory=set,
        description="Facility and equipment feature tags supplied by this resource",
    )
    """Feature tags available to course requirement matching."""

    times: dict[Day, list[TimeRange]] | None = Field(
        default=None,
        description="Optional weekday availability windows; null means unrestricted availability",
    )
    """Availability by weekday, or null when the resource is always available."""

    @field_validator("name")
    @classmethod
    def _validate_nonblank_name(cls, value: str) -> str:
        if not value.strip():
            raise ValueError("Resource name must not be blank")
        return value

    @field_validator("features", mode="before")
    @classmethod
    def _validate_features(cls, value):
        if not isinstance(value, list | tuple | set | frozenset):
            return value
        if any(not isinstance(feature, str) or not feature.strip() for feature in value):
            raise ValueError("Resource features must not be blank")
        return set(value)

    @field_validator("times", mode="before")
    @classmethod
    def _convert_time_strings(cls, value):
        if value is None or not isinstance(value, dict):
            return value
        return {
            day: [TimeRange.from_string(item) if isinstance(item, str) else item for item in ranges]
            for day, ranges in value.items()
        }


class RoomConfig(_ResourceConfig):
    """A lecture-room resource that can be assigned to physical course meetings.

    Fields:
        name: Unique, nonblank identifier used by course room candidates,
            faculty preferences, generated schedules, and diagnostics.
        capacity: Positive count of usable student seats. Physical assignments
            require a value at least as large as the course section capacity.
        features: Facility or equipment tags supplied by the room. A room is
            eligible only when it contains every feature required by the course.
        times: Optional availability windows for every scheduler weekday. ``None``
            means unrestricted availability; a mapping restricts occupancy to the
            listed windows.
    """

    name: str = Field(
        min_length=1,
        description="Unique, nonblank room name used by references and schedule output",
    )
    capacity: PositiveInt = Field(description="Maximum number of students the room can accommodate")
    features: set[str] = Field(
        default_factory=set,
        description="Facility and equipment feature tags supplied by this room",
    )
    times: dict[Day, list[TimeRange]] | None = Field(
        default=None,
        description="Optional weekday room availability windows; null means unrestricted availability",
    )


class LabConfig(_ResourceConfig):
    """A laboratory resource that can be assigned to a section's lab meeting.

    Fields:
        name: Unique, nonblank identifier used by course lab candidates, faculty
            preferences, generated schedules, and diagnostics.
        capacity: Positive count of usable student seats. Lab assignments require
            a value at least as large as the course section capacity.
        features: Facility or equipment tags supplied by the lab. A lab is
            eligible only when it contains every feature required by the course.
        times: Optional availability windows for every scheduler weekday. ``None``
            means unrestricted availability; a mapping restricts the lab meeting
            to the listed windows.
    """

    name: str = Field(
        min_length=1,
        description="Unique, nonblank lab name used by references and schedule output",
    )
    capacity: PositiveInt = Field(description="Maximum number of students the lab can accommodate")
    features: set[str] = Field(
        default_factory=set,
        description="Facility and equipment feature tags supplied by this lab",
    )
    times: dict[Day, list[TimeRange]] | None = Field(
        default=None,
        description="Optional weekday lab availability windows; null means unrestricted availability",
    )


class Meeting(StrictBaseModel):
    """
    Represents a single meeting instance.

    **Usage:**
    ```python
    Meeting(day="MON", duration=90, lab=False)
    ```
    """

    day: Day = Field(description="Day of the week", json_schema_extra={"example": "MON"})
    """
    Day of the week
    """

    start_time: TimeString | None = Field(
        default=None,
        description="Fixed start for this meeting; overrides the containing pattern start time",
    )
    """
    Fixed meeting start that takes precedence over the containing pattern start
    """

    duration: PositiveInt = Field(description="Duration of the meeting in minutes", json_schema_extra={"example": 150})
    """
    Duration of the meeting in minutes
    """

    lab: bool = Field(default=False, description="Whether this is the pattern's single lab meeting")
    """
    Whether this meeting is the pattern's single lab meeting
    """

    delivery: DeliveryMode = Field(
        default=DeliveryMode.IN_PERSON,
        description="Whether this meeting is held in person or online",
    )
    """Delivery mode controlling physical-room occupancy for this meeting."""

    @field_validator("delivery", mode="before")
    @classmethod
    def _convert_delivery(cls, value):
        return DeliveryMode(value) if isinstance(value, str) else value


class ClassPattern(StrictBaseModel):
    """
    Represents a class pattern.

    **Usage:**
    ```python
    ClassPattern(credits=3, meetings=[...])
    ```
    """

    credits: PositiveInt = Field(description="Number of credit hours", json_schema_extra={"example": 3})
    """
    Number of credit hours
    """

    meetings: list[Meeting] = Field(
        description="List of meeting times",
        json_schema_extra={"example": [{"day": "MON", "duration": 150, "lab": False}]},
    )
    """
    List of meeting times
    """

    disabled: bool = Field(default=False, description="Whether the pattern is disabled")
    """
    Whether the pattern is disabled
    """

    start_time: TimeString | None = Field(
        default=None,
        description="Fixed start fallback for meetings without their own start time",
    )
    """
    Fixed start used by meetings that do not specify their own start
    """

    @field_validator("meetings", mode="after")
    @classmethod
    def _validate_meetings(cls, v: list[Meeting], info: ValidationInfo):
        """
        Validate meeting list is not empty and has reasonable structure.

        **Usage:**
        ```python
        ClassPattern(credits=3, meetings=[Meeting(day="MON", duration=90, lab=False)])
        ```
        """
        if not v:
            raise ValueError("At least one meeting is required")

        # Check for duplicate days
        days = [meeting.day for meeting in v]
        if len(days) != len(set(days)):
            duplicates = [day for day in set(days) if days.count(day) > 1]
            raise ValueError(f"Duplicate meeting days found: {duplicates}")

        return v

    @model_validator(mode="after")
    def _validate_lab_meetings(self):
        """A pattern can reserve at most one lab meeting."""
        if sum(meeting.lab for meeting in self.meetings) > 1:
            raise ValueError("A class pattern can contain at most one lab meeting")
        if any(meeting.lab and meeting.delivery != DeliveryMode.IN_PERSON for meeting in self.meetings):
            raise ValueError("A lab meeting must use in-person delivery")
        return self


class TimeSlotConfig(StrictBaseModel):
    """
    Represents a time slot configuration.

    **Usage:**
    ```python
    TimeSlotConfig(times={...}, classes=[...])
    ```
    """

    times: dict[Day, list[TimeBlock]] = Field(
        description="Time blocks keyed by weekday; every Monday-Friday list must be non-empty"
    )
    """
    Time blocks for every weekday; each weekday list must be non-empty
    """

    classes: list[ClassPattern] = Field(description="Meeting patterns; at least one pattern must be enabled")
    """
    Class patterns, with at least one enabled pattern
    """

    max_time_gap: PositiveInt = Field(
        default=30,
        description="Maximum gap in minutes used to determine whether meetings are adjacent",
        json_schema_extra={"example": 30},
        ge=0,
    )
    """
    Maximum gap in minutes used to determine whether meetings are adjacent (default: 30)
    """

    min_time_overlap: PositiveInt = Field(
        default=45,
        description="Minimum clock-time overlap in minutes between meetings on different pattern days",
        json_schema_extra={"example": 45},
        gt=0,
    )
    """
    Minimum clock-time overlap between meetings on different pattern days (default: 45)
    """

    @model_validator(mode="after")
    def validate(self):
        """
        Validate the completeness and usability of a time-slot configuration.

        Args:
            None. Validation inspects the fields of this instance.

        Returns:
            This validated ``TimeSlotConfig`` instance for Pydantic's after-model
            validator protocol.

        Raises:
            ValueError: If a day key is unsupported, any weekday has no time
                blocks, no class pattern exists, or every pattern is disabled.

        Behavior:
            Validation checks all weekday coverage and pattern availability in a
            single pass, accumulates every discovered problem, and raises one
            combined error so callers can correct the complete configuration at
            once. It does not mutate the configuration.
        """
        errors = []

        # Check that all days in time_slot_config are valid
        weekdays: tuple[Day, ...] = ("MON", "TUE", "WED", "THU", "FRI")
        valid_days = frozenset(weekdays)
        for day in self.times:
            if day not in valid_days:
                errors.append(f"Invalid day '{day}' in time slot configuration")

        # Check that there are time blocks for each day
        for day in weekdays:
            if day not in self.times or not self.times[day]:
                errors.append(f"No time blocks defined for {day}")

        # Check that class patterns are reasonable
        if not self.classes:
            errors.append("At least one class pattern must be defined")

        # Check for disabled patterns
        disabled_patterns = [p for p in self.classes if p.disabled]
        if len(disabled_patterns) == len(self.classes):
            errors.append("All class patterns are disabled")

        if errors:
            error_message = "Time slot configuration errors:\n" + "\n".join(f"  - {error}" for error in errors)
            raise ValueError(error_message)

        return self


class CourseConfig(StrictBaseModel):
    """
    Represents a course configuration.

    **Usage:**
    ```python
    CourseConfig(
        course_id="CS 101",
        credits=3,
        capacity=30,
        room=["Room 101"],
        lab=[],
        conflicts=[],
        faculty=["Dr. Smith"],
    )
    ```
    """

    course_id: Course = Field(
        description="Base course identifier; repeated values create separately numbered sections",
        json_schema_extra={"example": "CS 101"},
    )
    """
    Base identifier for the course; repeated values create sections in configuration order
    """

    section_id: str | None = Field(
        default=None,
        description="Optional stable section suffix; null uses the generated zero-padded input-order number",
    )
    """Stable section suffix, or null to retain generated numbering."""

    credits: PositiveInt = Field(description="Number of credit hours", json_schema_extra={"example": 3})
    """
    Number of credit hours
    """

    capacity: PositiveInt = Field(
        description=("Expected section enrollment that any assigned rooms and labs must accommodate"),
        json_schema_extra={"example": 30},
    )
    """
    Expected section enrollment used for room and lab capacity validation
    """

    room: list[Room] = Field(
        description="Allowed room names; empty is valid only for compatible patterns that do not occupy a room",
        json_schema_extra={"example": ["Room 101"]},
    )
    """
    List of acceptable room names
    """

    lab: list[Lab] = Field(
        default_factory=list,
        description="Acceptable labs; an empty list means the course has no lab meeting",
        json_schema_extra={"example": ["Lab 101"]},
    )
    """
    Acceptable labs; empty means the course has no lab meeting
    """

    conflicts: list[Course] = Field(
        description="Base course IDs whose sections cannot overlap; an empty list means no declared conflicts"
    )
    """
    Base course IDs whose sections cannot overlap
    """

    faculty: list[Faculty] | None = Field(
        description=("Non-empty faculty candidates, or null to derive candidates from faculty course-preference keys"),
        json_schema_extra={"example": ["Dr. Smith"]},
    )
    """
    List of faculty names. `null` derives candidates from matching faculty course preferences.
    """

    modality: CourseModality = Field(
        default=CourseModality.IN_PERSON,
        description="Required delivery composition of the selected class pattern",
    )
    """Whether all meetings are in person, all are online, or the pattern is hybrid."""

    required_room_features: set[str] = Field(
        default_factory=set,
        description="Feature tags every assigned lecture room must provide",
    )
    """Required room features matched as a subset of resource features."""

    required_lab_features: set[str] = Field(
        default_factory=set,
        description="Feature tags every assigned lab must provide",
    )
    """Required lab features matched as a subset of resource features."""

    reserve_room_during_lab: bool = Field(
        default=True,
        description="Whether the lab meeting also occupies the section's assigned lecture room",
    )
    """When false, lab meetings leave the assigned lecture room available."""

    @field_validator("faculty")
    @classmethod
    def _validate_faculty_candidates(cls, value: list[Faculty] | None) -> list[Faculty] | None:
        if value == []:
            raise ValueError("Faculty candidates must be non-empty or null for preference-based assignment")
        return value

    @field_validator("modality", mode="before")
    @classmethod
    def _convert_modality(cls, value):
        return CourseModality(value) if isinstance(value, str) else value

    @field_validator("section_id")
    @classmethod
    def _validate_section_id(cls, value: str | None) -> str | None:
        if value is not None and not value.strip():
            raise ValueError("Section id must not be blank")
        return value

    @field_validator("required_room_features", "required_lab_features", mode="before")
    @classmethod
    def _validate_required_features(cls, value):
        if not isinstance(value, list | tuple | set | frozenset):
            return value
        if any(not isinstance(feature, str) or not feature.strip() for feature in value):
            raise ValueError("Required resource features must not be blank")
        return set(value)

    @model_validator(mode="after")
    def _validate_delivery_requirements(self):
        if self.modality == CourseModality.ONLINE and (self.room or self.lab or self.required_room_features):
            raise ValueError("Online courses cannot require rooms, labs, or room features")
        if self.required_room_features and not self.room:
            raise ValueError("Required room features require at least one candidate room")
        if self.required_lab_features and not self.lab:
            raise ValueError("Required lab features require at least one candidate lab")
        return self


class FacultyConfig(StrictBaseModel):
    """
    Represents a faculty configuration.

    **Usage:**
    ```python
    FacultyConfig(name="Dr. Smith", maximum_credits=12, minimum_credits=3, ...)
    ```
    """

    name: Faculty = Field(description='Faculty member"s name', json_schema_extra={"example": "Dr. Smith"})
    """
    Faculty member's name
    """

    maximum_credits: int = Field(
        description="Maximum credit hours they can teach", ge=0, json_schema_extra={"example": 12}
    )
    """
    Maximum credit hours they can teach
    """

    maximum_days: int = Field(
        default=5,
        ge=0,
        le=5,
        description="Maximum number of days they are willing to teach (0-5, optional)",
        json_schema_extra={"example": 3},
    )
    """
    Maximum number of days they are willing to teach (optional)
    """

    minimum_credits: int = Field(
        description="Minimum credit hours they must teach", ge=0, json_schema_extra={"example": 3}
    )
    """
    Minimum credit hours they must teach
    """

    unique_course_limit: PositiveInt = Field(
        description="Maximum number of different courses they can teach", json_schema_extra={"example": 3}
    )
    """
    Maximum number of different courses they can teach
    """

    times: dict[Day, list[TimeRange]] = Field(
        description="Availability ranges keyed by weekday; omitted days and empty lists mean unavailable",
        json_schema_extra={"example": {"MON": ["10:00-12:00"], "TUE": ["10:00-12:00"]}},
    )
    """
    Availability ranges by weekday; omitted days and empty lists are unavailable
    """

    course_preferences: dict[Course, Preference] = Field(
        default_factory=dict,
        description="Dictionary mapping course IDs to preference scores",
        json_schema_extra={"example": {"CS 101": 5}},
    )
    """
    Dictionary mapping `Course` IDs to `Preference` scores
    """

    room_preferences: dict[Room, Preference] = Field(
        default_factory=dict,
        description="Dictionary mapping room IDs to preference scores",
        json_schema_extra={"example": {"Room 101": 5}},
    )

    """
    Dictionary mapping `Room` IDs to `Preference` scores
    """

    lab_preferences: dict[Lab, Preference] = Field(
        default_factory=dict,
        description="Dictionary mapping lab IDs to preference scores",
        json_schema_extra={"example": {"Lab 101": 5}},
    )
    """
    Dictionary mapping `Lab` IDs to `Preference` scores
    """

    mandatory_days: set[Day] = Field(
        default_factory=set,
        description="Set of days the faculty must teach on",
        json_schema_extra={"example": ["MON", "WED"]},
    )
    """
    Set of days the faculty must teach on
    """

    @field_validator("times", mode="before")
    @classmethod
    def _convert_time_strings(cls, v):
        """
        Convert time strings to `TimeRange` objects

        **Usage:**
        ```python
        FacultyConfig.model_validate({..., "times": {"MON": ["10:00-12:00"]}})
        ```
        """
        if isinstance(v, dict):
            converted = {}
            for day, time_list in v.items():
                converted[day] = []
                for time_item in time_list:
                    if isinstance(time_item, str):
                        converted[day].append(TimeRange.from_string(time_item))
                    else:
                        converted[day].append(time_item)
            return converted
        return v

    @field_validator("mandatory_days", mode="before")
    @classmethod
    def _convert_mandatory_days(cls, v):
        if isinstance(v, list | tuple):
            return set(v)
        return v

    @model_validator(mode="after")
    def validate(self):
        """
        Validate workload limits and mandatory-day availability for one faculty member.

        Args:
            None. Validation inspects the fields of this instance.

        Returns:
            This validated ``FacultyConfig`` instance for Pydantic's after-model
            validator protocol.

        Raises:
            ValueError: If minimum credits exceed maximum credits, maximum days
                cannot contain all mandatory days, or a mandatory day has no
                availability entry.

        Behavior:
            Numeric bounds are checked before day feasibility. Day enum and string
            representations are normalized for comparison, but stored fields are
            not changed. The first invalid relationship is reported immediately.
        """
        if self.minimum_credits > self.maximum_credits:
            raise ValueError(
                f"Minimum credits ({self.minimum_credits}) cannot be greater than "
                f"maximum credits ({self.maximum_credits})"
            )
        if self.maximum_days < len(self.mandatory_days):
            raise ValueError(
                f"maximum_days ({self.maximum_days}) cannot be less than the number of mandatory days "
                f"({len(self.mandatory_days)})"
            )
        available_days = {day if isinstance(day, str) else str(day) for day in self.times}
        mandatory_days = {day if isinstance(day, str) else str(day) for day in self.mandatory_days}
        unavailable_mandatory = mandatory_days - available_days
        if unavailable_mandatory:
            raise ValueError(
                f"Mandatory days {sorted(unavailable_mandatory)} must be present in the availability times"
            )
        return self


class SchedulerConfig(StrictBaseModel):
    """
    Represents a scheduler configuration.

    **Usage:**
    ```python
    SchedulerConfig(
        rooms=[RoomConfig(name="Room 101", capacity=40)],
        labs=[LabConfig(name="Lab 101", capacity=24)],
        courses=[...],
        faculty=[...],
    )
    ```
    """

    rooms: list[RoomConfig] = Field(
        min_length=1,
        description="List of available room definitions",
        json_schema_extra={"example": [{"name": "Room 101", "capacity": 40}]},
    )
    """
    List of available room definitions
    """

    labs: list[LabConfig] = Field(
        description="List of available lab definitions",
        json_schema_extra={"example": [{"name": "Lab 101", "capacity": 24}]},
    )
    """
    List of available lab definitions
    """

    courses: list[CourseConfig] = Field(
        description="List of course configurations",
        json_schema_extra={
            "example": [
                {
                    "course_id": "CS 101",
                    "credits": 3,
                    "capacity": 24,
                    "room": ["Room 101"],
                    "lab": ["Lab 101"],
                    "conflicts": ["CS 102"],
                    "faculty": ["Dr. Smith"],
                }
            ]
        },
    )
    """
    List of `CourseConfig` configurations
    """

    faculty: list[FacultyConfig] = Field(
        description="List of faculty configurations",
        json_schema_extra={
            "example": [
                {
                    "name": "Dr. Smith",
                    "maximum_credits": 12,
                    "maximum_days": 3,
                    "minimum_credits": 3,
                    "unique_course_limit": 3,
                    "times": {"MON": ["10:00-12:00"], "TUE": ["10:00-12:00"]},
                    "mandatory_days": ["MON"],
                    "course_preferences": {"CS 101": 5},
                    "room_preferences": {"Room 101": 5},
                    "lab_preferences": {"Lab 101": 5},
                }
            ]
        },
    )
    """
    List of `FacultyConfig` configurations
    """

    @model_validator(mode="after")
    def validate(self):
        """
        Validate uniqueness and all cross-references in scheduler configuration.

        Args:
            None. Validation inspects this configuration and its nested course and
            faculty records.

        Returns:
            This validated ``SchedulerConfig`` instance for Pydantic's after-model
            validator protocol.

        Raises:
            ValueError: If resource or faculty names are duplicated; a course,
                conflict, room, lab, or preference reference is unknown; a course
                conflicts with itself; or null faculty cannot be inferred from
                course preferences.

        Behavior:
            Uniqueness is checked first. Remaining reference errors are accumulated
            across courses and faculty and emitted together. An explicit faculty
            list is validated directly; ``faculty=None`` instead requires at least
            one faculty course-preference entry from which eligibility can later be
            derived. Validation never replaces the null value or mutates children.
        """
        # Validate uniqueness first
        self._validate_uniqueness()

        # Create sets of valid references for efficient lookup
        valid_rooms = {room.name for room in self.rooms}
        valid_labs = {lab.name for lab in self.labs}
        valid_courses = {course.course_id for course in self.courses}
        valid_faculty = {faculty.name for faculty in self.faculty}

        # Collect all validation errors for better user experience
        errors = []

        course_counts: dict[str, int] = {}
        display_names: list[str] = []
        for course in self.courses:
            course_counts[course.course_id] = course_counts.get(course.course_id, 0) + 1
            suffix = course.section_id or f"{course_counts[course.course_id]:02d}"
            display_names.append(f"{course.course_id}.{suffix}")
        duplicate_display_names = sorted({name for name in display_names if display_names.count(name) > 1})
        if duplicate_display_names:
            duplicate_errors: list[InitErrorDetails] = []
            seen_display_names: set[str] = set()
            for index, (course, display_name) in enumerate(zip(self.courses, display_names, strict=True)):
                if display_name in seen_display_names:
                    field_name = "section_id" if course.section_id is not None else "course_id"
                    duplicate_errors.append(
                        InitErrorDetails(
                            type=PydanticCustomError(
                                "duplicate_course_section_identifier",
                                "Duplicate course section identifiers found: {names}",
                                {"names": duplicate_display_names},
                            ),
                            loc=("courses", index, field_name),
                            input=getattr(course, field_name),
                        )
                    )
                seen_display_names.add(display_name)
            raise ValidationError.from_exception_data(self.__class__.__name__, duplicate_errors)

        # Validate CourseConfig references
        for course in self.courses:
            # Validate room references
            invalid_rooms = [room for room in course.room if room not in valid_rooms]
            if invalid_rooms:
                errors.append(f'Course "{course.course_id}" references invalid rooms: {invalid_rooms}')

            # Validate lab references
            invalid_labs = [lab for lab in course.lab if lab not in valid_labs]
            if invalid_labs:
                errors.append(f'Course "{course.course_id}" references invalid labs: {invalid_labs}')

            # Validate conflict course references (including self-conflicts)
            invalid_conflicts = [conflict for conflict in course.conflicts if conflict not in valid_courses]
            if invalid_conflicts:
                errors.append(f'Course "{course.course_id}" references invalid conflict courses: {invalid_conflicts}')

            # Check for self-conflicts
            if course.course_id in course.conflicts:
                errors.append(f'Course "{course.course_id}" cannot conflict with itself')

            # Validate explicit faculty references or preference-based inference.
            if course.faculty is None:
                inferred_faculty = [
                    faculty.name for faculty in self.faculty if course.course_id in faculty.course_preferences
                ]
                if not inferred_faculty:
                    errors.append(
                        f'Course "{course.course_id}" has null faculty but no faculty course preferences to derive from'
                    )
            else:
                invalid_faculty = [faculty for faculty in course.faculty if faculty not in valid_faculty]
                if invalid_faculty:
                    errors.append(f'Course "{course.course_id}" references invalid faculty: {invalid_faculty}')

        # Validate FacultyConfig references
        for faculty in self.faculty:
            # Validate course preference references
            invalid_course_prefs = [course for course in faculty.course_preferences if course not in valid_courses]
            if invalid_course_prefs:
                errors.append(
                    f'Faculty "{faculty.name}" references invalid courses in preferences: {invalid_course_prefs}'
                )

            # Validate room preference references
            invalid_room_prefs = [room for room in faculty.room_preferences if room not in valid_rooms]
            if invalid_room_prefs:
                errors.append(f'Faculty "{faculty.name}" references invalid rooms in preferences: {invalid_room_prefs}')

            # Validate lab preference references
            invalid_lab_prefs = [lab for lab in faculty.lab_preferences if lab not in valid_labs]
            if invalid_lab_prefs:
                errors.append(f'Faculty "{faculty.name}" references invalid labs in preferences: {invalid_lab_prefs}')

        # Raise all errors at once for better debugging
        if errors:
            error_message = "Configuration validation errors:\n" + "\n".join(f"  - {error}" for error in errors)
            raise ValueError(error_message)

        return self

    def _validate_uniqueness(self):
        """
        Validate that all names are unique within their respective lists
        (except courses which can have duplicates).

        **Usage:**
        ```python
        scheduler_config._validate_uniqueness()
        ```
        """
        errors: list[InitErrorDetails] = []
        for field_name, values, label in (
            ("rooms", self.rooms, "room"),
            ("labs", self.labs, "lab"),
            ("faculty", self.faculty, "faculty"),
        ):
            seen: set[str] = set()
            for index, value in enumerate(values):
                if value.name in seen:
                    errors.append(
                        InitErrorDetails(
                            type=PydanticCustomError(
                                f"duplicate_{label}_name",
                                f"Duplicate {label} name: {{name}}",
                                {"name": value.name},
                            ),
                            loc=(field_name, index, "name"),
                            input=value.name,
                        )
                    )
                seen.add(value.name)
        if errors:
            raise ValidationError.from_exception_data(self.__class__.__name__, errors)


class OptimizerFlags(StrEnum):
    FACULTY_COURSE = "faculty_course"
    """
    Optimize faculty course assignments using preferences

    **Usage:**
    ```python
    OptimizerFlags.FACULTY_COURSE
    ["faculty_course"]  # accepted in CombinedConfig JSON
    ```
    """

    FACULTY_ROOM = "faculty_room"
    """
    Optimize faculty room assignments using preferences

    **Usage:**
    ```python
    OptimizerFlags.FACULTY_ROOM
    ["faculty_room"]  # accepted in CombinedConfig JSON
    ```
    """

    FACULTY_LAB = "faculty_lab"
    """
    Optimize faculty lab assignments using preferences

    **Usage:**
    ```python
    OptimizerFlags.FACULTY_LAB
    ["faculty_lab"]  # accepted in CombinedConfig JSON
    ```
    """

    SAME_ROOM = "same_room"
    """
    Prefer eligible course pairs taught by the same faculty to share a room

    **Usage:**
    ```python
    OptimizerFlags.SAME_ROOM
    ["same_room"]  # accepted in CombinedConfig JSON
    ```
    """

    SAME_LAB = "same_lab"
    """
    Prefer eligible lab-course pairs taught by the same faculty to share a lab

    **Usage:**
    ```python
    OptimizerFlags.SAME_LAB
    ["same_lab"]  # accepted in CombinedConfig JSON
    ```
    """

    PACK_ROOMS = "pack_rooms"
    """
    Prefer different courses to share a room when any meeting pair is adjacent

    **Usage:**
    ```python
    OptimizerFlags.PACK_ROOMS
    ["pack_rooms"]  # accepted in CombinedConfig JSON
    ```
    """

    PACK_LABS = "pack_labs"
    """
    Prefer different courses to share a lab at adjacent lab times

    **Usage:**
    ```python
    OptimizerFlags.PACK_LABS
    ["pack_labs"]  # accepted in CombinedConfig JSON
    ```
    """


class CombinedConfig(StrictBaseModel):
    """
    Represents a combined configuration.

    **Usage:**
    ```python
    CombinedConfig(config=..., time_slot_config=..., limit=10)
    ```
    """

    config: SchedulerConfig = Field(
        description="Scheduler configuration",
        json_schema_extra={
            "example": {
                "rooms": [{"name": "Room 101", "capacity": 40}],
                "labs": [{"name": "Lab 101", "capacity": 24}],
                "courses": [
                    {
                        "course_id": "CS 101",
                        "credits": 3,
                        "capacity": 24,
                        "room": ["Room 101"],
                        "lab": ["Lab 101"],
                        "conflicts": [],
                        "faculty": ["Dr. Smith"],
                    }
                ],
                "faculty": [
                    {
                        "name": "Dr. Smith",
                        "maximum_credits": 12,
                        "minimum_credits": 3,
                        "unique_course_limit": 3,
                        "times": {"MON": ["10:00-12:00"], "TUE": ["10:00-12:00"]},
                        "course_preferences": {"CS 101": 5},
                        "room_preferences": {"Room 101": 5},
                        "lab_preferences": {"Lab 101": 5},
                    }
                ],
            }
        },
    )
    """
    Scheduler configuration
    """

    time_slot_config: TimeSlotConfig = Field(
        description="Time slot configuration",
        json_schema_extra={
            "example": {
                "times": {
                    "MON": [{"start": "10:00", "spacing": 60, "end": "12:00"}],
                    "TUE": [{"start": "10:00", "spacing": 60, "end": "12:00"}],
                    "WED": [{"start": "10:00", "spacing": 60, "end": "12:00"}],
                    "THU": [{"start": "10:00", "spacing": 60, "end": "12:00"}],
                    "FRI": [{"start": "10:00", "spacing": 60, "end": "12:00"}],
                },
                "classes": [{"credits": 3, "meetings": [{"day": "MON", "duration": 150, "lab": False}]}],
            }
        },
    )
    """
    Time slot configuration
    """

    limit: PositiveInt = Field(
        default=10, description="Maximum number of schedules to generate", json_schema_extra={"example": 10}
    )
    """
    Maximum number of schedules to generate (default: 10)
    """

    optimizer_flags: list[OptimizerFlags] = Field(
        default_factory=list,
        description="List of optimizer flags",
        json_schema_extra={
            "example": [
                OptimizerFlags.FACULTY_COURSE,
                OptimizerFlags.FACULTY_ROOM,
                OptimizerFlags.FACULTY_LAB,
                OptimizerFlags.SAME_ROOM,
                OptimizerFlags.SAME_LAB,
                OptimizerFlags.PACK_ROOMS,
                OptimizerFlags.PACK_LABS,
            ]
        },
    )
    """
    List of optimizer flags to pass to the scheduler
    """

    @field_validator("optimizer_flags", mode="before")
    @classmethod
    def _convert_optimizer_flags(cls, v):
        """
        Convert optimizer flags to OptimizerFlags objects

        **Usage:**
        ```python
        CombinedConfig(..., optimizer_flags=["faculty_course"])
        ```
        """
        if isinstance(v, list):
            return [OptimizerFlags(flag) if isinstance(flag, str) else flag for flag in v]
        return v

    @model_validator(mode="after")
    def _validate_course_patterns(self):
        """Ensure every course has an enabled, resource-compatible class pattern."""
        patterns_by_credit: dict[int, list[ClassPattern]] = {}
        for pattern in self.time_slot_config.classes:
            if not pattern.disabled:
                patterns_by_credit.setdefault(pattern.credits, []).append(pattern)

        errors: list[InitErrorDetails] = []
        for index, course in enumerate(self.config.courses):
            patterns = patterns_by_credit.get(course.credits, [])
            if not patterns:
                errors.append(
                    InitErrorDetails(
                        type=PydanticCustomError(
                            "course_pattern_credit_mismatch",
                            'Course "{course_id}" has credits ({credits}) with no enabled class pattern',
                            {"course_id": course.course_id, "credits": course.credits},
                        ),
                        loc=("config", "courses", index, "credits"),
                        input=course.credits,
                    )
                )
                continue

            requires_lab = bool(course.lab)
            resource_patterns = [
                pattern for pattern in patterns if any(meeting.lab for meeting in pattern.meetings) == requires_lab
            ]
            if not resource_patterns:
                expected = "a lab meeting" if requires_lab else "no lab meeting"
                errors.append(
                    InitErrorDetails(
                        type=PydanticCustomError(
                            "course_pattern_lab_mismatch",
                            'Course "{course_id}" has no enabled class pattern with {expected}',
                            {"course_id": course.course_id, "expected": expected},
                        ),
                        loc=("config", "courses", index, "lab"),
                        input=course.lab,
                    )
                )
                continue

            def pattern_modality(pattern: ClassPattern) -> CourseModality:
                modes = {meeting.delivery for meeting in pattern.meetings}
                if modes == {DeliveryMode.IN_PERSON}:
                    return CourseModality.IN_PERSON
                if modes == {DeliveryMode.ONLINE}:
                    return CourseModality.ONLINE
                return CourseModality.HYBRID

            modality_patterns = [
                pattern for pattern in resource_patterns if pattern_modality(pattern) == course.modality
            ]
            if not modality_patterns:
                errors.append(
                    InitErrorDetails(
                        type=PydanticCustomError(
                            "course_pattern_modality_mismatch",
                            'Course "{course_id}" has no enabled class pattern matching modality "{modality}"',
                            {"course_id": course.course_id, "modality": course.modality.value},
                        ),
                        loc=("config", "courses", index, "modality"),
                        input=course.modality,
                    )
                )
                continue

            if not course.room:
                room_compatible_patterns = [
                    pattern
                    for pattern in modality_patterns
                    if not any(
                        meeting.delivery == DeliveryMode.IN_PERSON
                        and (not meeting.lab or course.reserve_room_during_lab)
                        for meeting in pattern.meetings
                    )
                ]
                if not room_compatible_patterns:
                    errors.append(
                        InitErrorDetails(
                            type=PydanticCustomError(
                                "course_pattern_room_requirement_mismatch",
                                'Course "{course_id}" has no enabled class pattern that can run without a room',
                                {"course_id": course.course_id},
                            ),
                            loc=("config", "courses", index, "room"),
                            input=course.room,
                        )
                    )

        if errors:
            raise ValidationError.from_exception_data(self.__class__.__name__, errors)
        return self
