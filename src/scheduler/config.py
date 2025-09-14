from enum import Enum
from typing import Annotated, Literal

from pydantic import (
    BaseModel,
    ConfigDict,
    Field,
    PositiveInt,
    field_validator,
    model_validator,
)

type TimeString = Annotated[
    str,
    Field(
        pattern=r"^([0-1][0-9]|2[0-3]):[0-5][0-9]$",
        description="Time in HH:MM format",
        frozen=True,
        example="10:00",
    ),
]
"""
TimeString is a string in the format of HH:MM.
"""

type TimeRangeString = Annotated[
    str,
    Field(
        pattern=r"^([0-1][0-9]|2[0-3]):[0-5][0-9]-([0-1][0-9]|2[0-3]):[0-5][0-9]$",
        description="Time range in HH:MM-HH:MM format",
        frozen=True,
        example="10:00-12:00",
    ),
]

"""
TimeRangeString is a string in the format of HH:MM-HH:MM.
"""

type Preference = Annotated[
    int,
    Field(
        ge=0,
        le=10,
        description="Preference score between 0 and 10",
        example=5,
    ),
]
"""
Preference is a score between 0 and 10.
"""

type Day = Annotated[
    Literal["MON", "TUE", "WED", "THU", "FRI"],
    Field(
        description="Day of the week",
        frozen=True,
        example="MON",
    ),
]
"""
Day is a day of the week (MON, TUE, WED, THU, FRI).
"""

type Room = Annotated[
    str,
    Field(
        frozen=True,
        description="Room name",
        example="Room 101",
    ),
]
"""
Room is a room name.
"""

type Lab = Annotated[
    str,
    Field(
        frozen=True,
        description="Lab name",
        example="Lab 101",
    ),
]
"""
Lab is a lab name.
"""

type Course = Annotated[
    str,
    Field(
        frozen=True,
        description="Course name",
        example="CS 101",
    ),
]
"""
Course is a course name.
"""

type Faculty = Annotated[
    str,
    Field(
        frozen=True,
        description="Faculty name",
        example="Dr. Smith",
    ),
]
"""
Faculty is a faculty name.
"""


class _StrictBaseModel(BaseModel):
    """
    Base class for all models which need strict validation.
    """

    model_config = ConfigDict(extra="forbid", strict=True)


class TimeBlock(_StrictBaseModel):
    """
    Represents a time block within a day.
    """

    start: TimeString = Field(description="Start time of the time block", example="10:00")
    spacing: PositiveInt = Field(description="Time spacing between slots in minutes", example=60)
    end: TimeString = Field(description="End time of the time block", example="17:00")

    @field_validator("end")
    @classmethod
    def validate_end_after_start(cls, v, info):
        if "start" in info.data:
            start_time = info.data["start"]
            # Convert time strings to minutes for comparison
            start_minutes = int(start_time.split(":")[0]) * 60 + int(start_time.split(":")[1])
            end_minutes = int(v.split(":")[0]) * 60 + int(v.split(":")[1])

            if end_minutes <= start_minutes:
                raise ValueError("End time must be after start time")
        return v


class TimeRange(_StrictBaseModel):
    """
    A time range with start and end times, ensuring start < end.
    """

    start: TimeString = Field(description="Start time of the time range", example="10:00")
    end: TimeString = Field(description="End time of the time range", example="17:00")

    @field_validator("end")
    @classmethod
    def validate_end_after_start(cls, v, info):
        if "start" in info.data:
            start_time = info.data["start"]
            # Convert time strings to minutes for comparison
            start_minutes = int(start_time.split(":")[0]) * 60 + int(start_time.split(":")[1])
            end_minutes = int(v.split(":")[0]) * 60 + int(v.split(":")[1])

            if end_minutes <= start_minutes:
                raise ValueError("End time must be after start time")
        return v

    def __str__(self) -> str:
        return f"{self.start}-{self.end}"

    @classmethod
    def from_string(cls, time_range_str: str) -> "TimeRange":
        """Create TimeRange from string format "HH:MM-HH:MM"."""
        start, end = time_range_str.split("-")
        return cls(start=start, end=end)


class Meeting(_StrictBaseModel):
    """
    Represents a single meeting instance.
    """

    day: Day = Field(description="Day of the week", example="MON")
    duration: PositiveInt = Field(description="Duration of the meeting in minutes", example=150)
    lab: bool = Field(default=False, description="Whether the meeting is in a lab")


class ClassPattern(_StrictBaseModel):
    """
    Represents a class pattern.
    """

    credits: int = Field(description="Number of credit hours", example=3)
    meetings: list[Meeting] = Field(
        description="List of meeting times", example=[{"day": "MON", "duration": 150, "lab": False}]
    )
    disabled: bool = Field(default=False, description="Whether the pattern is disabled")
    start_time: TimeString | None = Field(default=None, description="Specific start time constraint")

    @field_validator("meetings")
    @classmethod
    def validate_meetings(cls, v):
        """Validate meeting list is not empty and has reasonable structure."""
        if not v:
            raise ValueError("At least one meeting is required")

        # Check for duplicate days
        days = [meeting.day for meeting in v]
        if len(days) != len(set(days)):
            duplicates = [day for day in set(days) if days.count(day) > 1]
            raise ValueError(f"Duplicate meeting days found: {duplicates}")

        return v


class TimeSlotConfig(_StrictBaseModel):
    """
    Represents a time slot configuration.
    """

    times: dict[Day, list[TimeBlock]] = Field(description="Dictionary mapping day names to time blocks")
    classes: list[ClassPattern] = Field(description="List of class patterns")


class CourseConfig(_StrictBaseModel):
    """
    Represents a course configuration.
    """

    course_id: Course = Field(description="Unique identifier for the course", example="CS 101")
    credits: int = Field(description="Number of credit hours", example=3)
    room: list[Room] = Field(description="List of acceptable room names", example=["Room 101"])
    lab: list[Lab] = Field(description="List of acceptable lab names", example=["Lab 101"])
    conflicts: list[Course] = Field(description="List of course IDs that cannot be scheduled simultaneously")
    faculty: list[Faculty] = Field(description="List of faculty names", example=["Dr. Smith"])

    @model_validator(mode="after")
    def validate_references(self):
        """Validate that all references exist in the parent SchedulerConfig.
        This validator will be called by the parent SchedulerConfig."""
        return self


class FacultyConfig(_StrictBaseModel):
    """
    Represents a faculty configuration.
    """

    name: Faculty = Field(description='Faculty member"s name', example="Dr. Smith")
    maximum_credits: int = Field(description="Maximum credit hours they can teach", ge=0, example=12)
    minimum_credits: int = Field(description="Minimum credit hours they must teach", ge=0, example=3)
    unique_course_limit: PositiveInt = Field(
        description="Maximum number of different courses they can teach", example=3
    )
    times: dict[Day, list[TimeRange]] = Field(
        description="Dictionary mapping day names to time ranges",
        example={"MON": ["10:00-12:00"], "TUE": ["10:00-12:00"]},
    )
    course_preferences: dict[Course, Preference] = Field(
        default_factory=dict,
        description="Dictionary mapping course IDs to preference scores",
        example={"CS 101": 5},
    )
    room_preferences: dict[Room, Preference] = Field(
        default_factory=dict,
        description="Dictionary mapping room IDs to preference scores",
        example={"Room 101": 5},
    )
    lab_preferences: dict[Lab, Preference] = Field(
        default_factory=dict,
        description="Dictionary mapping lab IDs to preference scores",
        example={"Lab 101": 5},
    )

    @field_validator("times", mode="before")
    @classmethod
    def convert_time_strings(cls, v):
        """Convert time strings to TimeRange objects."""
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

    @model_validator(mode="after")
    def validate_credit_consistency(self):
        """Validate that minimum and maximum credits are consistent."""
        if self.minimum_credits > self.maximum_credits:
            raise ValueError(
                f"Minimum credits ({self.minimum_credits}) cannot be greater than "
                f"maximum credits ({self.maximum_credits})"
            )
        return self


class SchedulerConfig(_StrictBaseModel):
    """
    Represents a scheduler configuration.
    """

    rooms: list[Room] = Field(description="List of available room names", example=["Room 101"])
    labs: list[Lab] = Field(description="List of available lab names", example=["Lab 101"])
    courses: list[CourseConfig] = Field(
        description="List of course configurations",
        example=[
            {
                "course_id": "CS 101",
                "credits": 3,
                "room": ["Room 101"],
                "lab": ["Lab 101"],
                "conflicts": ["CS 102"],
                "faculty": ["Dr. Smith"],
            }
        ],
    )
    faculty: list[FacultyConfig] = Field(
        description="List of faculty configurations",
        example=[
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
    )

    @model_validator(mode="after")
    def validate_all_references(self):
        """Validate that all Faculty, Room, Lab, and Course references exist and are unique."""
        # Validate uniqueness first
        self._validate_uniqueness()

        # Create sets of valid references for efficient lookup
        valid_rooms = set(self.rooms)
        valid_labs = set(self.labs)
        valid_courses = {course.course_id for course in self.courses}
        valid_faculty = {faculty.name for faculty in self.faculty}

        # Collect all validation errors for better user experience
        errors = []

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

            # Validate faculty references
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

        # Additional business logic validations
        self._validate_business_logic(errors)

        # Raise all errors at once for better debugging
        if errors:
            error_message = "Configuration validation errors:\n" + "\n".join(f"  - {error}" for error in errors)
            raise ValueError(error_message)

        return self

    def _validate_business_logic(self, errors: list[str]):
        """Validate business logic constraints."""
        courses = set(c for f in self.faculty for c in f.course_preferences)
        unassignable = set(c.course_id for c in self.courses) - courses
        if unassignable:
            errors.append(f"Courses without faculty assignments: {unassignable}")
        return self

    def _validate_uniqueness(self):
        """
        Validate that all names are unique within their respective lists
        (except courses which can have duplicates).
        """
        # Check room uniqueness
        if len(self.rooms) != len(set(self.rooms)):
            duplicates = [room for room in set(self.rooms) if self.rooms.count(room) > 1]
            raise ValueError(f"Duplicate room names found: {duplicates}")

        # Check lab uniqueness
        if len(self.labs) != len(set(self.labs)):
            duplicates = [lab for lab in set(self.labs) if self.labs.count(lab) > 1]
            raise ValueError(f"Duplicate lab names found: {duplicates}")

        # Check faculty uniqueness
        faculty_names = [faculty.name for faculty in self.faculty]
        if len(faculty_names) != len(set(faculty_names)):
            duplicates = [name for name in set(faculty_names) if faculty_names.count(name) > 1]
            raise ValueError(f"Duplicate faculty names found: {duplicates}")


class OptimizerFlags(str, Enum):
    FACULTY_COURSE = "faculty_course"
    FACULTY_ROOM = "faculty_room"
    FACULTY_LAB = "faculty_lab"
    SAME_ROOM = "same_room"
    SAME_LAB = "same_lab"
    PACK_ROOMS = "pack_rooms"
    PACK_LABS = "pack_labs"


class CombinedConfig(_StrictBaseModel):
    """
    Represents a combined configuration.
    """

    config: SchedulerConfig = Field(
        description="Scheduler configuration",
        example=SchedulerConfig(
            rooms=["Room 101"],
            labs=["Lab 101"],
            courses=[
                {
                    "course_id": "CS 101",
                    "credits": 3,
                    "room": ["Room 101"],
                    "lab": ["Lab 101"],
                    "conflicts": [],
                    "faculty": ["Dr. Smith"],
                }
            ],
            faculty=[
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
        ),
    )
    time_slot_config: TimeSlotConfig = Field(
        description="Time slot configuration",
        example=TimeSlotConfig(
            times={"MON": [{"start": "10:00", "spacing": 60, "end": "12:00"}]},
            classes=[{"credits": 3, "meetings": [{"day": "MON", "duration": 150, "lab": False}]}],
        ),
    )
    limit: PositiveInt = Field(default=10, description="Maximum number of schedules to generate", example=10)
    optimizer_flags: list[OptimizerFlags] = Field(
        default_factory=list,
        description="List of optimizer flags",
        example=[
            OptimizerFlags.FACULTY_COURSE,
            OptimizerFlags.FACULTY_ROOM,
            OptimizerFlags.FACULTY_LAB,
            OptimizerFlags.SAME_ROOM,
            OptimizerFlags.SAME_LAB,
            OptimizerFlags.PACK_ROOMS,
            OptimizerFlags.PACK_LABS,
        ],
    )

    @field_validator("optimizer_flags", mode="before")
    @classmethod
    def convert_optimizer_flags(cls, v):
        """Convert optimizer flags to OptimizerFlags objects."""
        if isinstance(v, list):
            return [OptimizerFlags(flag) if isinstance(flag, str) else flag for flag in v]
        return v

    @model_validator(mode="after")
    def validate_time_slot_config_consistency(self):
        """Validate that time slot config is consistent with scheduler config."""
        errors = []

        # Check that all days in time_slot_config are valid
        valid_days = {"MON", "TUE", "WED", "THU", "FRI"}
        for day in self.time_slot_config.times:
            if day not in valid_days:
                errors.append(f"Invalid day '{day}' in time slot configuration")

        # Check that there are time blocks for each day
        for day in valid_days:
            if day not in self.time_slot_config.times or not self.time_slot_config.times[day]:
                errors.append(f"No time blocks defined for {day}")

        # Check that class patterns are reasonable
        if not self.time_slot_config.classes:
            errors.append("At least one class pattern must be defined")

        # Check for disabled patterns
        disabled_patterns = [p for p in self.time_slot_config.classes if p.disabled]
        if len(disabled_patterns) == len(self.time_slot_config.classes):
            errors.append("All class patterns are disabled")

        if errors:
            error_message = "Time slot configuration errors:\n" + "\n".join(f"  - {error}" for error in errors)
            raise ValueError(error_message)

        return self
