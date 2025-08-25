from enum import StrEnum

from pydantic import BaseModel, Field


class TimeBlock(BaseModel):
    start: str
    spacing: int
    end: str


class Meeting(BaseModel):
    day: str
    duration: int
    lab: bool | None = Field(default=False)


class ClassPattern(BaseModel):
    credits: int
    meetings: list[Meeting]
    disabled: bool | None = Field(default=False)
    start_time: str | None = Field(default=None)


class TimeSlotConfig(BaseModel):
    times: dict[str, list[TimeBlock]]
    classes: list[ClassPattern]


class CourseConfig(BaseModel):
    course_id: str
    credits: int
    room: list[str]
    lab: list[str]
    conflicts: list[str]
    faculty: list[str]


class FacultyConfig(BaseModel):
    name: str
    maximum_credits: int
    minimum_credits: int
    unique_course_limit: int
    times: dict[str, list[str]]  # {day_name: ["HH:MM-HH:MM", ...]}
    course_preferences: dict[str, int] = Field(default_factory=dict)
    room_preferences: dict[str, int] = Field(default_factory=dict)
    lab_preferences: dict[str, int] = Field(default_factory=dict)


class SchedulerConfig(BaseModel):
    rooms: list[str]
    labs: list[str]
    courses: list[CourseConfig]
    faculty: list[FacultyConfig]


class OptimizerFlags(StrEnum):
    FACULTY_COURSE = "faculty_course"
    FACULTY_ROOM = "faculty_room"
    FACULTY_LAB = "faculty_lab"
    SAME_ROOM = "same_room"
    SAME_LAB = "same_lab"
    PACK_ROOMS = "pack_rooms"
    PACK_LABS = "pack_labs"


class CombinedConfig(BaseModel):
    config: SchedulerConfig
    time_slot_config: TimeSlotConfig
    limit: int = Field(default=10)
    optimizer_flags: list[OptimizerFlags] = Field(default_factory=list)
