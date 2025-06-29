from typing import Optional

import json
from pydantic import BaseModel, Field
from enum import StrEnum


class TimeBlock(BaseModel):
    start: str
    spacing: int
    end: str


class Meeting(BaseModel):
    day: str
    duration: int
    lab: Optional[bool] = Field(default=False)


class ClassPattern(BaseModel):
    credits: int
    meetings: list[Meeting]
    disabled: Optional[bool] = Field(default=False)
    start_time: Optional[str] = Field(default=None)


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
