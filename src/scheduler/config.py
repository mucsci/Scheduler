from typing import List, Dict, Optional
import json

from pydantic import BaseModel, Field


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
    meetings: List[Meeting]
    disabled: Optional[bool] = Field(default=False)
    start_time: Optional[str] = Field(default=None)


class TimeSlotConfig(BaseModel):
    times: Dict[str, List[TimeBlock]]
    classes: List[ClassPattern]


class CourseConfig(BaseModel):
    course_id: str
    credits: int
    room: List[str]
    lab: List[str]
    conflicts: List[str]
    faculty: List[str]


class FacultyConfig(BaseModel):
    name: str
    maximum_credits: int
    minimum_credits: int
    unique_course_limit: int
    times: Dict[str, List[str]]  # {day_name: ["HH:MM-HH:MM", ...]}
    preferences: Dict[str, int] = Field(default_factory=dict)


class SchedulerConfig(BaseModel):
    rooms: List[str]
    labs: List[str]
    courses: List[CourseConfig]
    faculty: List[FacultyConfig]
