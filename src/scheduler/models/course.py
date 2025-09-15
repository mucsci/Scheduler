from dataclasses import dataclass

import z3
from pydantic import BaseModel, ConfigDict, Field, computed_field

from .time_slot import TimeInstance, TimeSlot


@dataclass
class Course:
    """
    A course with a course_id, section, credits, conflicts, potential labs, potential rooms, and potential faculty.
    """

    course_id: str
    """
    The unique identifier for the course
    """

    credits: int
    """
    The number of credits for the course
    """

    section: int
    """
    The section number for the course
    """

    labs: list[str]
    """
    The list of potential labs for the course
    """

    rooms: list[str]
    """
    The list of potential rooms for the course
    """

    conflicts: list[str]
    """
    The list of course conflicts for the course
    """

    faculties: list[str]
    """
    The list of potential faculty for the course
    """

    lab: z3.ExprRef | None = None
    """
    The z3 variable used for assigning a lab
    """

    room: z3.ExprRef | None = None
    """
    The z3 variable used for assigning a room
    """

    time: z3.ExprRef | None = None
    """
    The z3 variable used for assigning a time slot
    """

    faculty: z3.ExprRef | None = None
    """
    The z3 variable used for assigning a faculty
    """

    def __str__(self) -> str:
        """
        Pretty Print representation of a course is its course_id and section
        """
        return f"{self.course_id}.{self.section:02d}"


class CourseInstance(BaseModel):
    """
    A course instance with a course, time, faculty, room, and lab.
    """

    model_config = ConfigDict(extra="forbid", strict=True, arbitrary_types_allowed=True)
    """
    Configuration for the model which forbids extra fields and is strict (@private)
    """

    course: Course = Field(description="The corresponding course object", exclude=True)
    """
    The corresponding course object
    """

    time: TimeSlot = Field(description="The assigned time slot", exclude=True)
    """
    The assigned time slot
    """

    faculty: str = Field(description="The assigned faculty")
    """
    The assigned faculty
    """

    room: str | None = Field(default=None, description="The assigned room")
    """
    The assigned room
    """

    lab: str | None = Field(default=None, description="The assigned lab")
    """
    The assigned lab
    """

    @computed_field(alias="course")
    @property
    def course_str(self) -> str:
        """
        The string representation of the course

        **Returns:**
        The string representation of the course
        """
        return str(self.course)

    @computed_field
    @property
    def times(self) -> list[TimeInstance]:
        """
        The list of times assigned to the course instance

        **Returns:**
        The list of times assigned to the course instance
        """
        return self.time.times

    @computed_field
    @property
    def lab_index(self) -> int | None:
        """
        The index of the lab assigned to the course instance

        **Returns:**
        The index of the lab assigned to the course instance.
        None if the course instance does not have a lab
        """
        return self.time.lab_index if (self.lab is not None) else None

    def as_csv(self) -> str:
        """
        The CSV representation of the course instance in the format:

        `<course>,<faculty>,<room>,<lab>,<times>`

        **Returns:**
        The CSV representation of the course instance
        """
        room_str = str(self.room)
        lab_str = str(self.lab)
        time_str = str(self.time)
        if self.lab is None:
            time_str = time_str.replace("^", "")
        return f"{self.course},{self.faculty},{room_str},{lab_str},{time_str}"
