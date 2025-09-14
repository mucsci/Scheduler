from collections import defaultdict
from typing import ClassVar, cast

import z3
from pydantic import BaseModel, Field, computed_field

from .identifiable import Identifiable
from .time_slot import TimeInstance, TimeSlot


class Course(Identifiable):
    """
    A course with a course_id, section, labs, rooms, conflicts, and faculties.
    """

    credits: int = Field(description="The number of credits for the course")
    course_id: str = Field(description="The unique identifier for the course")
    section: int | None = Field(default=None, description="The section number for the course")
    labs: list[str] = Field(description="The list of potential labs for the course")
    rooms: list[str] = Field(description="The list of potential rooms for the course")
    conflicts: list[str] = Field(description="The list of course conflicts for the course")
    faculties: list[str] = Field(description="The list of potential faculty for the course")

    _total_sections: ClassVar[defaultdict[str, int]] = defaultdict(int)

    _lab: z3.ExprRef | None
    _room: z3.ExprRef | None
    _time: z3.ExprRef | None
    _faculty: z3.ExprRef | None

    def __init__(self, **kwargs):
        """
        Initializes a course with a course_id, section, labs, rooms, conflicts, and faculties.

        **Args:**
        - **kwargs: The keyword arguments to initialize the course
        """
        section = kwargs.pop("section", None)
        super().__init__(**kwargs)
        self.section = section or Course._next_section(self.course_id)

        # These will be set by the scheduler after EnumSorts are created
        self._lab = None
        self._room = None
        self._time = None
        self._faculty = None

    @staticmethod
    def _next_section(course_id: str) -> int:
        Course._total_sections[course_id] += 1
        return Course._total_sections[course_id]

    def uid(self) -> str:
        return self.course_id

    def faculty(self) -> z3.ExprRef:
        return cast(z3.ExprRef, self._faculty)

    def __str__(self) -> str:
        """
        Pretty Print representation of a course is its course_id and section
        """
        return f"{self.course_id}.{self.section:02d}"

    def time(self) -> z3.ExprRef:
        """
        the z3 variable used for assigning a time slot
        """
        return cast(z3.ExprRef, self._time)

    def room(self) -> z3.ExprRef:
        """
        the z3 variable used for assigning a room
        """
        return cast(z3.ExprRef, self._room)

    def lab(self) -> z3.ExprRef:
        """
        the z3 variable used for assigning a lab
        """
        return cast(z3.ExprRef, self._lab)


class CourseInstance(BaseModel):
    """
    A course instance with a course, time, faculty, room, and lab.
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
