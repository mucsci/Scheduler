from collections import defaultdict
from typing import ClassVar, cast

import z3
from pydantic import BaseModel, Field, computed_field

from .identifiable import Identifiable
from .time_slot import TimeInstance, TimeSlot


class Course(Identifiable):
    credits: int
    course_id: str
    section: int | None = Field(default=None)
    labs: list[str]
    rooms: list[str]
    conflicts: list[str]
    faculties: list[str]

    _total_sections: ClassVar[defaultdict[str, int]] = defaultdict(int)

    _lab: z3.ExprRef | None
    _room: z3.ExprRef | None
    _time: z3.ExprRef | None
    _faculty: z3.ExprRef | None

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.section = kwargs.get("section", Course._next_section(self.course_id))

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
    course: Course = Field(exclude=True)
    time: TimeSlot = Field(exclude=True)
    faculty: str
    room: str | None = Field(default=None)
    lab: str | None = Field(default=None)

    @computed_field(alias="course")
    @property
    def course_str(self) -> str:
        return str(self.course)

    @computed_field
    @property
    def times(self) -> list[TimeInstance]:
        return self.time.times

    @computed_field
    @property
    def lab_index(self) -> int | None:
        return self.time.lab_index if (self.lab is not None) else None

    def as_csv(self):
        room_str = str(self.room)
        lab_str = str(self.lab)
        time_str = str(self.time)
        if self.lab is None:
            time_str = time_str.replace("^", "")
        return f"{self.course},{self.faculty},{room_str},{lab_str},{time_str}"
