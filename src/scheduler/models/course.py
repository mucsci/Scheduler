from collections import defaultdict
from typing import DefaultDict, List, ClassVar, Optional
from pydantic import BaseModel, Field

import z3

from .lab import Lab
from .room import Room
from .faculty import Faculty
from .time_slot import TimeSlot
from .identifiable import Identifiable


class Course(Identifiable):
    credits: int
    course_id: str
    section: int = Field(default=None)
    labs: List[str]
    rooms: List[str]
    conflicts: List[str]
    faculties: List[str]

    _total_sections: ClassVar[DefaultDict[str, int]] = defaultdict(int)

    _lab: z3.Int
    _room: z3.Int
    _time: z3.Int
    _faculty: z3.Int

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.section = kwargs.get("section", Course._next_section(self.course_id))
        ctx = kwargs.get("ctx")
        self._lab = z3.Int(f"{str(self)}_lab", ctx=ctx)
        self._room = z3.Int(f"{str(self)}_room", ctx=ctx)
        self._time = z3.Int(f"{str(self)}_time", ctx=ctx)
        self._faculty = z3.Int(f"{str(self)}_faculty", ctx=ctx)


    @staticmethod
    def _next_section(course_id: str) -> int:
        Course._total_sections[course_id] += 1
        return Course._total_sections[course_id]

    def uid(self) -> str:
        return self.course_id

    def faculty(self) -> z3.ArithRef:
        return self._faculty

    def __str__(self) -> str:
        """
        Pretty Print representation of a course is its course_id and section
        """
        return f"{self.course_id}.{self.section:02d}"

    def time(self) -> z3.ArithRef:
        """
        the z3 variable used for assigning a time slot
        """
        return self._time

    def room(self) -> z3.ArithRef:
        """
        the z3 variable used for assigning a room
        """
        return self._room

    def lab(self) -> z3.ArithRef:
        """
        the z3 variable used for assigning a lab
        """
        return self._lab


    def instance(self, m: z3.ModelRef) -> "CourseInstance":
        time = TimeSlot.get(m.eval(self.time()).as_long())
        faculty = Faculty.get(m.eval(self.faculty()).as_long())
        return CourseInstance(
            course=self,
            time=time,
            faculty=faculty,
            room=None if not isinstance(m.eval(self.room()), z3.IntNumRef) else Room.get(m.eval(self.room()).as_long()),
            lab=None if not isinstance(m.eval(self.lab()), z3.IntNumRef) else Lab.get(m.eval(self.lab()).as_long()),
        )

class CourseInstance(BaseModel):
    course: Course
    time: TimeSlot
    faculty: Faculty
    room: Optional[Room] = Field(default=None)
    lab: Optional[Lab] = Field(default=None)

    def as_json(self):
        object = {}
        object["course"] = str(self.course)
        object["faculty"] = self.faculty.name
        if self.room:
            object["room"] = self.room.name
        if self.lab:
            object["lab"] = self.lab.name
        if self.time:
            object["times"] = [t.as_json() for t in self.time.times]
            if self.lab and self.time.lab_index is not None:
                object["lab_index"] = self.time.lab_index
        return object
    
    def csv(self):
        room_str = self.room.name if self.room else 'None'
        lab_str = self.lab.name if self.lab else 'None'
        time_str = str(self.time)
        if not self.lab:
            time_str = time_str.replace("^", "")
        return f"{self.course},{self.faculty.name},{room_str},{lab_str},{time_str}"
