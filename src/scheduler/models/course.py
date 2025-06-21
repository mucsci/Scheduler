from collections import defaultdict
from typing import DefaultDict, List, ClassVar, Optional
from pydantic import BaseModel, Field

import z3

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

    _lab: z3.ExprRef
    _room: z3.ExprRef
    _time: z3.ExprRef
    _faculty: z3.ExprRef

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.section = kwargs.get("section", Course._next_section(self.course_id))
        ctx = kwargs.get("ctx")
        
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
        return self._faculty

    def __str__(self) -> str:
        """
        Pretty Print representation of a course is its course_id and section
        """
        return f"{self.course_id}.{self.section:02d}"

    def time(self) -> z3.ExprRef:
        """
        the z3 variable used for assigning a time slot
        """
        return self._time

    def room(self) -> z3.ExprRef:
        """
        the z3 variable used for assigning a room
        """
        return self._room

    def lab(self) -> z3.ExprRef:
        """
        the z3 variable used for assigning a lab
        """
        return self._lab

class CourseInstance(BaseModel):
    course: Course
    time: TimeSlot
    faculty: str
    room: Optional[str] = Field(default=None)
    lab: Optional[str] = Field(default=None)

    def as_json(self):
        object = {}
        object["course"] = str(self.course)
        object["faculty"] = self.faculty
        if self.room:
            object["room"] = self.room
        if self.lab:
            object["lab"] = self.lab
        if self.time:
            object["times"] = [t.as_json() for t in self.time.times]
            if self.lab and self.time.lab_index is not None:
                object["lab_index"] = self.time.lab_index
        return object
    
    def as_csv(self):
        room_str = self.room if self.room else 'None'
        lab_str = self.lab if self.lab else 'None'
        time_str = str(self.time)
        if not self.lab:
            time_str = time_str.replace("^", "")
        return f"{self.course},{self.faculty},{room_str},{lab_str},{time_str}"
