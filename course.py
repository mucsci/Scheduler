from collections import defaultdict
from typing import DefaultDict, List, ClassVar

import z3

from lab import Lab
from room import Room
from faculty import Faculty
from time_slot import TimeSlot
from identifiable import Identifiable


class Course(Identifiable, default_id=0):

    _total_sections: ClassVar[DefaultDict[str, int]] = defaultdict(int)

    @staticmethod
    def _next_section(course_id: str) -> int:
        Course._total_sections[course_id] += 1
        return Course._total_sections[course_id]

    def __init__(self, credits: int, course_id: str, labs: List[str], rooms: List[str], faculties: List[str], conflicts: List[str]):
        # set credits and course identifier
        self.credits = credits
        self.course_id = course_id
        self.section = Course._next_section(course_id)
        # store labs, rooms, conflicts, and faculty
        self.labs = labs
        self.rooms = rooms
        self.conflicts = conflicts
        self.faculties = faculties
        # z3 variables for each course -- must assign a timeslot, a room, a lab, and a faculty
        self._lab = z3.Int(f'{repr(self)}_lab')
        self._room = z3.Int(f'{repr(self)}_room')
        self._time = z3.Int(f'{repr(self)}_time')
        self._faculty = z3.Int(f'{repr(self)}_faculty')

    def uid(self) -> str:
        return self.course_id

    def faculty(self) -> z3.ArithRef:
        return self._faculty

    def __str__(self) -> str:
        """
        Pretty Print representation of a course is its course_id and section
        """
        return f'{self.course_id}.{self.section:02d}'

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

    def evaluate(self, m: z3.ModelRef) -> dict:
        timeslot = m.eval(self.time()).as_long()
        room = m.eval(self.room()).as_long()
        faculty = m.eval(self.faculty()).as_long()
        lab = None if not self.labs else m.eval(self.lab()).as_long()
        return {'name': str(self), 'time': timeslot, 'room': room, 'lab': lab, 'faculty': faculty}

    def csv(self, m: z3.ModelRef) -> str:
        lookup = self.evaluate(m)
        timeslot = str(TimeSlot.get(lookup['time']))
        room = str(Room.get(lookup['room']))
        faculty = str(Faculty.get(lookup['faculty']))
        lab = 'None' if not self.labs else str(Lab.get(lookup['lab']))
        return f'{self},{faculty},{room},{lab},{timeslot}'
