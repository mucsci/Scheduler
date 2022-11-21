# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from lab import Lab
from room import Room
from time_slot import TimeSlot
from identifiable import Identifiable
from typing import DefaultDict, List
from collections import defaultdict
import z3


class Course(Identifiable, default_id=0):

    _total_sections: DefaultDict[int, int] = defaultdict(int)

    @staticmethod
    def _next_section(num):
        Course._total_sections[num] += 1
        return Course._total_sections[num]

    def __init__(self, credits: int, subj: str, num: int, labs: List[str], rooms: List[str], faculty: str, conflicts: List[int]):
        # set credits, subject, name, and section
        self.credits = credits
        self.subject = subj
        self.num = num
        self.section = Course._next_section(num)
        # store labs, rooms, conflicts, and faculty
        self.labs = labs
        self.rooms = rooms
        self.conflicts = conflicts
        self.faculty = faculty
        # z3 variables for each course -- must assign a timeslot, a room, and a lab
        self._lab = z3.Int(f'{repr(self)}_lab')
        self._room = z3.Int(f'{repr(self)}_room')
        self._time = z3.Int(f'{repr(self)}_time')
        
    def __str__(self) -> str:
        """
        Pretty Print representation of a course is its subject, number, and section
        """
        return f'{self.subject}{self.num}.{self.section:02d}'

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
        lab = None if not self.labs else m.eval(self.lab()).as_long()
        return {'name': str(self), 'time': timeslot, 'room': room, 'lab': lab, 'faculty': self.faculty}

    def csv(self, m: z3.ModelRef) -> str:
        timeslot = str(TimeSlot.get(m.eval(self.time()).as_long()))
        room = str(Room.get(m.eval(self.room()).as_long()))
        lab = 'None' if not self.labs else str(
            Lab.get(m.eval(self.lab()).as_long()))
        return f'{self},{self.faculty},{room},{lab},{timeslot}'
