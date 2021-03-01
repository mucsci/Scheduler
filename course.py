# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from typing import List
from collections import defaultdict
import z3

class Course:

    _all = dict()
    total_sections = defaultdict(int)
    course_id = 0

    def min_id():
        """
        Returns the minimum number for the course IDs (always 0)
        """
        return 0

    def max_id():
        """
        Returns the maximum number for the course IDs
        """
        return Course.course_id - 1
    
    def get(id):
        """
        Given an ID of a course, return the instance
        """
        return Course._all[id]
    
    def __init__(self, subj : str, num : int, labs : List[str], rooms : List[str], faculty: str, conflicts : List[int]):
        # update id to be a unique identifier
        self.id = Course.course_id
        Course.course_id += 1
        # set subject, name, and section
        self.subject = subj
        self.num = num
        Course.total_sections[num] += 1
        self.section = Course.total_sections[num]
        self.labs = labs
        self.rooms = rooms
        self.conflicts = conflicts
        self.faculty = faculty
        Course._all[self.id] = self
        # z3 variables for each course -- must assign a timeslot, a room, and a lab
        self._time = z3.Int(f'{self.__repr__()}_time')
        self._room = z3.Int(f'{self.__repr__()}_room')
        self._lab = z3.Int(f'{self.__repr__()}_lab')
    

    def __repr__(self):
        """
        Pretty Print representation of a course is its subject, number, and section
        """
        return f'{self.subject}{self.num}.{self.section:02d}'

    def time(self):
        """
        the z3 variable used for assigning a time slot
        """
        return self._time

    def room(self):
        """
        the z3 variable used for assigning a room
        """
        return self._room

    def lab(self):
        """
        the z3 variable used for assigning a lab
        """
        return self._lab
