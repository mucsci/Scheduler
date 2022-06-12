# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from enum import IntFlag, auto

class Day(IntFlag):
    MON = auto()
    TUE = auto()
    WED = auto()
    THU = auto()
    FRI = auto()

    def __str__(self):
        return '|'.join(val.name for val in Day if self.value & val)

    def __repr__(self):
        """
        Pretty Print representation of a course is its subject, number, and section
        """
        return '|'.join(val.name for val in Day if self.value & val)
