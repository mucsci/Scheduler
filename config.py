# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from typing import Iterable, Tuple
from time_slot import Day, TimeSlot, ClassTime

def lab_days() -> Iterable[Tuple[Day, int, int]]:
    """
    returns all possible lab day times
    """
    for labs in [Day.TUE, Day.THU]:
        for time in [(8, 0), (9, 0), (10, 0), (13, 0), (14, 0), (15, 0)]:
            yield (labs, time[0], time[1])
    for time in [(8, 0), (9, 0), (10, 0), (11, 0), (12, 0), (13, 0)]:
        yield (Day.WED, time[0], time[1])

def time_slots() -> Iterable[Tuple[Day, int, int]]:
    """
    returns all possible time slots
    """
    for l in lab_days():
        if l[0] != Day.WED:
            yield TimeSlot(*l, ClassTime.TR)
        yield TimeSlot(*l, ClassTime.MF_EARLY)
        yield TimeSlot(*l, ClassTime.MF_LATE)