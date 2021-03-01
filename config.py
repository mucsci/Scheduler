# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from typing import Iterable, Tuple
from time_slot import Day, TimeSlot

# other departments (such as math) would want to define all of their
# - 3 credit course times
# - 4 credit course times
# here -- programmatically would probably be best but a sequence of yield statements
# could also work

def time_slots(credits) -> Iterable[Tuple[Day, int, int]]:
    """
    returns all possible time slots
    """
    SHORT = 50
    LONG = 110
    if credits == 3:
        for h in range(8, 17):
            yield TimeSlot.make_mwf(h, 0, SHORT)
    elif credits == 4:
        # TR
        for (h, m) in [(8, 0), (9, 0), (10, 0), (13, 10), (14, 10), (15, 10)]:
            yield TimeSlot.make_tr(h, m, LONG, lab_index=0)
            yield TimeSlot.make_tr(h, m, LONG, lab_index=1)
            for idx,lab in enumerate([Day.TUE, Day.THU]):
                yield TimeSlot((Day.MON, h, 0, SHORT), (lab, h, m, LONG), (Day.FRI, h, 0, SHORT), lab_index=1)
                yield TimeSlot((Day.MON, h + 1, 0, SHORT), (lab, h, m, LONG), (Day.FRI, h + 1, 0, SHORT), lab_index=1)
        # W
        for (h, m) in [(8, 0), (9, 0), (10, 0), (11, 0), (12, 0), (13, 0)]:
            yield TimeSlot((Day.MON, h, 0, SHORT), (Day.WED, h, m, LONG), (Day.FRI, h, 0, SHORT), lab_index=1)
            yield TimeSlot((Day.MON, h + 1, 0, SHORT), (Day.WED, h, m, LONG), (Day.FRI, h + 1, 0, SHORT), lab_index=1)
        # evenings
        for (h, m) in [(17, 0), (17, 30), (18, 0), (18, 30)]:
            yield TimeSlot.make_mw(h, m, LONG, lab_index=0)
            yield TimeSlot.make_mw(h, m, LONG, lab_index=1)
            yield TimeSlot.make_tr(h, m, LONG, lab_index=0)
            yield TimeSlot.make_tr(h, m, LONG, lab_index=1)
