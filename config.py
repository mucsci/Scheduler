# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from typing import Iterable
from day import Day
from time_slot import Duration, TimeInstance, TimePoint, TimeSlot

# other departments (such as math) would want to define all of their
# - 3 credit course times
# - 4 credit course times
# here -- programmatically would probably be best but a sequence of yield statements
# could also work


def time_slots(credits : int) -> Iterable[TimeSlot]:
    """
    returns all possible time slots
    """
    SHORT : Duration = Duration(50)
    LONG : Duration = Duration(110)
    if credits == 3:
        for h in range(8, 17):
            yield TimeSlot.make_mwf(h, 0, SHORT)
    elif credits == 4:
        # TR
        for (h, m) in [(8, 0), (9, 0), (10, 0), (13, 10), (14, 10), (15, 10)]:
            yield TimeSlot.make_tr(TimePoint.make_from(h, m), LONG, 0)
            yield TimeSlot.make_tr(TimePoint.make_from(h, m), LONG, 1)
            for lab in [Day.TUE, Day.THU]:
                yield TimeSlot([
                    TimeInstance(Day.MON, TimePoint.make_from(h, 0), SHORT),
                    TimeInstance(lab, TimePoint.make_from(h, m), LONG),
                    TimeInstance(Day.FRI, TimePoint.make_from(h, 0), SHORT)
                ], lab_index=1)
                yield TimeSlot([
                    TimeInstance(
                        Day.MON, TimePoint.make_from(h + 1, 0), SHORT),
                    TimeInstance(lab, TimePoint.make_from(h, m), LONG),
                    TimeInstance(Day.FRI, TimePoint.make_from(h + 1, 0), SHORT)
                ], lab_index=1)
        # W
        for (h, m) in [(8, 0), (9, 0), (10, 0), (11, 0), (12, 0), (13, 0)]:
            yield TimeSlot([
                TimeInstance(Day.MON, TimePoint.make_from(h, 0), SHORT),
                TimeInstance(Day.WED, TimePoint.make_from(h, m), LONG),
                TimeInstance(Day.FRI, TimePoint.make_from(h, 0), SHORT)
            ], lab_index=1)
            yield TimeSlot([
                TimeInstance(Day.MON, TimePoint.make_from(h + 1, 0), SHORT),
                TimeInstance(Day.WED, TimePoint.make_from(h, m), LONG),
                TimeInstance(Day.FRI, TimePoint.make_from(h + 1, 0), SHORT)
            ], lab_index=1)
        # evenings
        for (h, m) in [(17, 0), (17, 30), (18, 0), (18, 30)]:
            yield TimeSlot.make_mw(TimePoint.make_from(h, m), LONG, 0)
            yield TimeSlot.make_mw(TimePoint.make_from(h, m), LONG, 1)
            yield TimeSlot.make_tr(TimePoint.make_from(h, m), LONG, 0)
            yield TimeSlot.make_tr(TimePoint.make_from(h, m), LONG, 1)
