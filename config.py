from typing import Iterable
from day import Day
from time_slot import Duration, TimeInstance, TimePoint, TimeSlot


def time_slots(credits: int) -> Iterable[TimeSlot]:
    """
    returns all possible time slots
    """
    SHORT: Duration = Duration(50)
    LONG: Duration = Duration(110)
    if credits == 3:
        for (h, m) in [(8, 0), (9, 0), (10, 0), (11, 0), (12, 0), (13, 0), (14, 0), (15, 0), (16, 0)]:
            yield TimeSlot([
                TimeInstance(Day.MON, TimePoint.make_from(h, m), SHORT),
                TimeInstance(Day.WED, TimePoint.make_from(h, m), SHORT),
                TimeInstance(Day.FRI, TimePoint.make_from(h, m), SHORT)
            ])
    elif credits == 4:
        # TR
        for (h, m) in [(8, 0), (9, 0), (10, 0), (13, 10), (14, 10), (15, 10)]:
            yield TimeSlot([
                TimeInstance(Day.TUE, TimePoint.make_from(h, m), LONG),
                TimeInstance(Day.THU, TimePoint.make_from(h, m), LONG)
            ], lab_index=1)
            for lab in [Day.TUE, Day.THU]:
                for hh in [h, h + 1]:
                    yield TimeSlot([
                        TimeInstance(
                            Day.MON, TimePoint.make_from(hh, 0), SHORT),
                        TimeInstance(lab, TimePoint.make_from(h, m), LONG),
                        TimeInstance(
                            Day.FRI, TimePoint.make_from(hh, 0), SHORT)
                    ], lab_index=1)
        # W
        for (h, m) in [(8, 0), (9, 0), (10, 0), (11, 0), (12, 0), (13, 0)]:
            for hh in [h, h + 1]:
                yield TimeSlot([
                    TimeInstance(Day.MON, TimePoint.make_from(hh, 0), SHORT),
                    TimeInstance(Day.WED, TimePoint.make_from(h, m), LONG),
                    TimeInstance(Day.FRI, TimePoint.make_from(hh, 0), SHORT)
                ], lab_index=1)
        # evenings
        for (h, m) in [(16, 0), (16, 30), (17, 0), (17, 30), (18, 0), (18, 30)]:
            for (d1, d2) in [(Day.MON, Day.WED), (Day.TUE, Day.THU)]:
                yield TimeSlot([
                    TimeInstance(d1, TimePoint.make_from(h, m), LONG),
                    TimeInstance(d2, TimePoint.make_from(h, m), LONG)
                ], lab_index=1)
