# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from identifiable import Identifiable
from typing import List, Tuple
from day import Day

def hhmm_to_timeid(hour : int, minute : int) -> int:
    return 60 * hour + minute

class TimeSlot(Identifiable, default_id = 0):

    @staticmethod
    def make_mwf(hour, minute, duration):
        return TimeSlot(*((d, hour, minute, duration) for d in [Day.MON, Day.WED, Day.FRI]))
    
    @staticmethod
    def make_tr(hour, minute, duration, lab_index = -1):
        return TimeSlot(*((d, hour, minute, duration) for d in [Day.TUE, Day.THU]), lab_index=lab_index)
    
    @staticmethod
    def make_mw(hour, minute, duration, lab_index = -1):
        return TimeSlot(*((d, hour, minute, duration) for d in [Day.MON, Day.WED]), lab_index=lab_index)
    
    def __init__(self, *times, lab_index = -1):
        """
        Constructs a time slot.

        Parameters
        ----------
        times : vararg of (Day, hour, minute, duration) tuples
            meeting times
        lab_index : int = -1
            an integral number representing index of which a lab period occurs (or none at all)
        """
        self._lab_index = lab_index
        self._times = list((t[0], hhmm_to_timeid(t[1], t[2]), t[3]) for t in times)

    def times(self) -> List[Tuple[Day, int, int]]:
        """
        Returns a list of Day - StartTime - Duration tuples
        """
        return self._times
    
    def lab_time(self) -> Tuple[Day, int, int]:
        """
        Returns only the two hour time (if necessary) for a lab
        """
        if self._lab_index >= 0:
            return self.times()[self._lab_index]
        else:
            return None
    
    def has_lab(self) -> bool:
        """
        Returns True IFF the timeslot has a lab (two hour component)
        """
        return self._lab_index > 0

    def next_to(self, other) -> bool:
        """
        Check if a time slot is logically next to another (same day + adjacent or next day + same time)
        """
        if self.has_lab() and other.has_lab():
            def range(t):
                return t[0], t[1], t[1] + t[2] - 1
            day1, start1, stop1 = range(self.lab_time())
            day2, start2, stop2 = range(other.lab_time())
            # calculate time gap between for same day
            diff_same_day = min(abs(start1 - stop2), abs(start2 - stop1))
            diff_diff_day = abs(start1 - start2)
            return (diff_same_day if day1 == day2 else diff_diff_day) <= 70
        else:
            return False

    def overlaps(self, other) -> bool:
        """
        Returns true IFF this timeslot has any overlap with the passed time slot
        """
        return any(TimeSlot._overlaps(a, b) for a in self.times() for b in other.times())

    def lab_overlaps(self, other) -> bool:
        """
        Returns true IFF this timeslot's two-hour block has any overlap with the passed time slot's two-hour block
        """
        l1 = self.lab_time()
        l2 = other.lab_time()
        return l1 and l2 and TimeSlot._overlaps(l1, l2)

    def labs_on_same_day(self, other) -> bool:
        """
        Returns true IFF the labs of this timeslot and the passed are on the same day
        """
        return self.has_lab() and other.has_lab() and self.lab_time()[0] == other.lab_time()[0]

    @staticmethod
    def _overlaps(a, b) -> bool:
        """
        Internal utility function that returns true if two time slot instances overlap at any point
        """
        def range(t):
            return t[0], t[1], t[1] + t[2] - 1
        
        day1, start1, stop1 = range(a)
        day2, start2, stop2 = range(b)

        return (day1 == day2) and (
            (start1 <= start2 <= stop1) or
            (start2 <= start1 <= stop2) or
            (start1 <= stop2 <= stop1) or
            (start2 <= stop1 <= stop2)
        )

    def in_time_ranges(self, ranges) -> bool:
        """
        Returns true if this time slot fits into the passed range list (day mask, start time, and end time)
        """
        def check():
            for d1, slot_start, dur in self.times():
                yield any(d2 == d1 and start <= slot_start and  slot_start + dur <= stop for d2, start, stop in ranges)
        return all(x for x in check())
    
    def __repr__(self) -> str:
        def one(time):
            day, start, duration = time
            return {'day': day.name, 'start': start, 'duration': duration}
        return str(list(one(t) for t in self.times()))

    def __str__(self) -> str:
        def time(t):
            return f'{t // 60:02d}:{t % 60:02d}'
        def str_for(day, start, dur, idx):
            star = "*" if idx == self._lab_index else ""
            return f'{day.name} {time(start)}-{time(start + dur)}{star}'
        return ','.join(str_for(*t, i) for i,t in enumerate(self.times()))