# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from enum import Enum, IntFlag, auto
from typing import List, Tuple

def hhmm_to_timeid(hour : int, minute : int) -> int:
    return 60 * hour + minute

class Day(IntFlag):
    MON = auto()
    TUE = auto()
    WED = auto()
    THU = auto()
    FRI = auto()

class TimeSlot:

    _time_slot_id = 0
    _all = dict()

    def min_id():
        """
        Returns the minimum number for the course IDs (always 0)
        """
        return 0

    def max_id():
        """
        Returns the maximum number for the course IDs
        """
        return TimeSlot._time_slot_id - 1

    
    def get(id):
        """
        Given an ID of a time slot, return the instance
        """
        return TimeSlot._all[id]

    @classmethod
    def make_mwf(cls, hour, minute, duration):
        return cls(*((d, hour, minute, duration) for d in [Day.MON, Day.WED, Day.FRI]))
    
    @classmethod
    def make_tr(cls, hour, minute, duration, lab_index = -1):
        return cls(*((d, hour, minute, duration) for d in [Day.TUE, Day.THU]), lab_index=lab_index)
    
    @classmethod
    def make_mw(cls, hour, minute, duration, lab_index = -1):
        return cls(*((d, hour, minute, duration) for d in [Day.MON, Day.WED]), lab_index=lab_index)
    
    def __init__(self, *times, lab_index = -1):
        """Constructs a time slot. For the sake of the CS department, we are guaranteed to have exactly one two-hour day.

        Parameters
        ----------
        times : vararg of (Day, hour, minute, duration) tuples
            meeting times
        lab_index : int = -1
            an integral number representing index of which a lab period occurs (or none at all)
        """
        self.id = TimeSlot._time_slot_id
        self._lab_index = lab_index
        self._times = list((t[0], hhmm_to_timeid(t[1], t[2]), t[3]) for t in times)

        # update id to be a unique identifier
        TimeSlot._time_slot_id += 1
        TimeSlot._all[self.id] = self

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
            return (day1 == day2 and diff_same_day <= 70) or (day1 != day2 and diff_diff_day <= 70)
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

    def _overlaps(a, b) -> bool:
        """
        Internal utility function that returns true if two time slot instances overlap
        """
        def range(t):
            return t[0], t[1], t[1] + t[2] - 1
        
        day1, start1, stop1 = range(a)
        day2, start2, stop2 = range(b)

        return (day1 == day2) and (
            (start1 <= start2 <= stop1) or
            (start2 <= start1 <= stop2) or
            (start1 < stop2 <= stop1) or
            (start2 < stop1 <= stop2)
        )

    def in_time_range(self, mask : Day, start : int, stop : int) -> bool:
        """
        Rturns true if this time slot fits into the passed day mask, start time, and end time
        """
        if any(not (mask & d) for (d, _, _) in self.times()):
            return False
        return all(start <= t and t + dur <= stop for (_, t, dur) in self.times())

    def __repr__(self) -> str:
        return ','.join(f'{day.name} {t // 60:02d}:{t % 60:02d}-{(t + d) // 60:02d}:{(t + d) % 60:02d}{"*" if i == self._lab_index else ""}' for i,(day, t, d) in enumerate(self.times()))