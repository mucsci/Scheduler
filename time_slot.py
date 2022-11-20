# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from dataclasses import dataclass
from identifiable import Identifiable
from typing import List
from day import Day
import json

import json_fix

def hhmm_to_timeid(hour : int, minute : int) -> int:
    return 60 * hour + minute

@dataclass
class TimeInstance:
    day : Day
    start : int
    duration : int

    def __init__(self, d : Day, h : int, m : int, dur : int):
        self.day = d
        self.start = hhmm_to_timeid(h, m)
        self.duration = dur
    
    def __init__(self, d : Day, begin : int, dur : int):
        self.day = d
        self.start = begin
        self.duration = dur
    
    def __repr__(self) -> str:
        return str({'day': str(self.day), 'start': self.start, 'duration': self.duration, 'stop': self.stop})

    def __json__(self) -> str:
        return repr(self)

    @property
    def stop(self) -> int:
        return self.start + self.duration

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
        self._lab_index : int = lab_index
        self._times : List[TimeInstance] = list(TimeInstance(t[0], hhmm_to_timeid(t[1], t[2]), t[3]) for t in times)

    def times(self) -> List[TimeInstance]:
        """
        Returns a list of Day - StartTime - Duration tuples
        """
        return self._times
    
    def lab_time(self) -> TimeInstance:
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
        MAX_TIME_DELTA = 70
        MAX_TIME_DELTA_NO_LAB = 60

        def diff_same_day(t1 : TimeInstance, t2 : TimeInstance) -> int:
            return min(abs(t1.start - t2.stop), abs(t2.start - t1.stop))
        def diff_diff_day(t1 : TimeInstance, t2 : TimeInstance) -> int:
            return abs(t1.start - t2.start)

        if self.has_lab() and other.has_lab():
            t1 : TimeInstance = self.lab_time()
            t2 : TimeInstance = other.lab_time()
            return (diff_same_day(t1, t2) if t1.day == t2.day else diff_diff_day(t1, t2)) <= MAX_TIME_DELTA
        else:
            if len(self.times()) != len(other.times()):
                return False
            for t1, t2 in zip(self.times(), other.times()):
                if t1.day == t2.day:
                    if diff_same_day(t1, t2) > MAX_TIME_DELTA_NO_LAB:
                        return False
            return True

    def overlaps(self, other) -> bool:
        """
        Returns true IFF this timeslot has any overlap with the passed time slot
        """
        return any(TimeSlot._overlaps(a, b) for a in self.times() for b in other.times())

    def lab_overlaps(self, other : TimeInstance) -> bool:
        """
        Returns true IFF this timeslot's two-hour block has any overlap with the passed time slot's two-hour block
        """
        return self.has_lab() and other.has_lab() and TimeSlot._overlaps(self.lab_time(), other.lab_time())

    def labs_on_same_day(self, other) -> bool:
        """
        Returns true IFF the labs of this timeslot and the passed are on the same day
        """
        return self.has_lab() and other.has_lab() and self.lab_time().day == other.lab_time().day

    @staticmethod
    def _overlaps(a : TimeInstance, b : TimeInstance) -> bool:
        """
        Internal utility function that returns true if two time slot instances overlap at any point
        """

        return (a.day == b.day) and (
            (a.start <= b.start <= a.stop) or
            (b.start <= a.start <= b.stop) or
            (a.start <= b.stop <= a.stop) or
            (b.start <= a.stop <= b.stop)
        )

    def in_time_ranges(self, ranges : List[TimeInstance]) -> bool:
        """
        Returns true if this time slot fits into the passed range list (day mask, start time, and end time)
        """
        #              on the same day       time fits in at least one available slot
        for t in self.times():
            fits = False
            for slot in ranges:
                if t.day == slot.day:
                    fits = fits or (t.day == slot.day and slot.start <= t.start and t.stop <= slot.stop)
            if not fits:
                return False
        return True
    
    def __repr__(self) -> str:
        return str(list(repr(t) for t in self.times()))

    def __str__(self) -> str:
        def time(t):
            return f'{t // 60:02d}:{t % 60:02d}'
        def str_for(idx, t):
            star = "*" if idx == self._lab_index else ""
            return f'{t.day.name} {time(t.start)}-{time(t.start + t.duration)}{star}'
        return ','.join(str_for(i, t) for i,t in enumerate(self.times()))