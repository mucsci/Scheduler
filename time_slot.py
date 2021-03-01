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

class ClassTime(Enum):
    MF_EARLY = auto()
    MF_LATE = auto()
    TR = auto()

class TimeSlot:

    time_slot_id = 0
    _all = dict()

    def min_id():
        """
        Returns the maximum number for the course IDs (always 0)
        """
        return 0

    def max_id():
        """
        Returns the maximum number for the course IDs
        """
        return TimeSlot.time_slot_id - 1

    
    def get(id):
        """
        Given an ID of a time slot, return the instance
        """
        return TimeSlot._all[id]
    
    """
    A time slot class used to represent when a class can be held
    """
    def _make(self, two_hour_day : Day, start_time : int, class_time : ClassTime):
        """Constructs a time slot. For the sake of the CS department, we are guaranteed to have exactly one two-hour day.

        Parameters
        ----------
        two_hour_day : Day
            which day has a two-hour period that may be a lab
        start_time : int
            an integral number representing the time in minutes of the day
        class_time: ClassTime
            an enumeration specifying when the class will meet on the non-two-hour-day
            - `MF_EARLY`: the 50-minute meetings are during the early half of the period
            - `MF_LATE`: the 50-minute meetings are during the late half of the period
            - `TR`: a course is only offered as two 110-minute meetings
        """
        def init_class_time() -> List[Tuple[Day, int, int]]:
            SHORT = 50
            LONG = 110
            if class_time == ClassTime.MF_EARLY:
                return [(two_hour_day, start_time, LONG), (Day.MON, start_time - (start_time % 60), SHORT), (Day.FRI, start_time - (start_time % 60), SHORT)]
            elif class_time == ClassTime.MF_LATE:
                return [(two_hour_day, start_time, LONG), (Day.MON, start_time - (start_time % 60) + 60, SHORT), (Day.FRI, start_time - (start_time % 60) + 60, SHORT)]
            else:
                return [(two_hour_day, start_time, LONG), (Day.TUE ^ Day.THU ^ two_hour_day, start_time, LONG)]
        self._times = init_class_time()
    
    def __init__(self, two_hour_day : Day, hour : int, minute : int, class_time: ClassTime):
        """Constructs a time slot. For the sake of the CS department, we are guaranteed to have exactly one two-hour day.

        Parameters
        ----------
        two_hour_day : Day
            which day has a two-hour period that may be a lab
        hour : int
            an integral number representing the hour in which the class starts
        minute : int
            an integral number representing the minute of the hour in which the class starts
        class_time: ClassTime
            an enumeration specifying when the class will meet on the non-two-hour-day
            - `MF_EARLY`: the 50-minute meetings are during the early half of the period
            - `MF_LATE`: the 50-minute meetings are during the late half of the period
            - `TR`: a course is only offered as two 110-minute meetings
        """
        # update id to be a unique identifier
        self.id = TimeSlot.time_slot_id
        TimeSlot.time_slot_id += 1
        self._make(two_hour_day, hhmm_to_timeid(hour, minute), class_time)
        TimeSlot._all[self.id] = self

    def times(self) -> List[Tuple[Day, int, int]]:
        """
        Returns a list of Day - StartTime - Duration tuples
        """
        return self._times
    
    def two_hour_time(self) -> Tuple[Day, int, int]:
        """
        Returns only the two hour time (if necessary) for a lab
        """
        return self.times()[0]

    def next_to(self, other) -> bool:
        """
        Check if a time slot is logically next to another (same day + adjacent or next day + same time)
        """
        [d1, t1, _] = self.two_hour_time()
        [d2, t2, _] = other.two_hour_time()
        #       same day     within 180 minutes      different day within 60 minutes
        return (d1 == d2 and abs(t1 - t2) <= 180) or abs(t1 - t2) <= 60

    def overlaps(self, other) -> bool:
        """
        Returns true IFF this timeslot has any overlap with the passed time slot
        """
        return any(TimeSlot._overlaps(a, b) for a in self.times() for b in other.times())

    def lab_overlaps(self, other) -> bool:
        """
        Returns true IFF this timeslot's two-hour block has any overlap with the passed time slot's two-hour block
        """
        return TimeSlot._overlaps(self.two_hour_time(), other.two_hour_time())

    def labs_on_same_day(self, other) -> bool:
        """
        Returns true IFF the labs of this timeslot and the passed are on the same day
        """
        return self.two_hour_time()[0] == other.two_hour_time()[0]

    def _overlaps(a, b) -> bool:
        """
        Internal utility function that returns true if two time slot instances overlap
        """
        d1, t1, dur1 = a
        d2, t2, dur2 = b
        return d1 == d2 and ((t1 < t2 < t1 + dur1) or
                    (t1 < t2 + dur2 < t1 + dur1) or
                    (t2 < t1 < t2 + dur2) or
                    (t2 < t1 + dur1 < t2 + dur2))

    def in_time_range(self, mask : Day, start : int, stop : int) -> bool:
        """
        Rturns true if this time slot fits into the passed day mask, start time, and end time
        """
        if any(not (mask & d) for (d, _, _) in self.times()):
            return False
        return all(start <= t and t + dur <= stop for (_, t, dur) in self.times())

    def __repr__(self) -> str:
        return ','.join(f'{day.name} {t // 60:02d}:{t % 60:02d}-{(t + d) // 60:02d}:{(t + d) % 60:02d}' for (day, t, d) in self.times())