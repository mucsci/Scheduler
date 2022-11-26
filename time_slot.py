from dataclasses import dataclass
from identifiable import Identifiable
from typing import List
from day import Day


@dataclass
class Duration:
    duration: int

    @property
    def value(self):
        return self.duration

    def __abs__(self) -> 'Duration':
        return Duration(abs(self.value))

    def __lt__(self, other: 'Duration') -> bool:
        return self.value < other.value

    def __le__(self, other: 'Duration') -> bool:
        return self.value <= other.value

    def __gt__(self, other: 'Duration') -> bool:
        return self.value > other.value

    def __ge__(self, other: 'Duration') -> bool:
        return self.value >= other.value

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Duration):
            return NotImplemented
        return self.value == other.value

    def __ne__(self, other: object) -> bool:
        if not isinstance(other, Duration):
            return NotImplemented
        return self.value != other.value

    def __str__(self) -> str:
        return str(self.value)

    def __json__(self):
        return self.value

    def __repr__(self):
        return self.value


@dataclass
class TimePoint:
    timepoint: int

    def __init__(self, value):
        self.timepoint = value

    @staticmethod
    def make_from(hr: int, min: int) -> 'TimePoint':
        return TimePoint(60 * hr + min)

    @property
    def value(self):
        return self.timepoint

    def __add__(self, dur: Duration) -> 'TimePoint':
        return TimePoint(self.value + dur.value)

    def __sub__(self, other: 'TimePoint') -> Duration:
        return Duration(self.value - other.value)

    def __lt__(self, other: 'TimePoint') -> bool:
        return self.value < other.value

    def __le__(self, other: 'TimePoint') -> bool:
        return self.value <= other.value

    def __gt__(self, other: 'TimePoint') -> bool:
        return self.value > other.value

    def __ge__(self, other: 'TimePoint') -> bool:
        return self.value >= other.value

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, TimePoint):
            return NotImplemented
        return self.value == other.value

    def __ne__(self, other: object) -> bool:
        if not isinstance(other, TimePoint):
            return NotImplemented
        return self.value != other.value

    def __str__(self) -> str:
        return f'{self.value // 60:02d}:{self.value % 60:02d}'

    def __repr__(self):
        return self.value

    def __json__(self):
        return self.value


@dataclass
class TimeInstance:
    day: Day
    start: TimePoint
    duration: Duration

    @property
    def stop(self) -> TimePoint:
        return TimePoint(self.start.value + self.duration.value)

    def __repr__(self) -> str:
        return str({'day': str(self.day), 'start': self.start.value, 'duration': self.duration.value, 'stop': self.stop.value})

    def __str__(self) -> str:
        return f'{self.day.name} {str(self.start)}-{str(self.stop)}'

    def __json__(self):
        return {'day': self.day, 'start': self.start, 'duration': self.duration, 'stop': self.stop}


class TimeSlot(Identifiable, default_id=0):

    def __init__(self, times, lab_index=-1):
        """
        Constructs a time slot.

        Parameters
        ----------
        times : vararg of (Day, hour, minute, duration) tuples
            meeting times
        lab_index : int = -1
            an integral number representing index of which a lab period occurs (or none at all)
        """
        self._lab_index: int = lab_index
        self._times: List[TimeInstance] = times

    def times(self) -> List[TimeInstance]:
        """
        Returns a list of Day - StartTime - Duration tuples
        """
        return self._times

    def lab_time(self) -> TimeInstance:
        """
        Returns only the two hour time (if necessary) for a lab
        """
        return self.times()[self._lab_index]

    def has_lab(self) -> bool:
        """
        Returns True IFF the timeslot has a lab (two hour component)
        """
        return self._lab_index > 0

    def not_next_to(self, other: 'TimeSlot') -> bool:
        """
        Ensure that a time slot has padding between all possibly adjacent times
        """
        MAX_TIME_DIFF = Duration(50)

        def diff(t1: TimeInstance, t2: TimeInstance) -> Duration:
            return min(abs(t1.start - t2.stop), abs(t2.start - t1.stop))

        for t1 in self._times:
            for t2 in other._times:
                if t1.day == t2.day:
                    if diff(t1, t2) <= MAX_TIME_DIFF:
                        return False

        return True

    def next_to(self, other: 'TimeSlot') -> bool:
        """
        Check if a time slot is logically next to another (same day + adjacent or next day + same time)
        """
        MAX_TIME_DELTA = Duration(70)
        MAX_TIME_DELTA_NO_LAB = Duration(60)

        def diff(t1: TimeInstance, t2: TimeInstance) -> Duration:
            if t1.day == t2.day:
                return min(abs(t1.start - t2.stop), abs(t2.start - t1.stop))
            else:
                return abs(t1.start - t2.start)

        if self.has_lab() and other.has_lab():
            t1: TimeInstance = self.lab_time()
            t2: TimeInstance = other.lab_time()
            # forcefully disallow T/W split labs -- messes up fall schedules otherwise!
            # keep uncommented unless you really want this
            # if {t1.day, t2.day} == {Day.TUE, Day.WED}:
            #     return False
            if diff(t1, t2) > MAX_TIME_DELTA:
                return False
            for t1 in self.times():
                if self.lab_time() != t1:
                    for t2 in other.times():
                        if other.lab_time() != t2:
                            if t1.day == t2.day:
                                if diff(t1, t2) > MAX_TIME_DELTA_NO_LAB:
                                    return False
            return True
        else:
            if len(self.times()) != len(other.times()):
                return False
            for t1 in self._times:
                for t2 in other._times:
                    if t1.day == t2.day:
                        if diff(t1, t2) > MAX_TIME_DELTA_NO_LAB:
                            return False
            return True

    def overlaps(self, other: 'TimeSlot') -> bool:
        """
        Returns true IFF this timeslot has any overlap with the passed time slot
        """
        return any(TimeSlot._overlaps(a, b) for a in self.times() for b in other.times())

    def lab_overlaps(self, other: 'TimeSlot') -> bool:
        """
        Returns true IFF this timeslot's two-hour block has any overlap with the passed time slot's two-hour block
        """
        return self.has_lab() and other.has_lab() and TimeSlot._overlaps(self.lab_time(), other.lab_time())

    def labs_on_same_day(self, other: 'TimeSlot') -> bool:
        """
        Returns true IFF the labs of this timeslot and the passed are on the same day
        """
        return self.has_lab() and other.has_lab() and self.lab_time().day == other.lab_time().day

    @staticmethod
    def _overlaps(a: TimeInstance, b: TimeInstance) -> bool:
        """
        Internal utility function that returns true if two time slot instances overlap at any point
        """
        return (a.day == b.day) and (
            (a.start <= b.start < a.stop) or
            (a.start <= b.stop < a.stop) or
            (b.start <= a.start < b.stop) or
            (b.start <= a.stop < b.stop)
        )

    def in_time_ranges(self, ranges: List[TimeInstance]) -> bool:
        """
        Returns true if this time slot fits into the passed range list (day mask, start time, and end time)
        """
        return all(any((t.day == slot.day and slot.start <= t.start and t.stop <= slot.stop) for slot in ranges if t.day == slot.day) for t in self.times())

    def __repr__(self) -> str:
        return str(list(repr(t) for t in self.times()))

    def __str__(self) -> str:
        return ','.join(f'{str(t)}{"^" if i == self._lab_index else ""}' for i, t in enumerate(self.times()))
