from typing import List, Optional

from pydantic import BaseModel, Field

from .identifiable import Identifiable
from .day import Day


class Duration(BaseModel):
    duration: int

    @property
    def value(self):
        return self.duration

    def __abs__(self) -> "Duration":
        return Duration(duration=abs(self.value))

    def __lt__(self, other: "Duration") -> bool:
        return self.value < other.value

    def __le__(self, other: "Duration") -> bool:
        return self.value <= other.value

    def __gt__(self, other: "Duration") -> bool:
        return self.value > other.value

    def __ge__(self, other: "Duration") -> bool:
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

    def as_json(self):
        return self.value

    def __repr__(self):
        return self.value


class TimePoint(BaseModel):
    timepoint: int

    @staticmethod
    def make_from(hr: int, min: int) -> "TimePoint":
        return TimePoint(timepoint=(60 * hr + min))

    @property
    def hour(self):
        return self.timepoint // 60
    
    @property
    def minute(self):
        return self.timepoint % 60

    @property
    def value(self):
        return self.timepoint

    def __add__(self, dur: Duration) -> "TimePoint":
        return TimePoint(timepoint=(self.value + dur.value))

    def __sub__(self, other: "TimePoint") -> Duration:
        return Duration(duration=(self.value - other.value))

    def __abs__(self) -> Duration:
        return Duration(duration=abs(self.value))

    def __lt__(self, other: "TimePoint") -> bool:
        return self.value < other.value

    def __le__(self, other: "TimePoint") -> bool:
        return self.value <= other.value

    def __gt__(self, other: "TimePoint") -> bool:
        return self.value > other.value

    def __ge__(self, other: "TimePoint") -> bool:
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
        return f"{self.value // 60:02d}:{self.value % 60:02d}"

    def __repr__(self) -> str:
        return f"TimePoint(timepoint={self.value})"

    def as_json(self):
        return self.value


class TimeInstance(BaseModel):
    day: Day
    start: TimePoint
    duration: Duration

    @property
    def stop(self) -> TimePoint:
        return TimePoint(timepoint=(self.start.value + self.duration.value))

    def __str__(self) -> str:
        return f"{self.day.name} {str(self.start)}-{str(self.stop)}"

    def as_json(self):
        return {"day": self.day, "start": self.start.timepoint, "duration": self.duration.duration}


class TimeSlot(Identifiable):
    times: List[TimeInstance]
    lab_index: Optional[int] = Field(default=None)

    def lab_time(self) -> Optional[TimeInstance]:
        """
        Returns only the two hour time (if necessary) for a lab
        """
        if self.lab_index is not None:
            return self.times[self.lab_index]
        else:
            return None

    def has_lab(self) -> bool:
        """
        Returns True IFF the timeslot has a lab (two hour component)
        """
        return self.lab_index is not None

    def not_next_to(self, other: "TimeSlot") -> bool:
        """
        Ensure that a time slot has padding between all possibly adjacent times
        """
        MAX_TIME_DIFF = Duration(duration=50)

        def diff(t1: TimeInstance, t2: TimeInstance) -> Duration:
            return min(abs(t1.start - t2.stop), abs(t2.start - t1.stop))

        for t1 in self.times:
            for t2 in other.times:
                if t1.day == t2.day:
                    if diff(t1, t2) <= MAX_TIME_DIFF:
                        return False

        return True

    def next_to_tues_wed(self, other: "TimeSlot") -> bool:
        if self.has_lab() and other.has_lab():
            t1: Optional[TimeInstance] = self.lab_time()
            t2: Optional[TimeInstance] = other.lab_time()
            if t1 is None or t2 is None:
                return False
            # forcefully disallow T/W split labs -- messes up fall schedules otherwise!
            if {t1.day, t2.day} == {Day.TUE, Day.WED}:
                return False
        return True

    def lab_starts_with_lecture(self) -> bool:
        if not self.has_lab():
            return True
        lab_start = self.lab_time().start
        lecture_start = self.times[0].start
        return abs(lecture_start - lab_start) <= Duration(duration=10)

    def next_to(self, other: "TimeSlot") -> bool:
        """
        Check if a time slot is logically next to another (same day + adjacent or next day + same time)
        """
        MAX_TIME_DELTA = Duration(duration=70)
        MAX_TIME_DELTA_NO_LAB = Duration(duration=60)

        def diff(t1: TimeInstance, t2: TimeInstance) -> Duration:
            if t1.day == t2.day:
                return min(abs(t1.start - t2.stop), abs(t2.start - t1.stop))
            else:
                return abs(t1.start - t2.start)

        if self.has_lab() and other.has_lab():
            t1: Optional[TimeInstance] = self.lab_time()
            t2: Optional[TimeInstance] = other.lab_time()
            if t1 is None or t2 is None:
                return False
            # forcefully disallow T/W split labs -- messes up fall schedules otherwise!
            # keep uncommented unless you really want this
            # if {t1.day, t2.day} == {Day.TUE, Day.WED}:
            #     return False
            if diff(t1, t2) > MAX_TIME_DELTA:
                return False
            for t1 in self.times:
                if self.lab_time() != t1:
                    for t2 in other.times:
                        if other.lab_time() != t2:
                            if t1.day == t2.day:
                                if diff(t1, t2) > MAX_TIME_DELTA_NO_LAB:
                                    return False
            return True
        else:
            if len(self.times) != len(other.times):
                return False
            for t1 in self.times:
                for t2 in other.times:
                    if t1.day == t2.day:
                        if diff(t1, t2) > MAX_TIME_DELTA_NO_LAB:
                            return False
            return True

    def overlaps(self, other: "TimeSlot") -> bool:
        """
        Returns true IFF this timeslot has any overlap with the passed time slot
        """
        return any(
            TimeSlot._overlaps(a, b) for a in self.times for b in other.times
        )

    def lab_overlaps(self, other: "TimeSlot") -> bool:
        """
        Returns true IFF this timeslot's two-hour block has any overlap with the passed time slot's two-hour block
        """
        a: Optional[TimeInstance] = self.lab_time()
        b: Optional[TimeInstance] = other.lab_time()
        if a is None or b is None:
            return False
        return TimeSlot._overlaps(a, b)

    def labs_on_same_day(self, other: "TimeSlot") -> bool:
        """
        Returns true IFF the labs of this timeslot and the passed are on the same day
        """
        a: Optional[TimeInstance] = self.lab_time()
        b: Optional[TimeInstance] = other.lab_time()
        if a is None or b is None:
            return False
        return a.day == b.day

    @staticmethod
    def _overlaps(a: TimeInstance, b: TimeInstance) -> bool:
        """
        Internal utility function that returns true if two time slot instances overlap at any point
        """
        return (a.day == b.day) and (a.start < b.stop) and (b.start < a.stop)

    def in_time_ranges(self, ranges: List[TimeInstance]) -> bool:
        """
        Returns true if this time slot fits into the passed range list (day mask, start time, and end time)
        """
        return all(
            any(
                (t.day == slot.day and slot.start <= t.start and t.stop <= slot.stop)
                for slot in ranges
                if t.day == slot.day
            )
            for t in self.times
        )

    def __repr__(self) -> str:
        return str(list(repr(t) for t in self.times))

    def __str__(self) -> str:
        return ",".join(
            f'{str(t)}{"^" if i == self.lab_index else ""}'
            for i, t in enumerate(self.times)
        )

    def as_json(self):
        object = {"times": [t.as_json() for t in self.times]}
        if self.lab_index is not None:
            object["lab_index"] = self.lab_index
        return object
