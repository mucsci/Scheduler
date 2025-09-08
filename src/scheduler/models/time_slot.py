from typing import ClassVar

from pydantic import BaseModel, Field, model_serializer

from .day import Day
from .identifiable import Identifiable


class Duration(BaseModel):
    duration: int

    @model_serializer
    def serialize_model(self) -> int:
        return self.value

    @property
    def value(self) -> int:
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

    def __repr__(self):
        return self.value


class TimePoint(BaseModel):
    timepoint: int

    @model_serializer
    def serialize_model(self) -> int:
        return self.value

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
    def value(self) -> int:
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


class TimeInstance(BaseModel):
    day: Day
    start: TimePoint
    duration: Duration

    @property
    def stop(self) -> TimePoint:
        return TimePoint(timepoint=(self.start.value + self.duration.value))

    def __str__(self) -> str:
        return f"{self.day.name} {str(self.start)}-{str(self.stop)}"


class TimeSlot(Identifiable):
    times: list[TimeInstance]
    lab_index: int | None = Field(default=None)

    _MAX_TIME_DIFF_BETWEEN_SLOTS: ClassVar[Duration] = Duration(duration=30)

    def __hash__(self) -> int:
        return hash(self.id)

    def lab_time(self) -> TimeInstance | None:
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

    @staticmethod
    def _diff_between_slots(t1: TimeInstance, t2: TimeInstance) -> Duration:
        if t1.day == t2.day:
            return min(abs(t1.start - t2.stop), abs(t2.start - t1.stop))
        else:
            return min(abs(t1.start - t2.start), abs(t1.stop - t2.stop))

    def lab_next_to(self, other: "TimeSlot") -> bool:
        a = self.lab_time()
        b = other.lab_time()
        if a is None or b is None:
            return False
        if a.day != b.day:
            # different days -- check if the times logically overlap
            return (
                (a.start < b.stop)
                and (b.start < a.stop)
                and abs(a.start - b.start) <= TimeSlot._MAX_TIME_DIFF_BETWEEN_SLOTS
            )
        return (
            # same day -- check if the times are within the max time diff
            TimeSlot._diff_between_slots(a, b) <= TimeSlot._MAX_TIME_DIFF_BETWEEN_SLOTS
        )

    def lecture_next_to(self, other: "TimeSlot") -> bool:
        """
        Check if a time slot is logically next to another
        (same day + adjacent or next day + same time)
        """
        for i1, t1 in enumerate(self.times):
            for i2, t2 in enumerate(other.times):
                if self.lab_index is None or other.lab_index is None:
                    continue
                if i1 == self.lab_index or i2 == other.lab_index:
                    continue
                if TimeSlot._diff_between_slots(t1, t2) <= TimeSlot._MAX_TIME_DIFF_BETWEEN_SLOTS:
                    return True
        return False

    def overlaps(self, other: "TimeSlot") -> bool:
        """
        Returns true IFF this timeslot has any overlap with the passed time slot
        """
        return any(TimeSlot._overlaps(a, b) for a in self.times for b in other.times)

    def lab_overlaps(self, other: "TimeSlot") -> bool:
        """
        Returns true IFF this timeslot's two-hour block has any overlap
        with the passed time slot's two-hour block
        """
        a: TimeInstance | None = self.lab_time()
        b: TimeInstance | None = other.lab_time()
        if a is None or b is None:
            return False
        return TimeSlot._overlaps(a, b)

    @staticmethod
    def _overlaps(a: TimeInstance, b: TimeInstance) -> bool:
        """
        Internal utility function that returns true if two time slot instances overlap at any point
        """
        return (a.day == b.day) and (a.start < b.stop) and (b.start < a.stop)

    def in_time_ranges(self, ranges: list[TimeInstance]) -> bool:
        """
        Returns true if this time slot fits into the passed range list
        (day mask, start time, and end time)
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
        return ",".join(f"{str(t)}{'^' if i == self.lab_index else ''}" for i, t in enumerate(self.times))
