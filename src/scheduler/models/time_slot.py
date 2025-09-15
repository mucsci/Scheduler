from typing import Self

from pydantic import BaseModel, ConfigDict, Field, model_serializer

from .day import Day


class Duration(BaseModel):
    """
    A duration of a time slot in minutes.
    """

    model_config = ConfigDict(extra="forbid", strict=True)
    """
    Default configuration for the model (@private)
    """

    duration: int = Field(description="The duration of the time slot in minutes")
    """
    The duration of the time slot in minutes
    """

    @model_serializer
    def _serialize_model(self) -> int:
        """
        Serialize the duration to an integer
        """
        return self.value

    @property
    def value(self) -> int:
        """
        The value of the duration in minutes since midnight
        """
        return self.duration

    def __abs__(self) -> "Duration":
        return Duration(duration=abs(self.value))

    def __lt__(self, other: Self) -> bool:
        return self.value < other.value

    def __le__(self, other: Self) -> bool:
        return self.value <= other.value

    def __gt__(self, other: Self) -> bool:
        return self.value > other.value

    def __ge__(self, other: Self) -> bool:
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
    """
    A time point in minutes since midnight.
    """

    model_config = ConfigDict(extra="forbid", strict=True)
    """
    Default configuration for the model (@private)
    """

    timepoint: int = Field(description="The time point in minutes since midnight")
    """
    The time point in minutes since midnight
    """

    @model_serializer
    def _serialize_model(self) -> int:
        """
        Serialize the time point to an integer
        """
        return self.value

    @staticmethod
    def make_from(hr: int, min: int) -> "TimePoint":
        """
        Make a time point from an hour and minute
        """
        return TimePoint(timepoint=(60 * hr + min))

    @property
    def hour(self):
        """
        The hour of the time point
        """
        return self.timepoint // 60

    @property
    def minute(self):
        """
        The minute of the time point
        """
        return self.timepoint % 60

    @property
    def value(self) -> int:
        """
        The value of the time point in minutes since midnight
        """
        return self.timepoint

    def __add__(self, dur: Duration) -> "TimePoint":
        return TimePoint(timepoint=(self.value + dur.value))

    def __sub__(self, other: Self) -> Duration:
        return Duration(duration=(self.value - other.value))

    def __abs__(self) -> Duration:
        return Duration(duration=abs(self.value))

    def __lt__(self, other: Self) -> bool:
        return self.value < other.value

    def __le__(self, other: Self) -> bool:
        return self.value <= other.value

    def __gt__(self, other: Self) -> bool:
        return self.value > other.value

    def __ge__(self, other: Self) -> bool:
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
    """
    A time instance with a day, start time, and duration.
    """

    model_config = ConfigDict(extra="forbid", strict=True)
    """
    Default configuration for the model (@private)
    """

    day: Day = Field(description="The day of the time instance")
    """
    The day of the time instance
    """

    start: TimePoint = Field(description="The start time of the time instance")
    """
    The start time of the time instance
    """

    duration: Duration = Field(description="The duration of the time instance")
    """
    The duration of the time instance
    """

    @property
    def stop(self) -> TimePoint:
        """
        The stop time of the time instance
        """
        return TimePoint(timepoint=(self.start.value + self.duration.value))

    def __str__(self) -> str:
        return f"{self.day.name} {str(self.start)}-{str(self.stop)}"


class TimeSlot(BaseModel):
    """
    A time slot with a list of time instances and a lab index.
    """

    model_config = ConfigDict(extra="forbid", strict=True)
    """
    Configuration for the model which allows extra fields and is not strict (@private)
    """

    times: list[TimeInstance] = Field(description="The list of time instances in the time slot")
    """
    The list of time instances in the time slot
    """

    lab_index: int | None = Field(default=None, description="The index of the lab in the time slot")
    """
    The index of the lab in the time slot
    """

    max_time_gap: Duration = Field(default=Duration(duration=30), description="The maximum time gap between time slots")
    """
    The maximum time gap between time slots
    """

    def __hash__(self) -> int:
        """
        Hash the time slot by its string representation
        """
        return hash(str(self))

    def lab_time(self) -> TimeInstance | None:
        """
        Returns the time instance corresponding to the lab time slot

        **Returns:**
        The time instance of the lab
        None if the time slot does not have a lab
        """
        if self.lab_index is None:
            return None
        return self.times[self.lab_index]

    def has_lab(self) -> bool:
        """
        Check if the time slot has a lab

        **Returns:**
        True if the time slot has a lab.
        False otherwise
        """
        return self.lab_index is not None

    @staticmethod
    def _diff_between_slots(t1: TimeInstance, t2: TimeInstance) -> Duration:
        """
        Calculate the minimum time difference between two time instances.

        **Args:**
        - t1: First time instance
        - t2: Second time instance

        **Returns:**
        The minimum duration between the two time instances
        """
        if t1.day == t2.day:
            return min(abs(t1.start - t2.stop), abs(t2.start - t1.stop))
        else:
            return min(abs(t1.start - t2.start), abs(t1.stop - t2.stop))

    def lab_next_to(self, other: "TimeSlot") -> bool:
        """
        Check if the time slot has a lab that is next to another time slot

        **Returns:**
        True if the time slot has a lab that is next to another time slot.
        False otherwise
        """
        a = self.lab_time()
        b = other.lab_time()
        if a is None or b is None:
            return False
        if a.day != b.day:
            # different days -- check if the times logically overlap
            return (a.start < b.stop) and (b.start < a.stop) and abs(a.start - b.start) <= self.max_time_gap
        return (
            # same day -- check if the times are within the max time diff
            TimeSlot._diff_between_slots(a, b) <= self.max_time_gap
        )

    def lecture_next_to(self, other: "TimeSlot") -> bool:
        """
        Check if a time slot is logically next to another

        **Returns:**
        True if the time slot is logically next to another.
        False otherwise
        """
        for i1, t1 in enumerate(self.times):
            for i2, t2 in enumerate(other.times):
                if self.lab_index is None or other.lab_index is None:
                    continue
                if i1 == self.lab_index or i2 == other.lab_index:
                    continue
                if TimeSlot._diff_between_slots(t1, t2) <= self.max_time_gap:
                    return True
        return False

    def overlaps(self, other: "TimeSlot") -> bool:
        """
        Check if a time slot has any overlap with another time slot

        **Returns:**
        True if the time slot has any overlap with another time slot.
        False otherwise
        """
        return any(TimeSlot._overlaps(a, b) for a in self.times for b in other.times)

    def lab_overlaps(self, other: "TimeSlot") -> bool:
        """
        Check if a course's lab time slot has any overlap with another course's lab time slot

        **Returns:**
        True if the course's lab time slot has any overlap with another course's lab time slot.
        False otherwise
        """
        a: TimeInstance | None = self.lab_time()
        b: TimeInstance | None = other.lab_time()
        if a is None or b is None:
            return False
        return TimeSlot._overlaps(a, b)

    @staticmethod
    def _overlaps(a: TimeInstance, b: TimeInstance) -> bool:
        """
        Internal utility function that returns true if two time slot instances overlap at any point.

        **Args:**
        - a: First time instance
        - b: Second time instance

        **Returns:**
        True if the time instances overlap, False otherwise
        """
        return (a.day == b.day) and (a.start < b.stop) and (b.start < a.stop)

    def in_time_ranges(self, ranges: list[TimeInstance]) -> bool:
        """
        Check if a time slot fits into a list of time ranges

        **Returns:**
        True if the time slot fits into the list of time ranges
        False otherwise
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
