from typing import Literal, Self

from pydantic import BaseModel, ConfigDict, Field, model_serializer, model_validator

from .day import Day


class Duration(BaseModel):
    """
    A duration of a time slot in minutes.

    **Usage:**
    ```python
    Duration(duration=90)
    ```
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

        **Usage:**
        ```python
        d.model_dump()
        ```
        """
        return self.value

    @property
    def value(self) -> int:
        """Return the duration as an integer number of minutes.

        Args:
            None.

        Returns:
            Stored duration in minutes.

        Raises:
            None.

        Behavior:
            Returns the validated scalar unchanged and supplies the canonical value
            used by arithmetic, ordering, stringification, and serialization.
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

    def __repr__(self) -> str:
        return f"Duration(duration={self.value})"


class TimePoint(BaseModel):
    """
    A time point in minutes since midnight.

    **Usage:**
    ```python
    TimePoint.make_from(10, 30)
    ```
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

        **Usage:**
        ```python
        d.model_dump()
        ```
        """
        return self.value

    @staticmethod
    def make_from(hr: int, min: int) -> "TimePoint":
        """Construct a time point from separate hour and minute components.

        Args:
            hr: Hour component interpreted on a 24-hour clock.
            min: Minute component added to the supplied hour.

        Returns:
            Time point containing ``hr * 60 + min`` minutes after midnight.

        Raises:
            pydantic.ValidationError: If calculated data violates model validation.

        Behavior:
            Performs arithmetic conversion only; it does not wrap or independently
            constrain out-of-range hour or minute arguments.
        """
        return TimePoint(timepoint=(60 * hr + min))

    @property
    def hour(self):
        """Return the whole-hour component of this minute offset.

        Args:
            None.

        Returns:
            Integer floor division of total minutes by sixty.

        Raises:
            None.

        Behavior:
            Computes the component on access and does not normalize the stored value.
        """
        return self.timepoint // 60

    @property
    def minute(self):
        """Return the within-hour minute component of this offset.

        Args:
            None.

        Returns:
            Integer remainder after division by sixty.

        Raises:
            None.

        Behavior:
            Computes the component on access using Python modulo semantics.
        """
        return self.timepoint % 60

    @property
    def value(self) -> int:
        """Return the stored minute offset from midnight.

        Args:
            None.

        Returns:
            Integer number of minutes represented by this time point.

        Raises:
            None.

        Behavior:
            Returns the validated scalar unchanged for arithmetic and serialization.
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

    **Usage:**
    ```python
    TimeInstance(day=Day.MON, start=tp, duration=Duration(duration=90))
    ```
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

    delivery: Literal["in_person", "online"] = Field(
        default="in_person",
        description="Whether this meeting consumes a physical room",
    )
    """Meeting delivery mode used for room occupancy and serialized output."""

    @property
    def stop(self) -> TimePoint:
        """Calculate the exclusive stop point of this meeting interval.

        Args:
            None.

        Returns:
            New time point equal to start plus duration.

        Raises:
            pydantic.ValidationError: If the calculated time point is invalid.

        Behavior:
            Recomputes a new immutable value on every access without altering start
            or duration.
        """
        return TimePoint(timepoint=(self.start.value + self.duration.value))

    def __str__(self) -> str:
        suffix = "@online" if self.delivery == "online" else ""
        return f"{self.day.name} {str(self.start)}-{str(self.stop)}{suffix}"


class TimeSlot(BaseModel):
    """
    A time slot with a list of time instances and a lab index.

    **Usage:**
    ```python
    TimeSlot(times=[...], lab_index=0)
    ```
    """

    model_config = ConfigDict(extra="forbid", strict=True)
    """
    Configuration that forbids extra fields and requires strict values (@private)
    """

    times: list[TimeInstance] = Field(description="The list of time instances in the time slot")
    """
    The list of time instances in the time slot
    """

    lab_index: int | None = Field(
        default=None,
        description="Index of the single lab-marked meeting, or null for a no-lab pattern",
    )
    """
    Index of the single lab-marked meeting, or null for a no-lab pattern
    """

    max_time_gap: Duration = Field(
        default=Duration(duration=30),
        description="Maximum gap used by lecture and lab adjacency checks",
    )
    """
    Maximum gap used by meeting and lab adjacency checks
    """

    @model_validator(mode="after")
    def _validate_structure(self) -> "TimeSlot":
        if not self.times:
            raise ValueError("A time slot must contain at least one meeting")
        if self.lab_index is not None and not 0 <= self.lab_index < len(self.times):
            raise ValueError("Lab index must identify a meeting in the time slot")
        return self

    def __hash__(self) -> int:
        """
        Hash the time slot by its string representation

        **Usage:**
        ```python
        hash(slot)
        ```
        """
        return hash(str(self))

    def lab_time(self) -> TimeInstance | None:
        """Return the meeting marked as the lab portion of this time slot.

        Args:
            None.

        Returns:
            Lab meeting instance, or ``None`` when no lab index is present.

        Raises:
            None.

        Behavior:
            Uses only ``lab_index``; it does not infer lab status from duration or day.
            A slot mutated into an invalid index is treated as having no lab so
            independent audit code can report incompatibility instead of crashing.
        """
        if self.lab_index is None or not 0 <= self.lab_index < len(self.times):
            return None
        return self.times[self.lab_index]

    def has_lab(self) -> bool:
        """Report whether this slot explicitly marks one meeting as a lab.

        Args:
            None.

        Returns:
            ``True`` exactly when ``lab_index`` is not ``None``.

        Raises:
            None.

        Behavior:
            Checks marker presence only and does not dereference or validate the index.
        """
        return self.lab_index is not None

    def lecture_times(self) -> tuple[TimeInstance, ...]:
        """Return every non-lab meeting in configured order.

        Args:
            None.

        Returns:
            Tuple containing all meetings except the lab-marked index.

        Raises:
            None.

        Behavior:
            Preserves configured order and treats a no-lab slot as entirely lecture.
        """
        return tuple(time for index, time in enumerate(self.times) if index != self.lab_index)

    def physical_lecture_times(self) -> tuple[TimeInstance, ...]:
        """Return in-person non-lab meetings that consume the assigned room.

        Args:
            None.

        Returns:
            Ordered in-person lecture meeting tuple.

        Raises:
            None.

        Behavior:
            Excludes both the lab-marked meeting and meetings delivered online.
        """
        return tuple(time for time in self.lecture_times() if time.delivery == "in_person")

    def same_lectures(self, other: "TimeSlot") -> bool:
        """Compare two slots while ignoring their independently selected lab times.

        Args:
            other: Slot whose non-lab meetings are compared.

        Returns:
            Whether ordered lecture meetings are exactly equal.

        Raises:
            None.

        Behavior:
            Uses full meeting equality, including delivery mode, day, start, and duration.
        """
        return self.lecture_times() == other.lecture_times()

    def lab_overlaps_slot(self, other: "TimeSlot") -> bool:
        """Check whether this slot's lab overlaps any meeting in another slot.

        Args:
            other: Complete slot compared with this slot's lab meeting.

        Returns:
            False when this slot has no lab; otherwise whether it overlaps any other meeting.

        Raises:
            None.

        Behavior:
            Evaluates the marked lab against every meeting in ``other`` using exclusive stops.
        """
        lab = self.lab_time()
        return lab is not None and any(self._overlaps(lab, time) for time in other.times)

    @staticmethod
    def _diff_between_slots(t1: TimeInstance, t2: TimeInstance) -> Duration:
        """
        Calculate the minimum time difference between two time instances.

        **Usage:**
        ```python
        TimeSlot._diff_between_slots(t1, t2)
        ```

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
        """Determine whether two marked lab meetings satisfy adjacency semantics.

        Args:
            other: Time slot whose lab meeting is compared with this slot.

        Returns:
            Whether both labs exist and are within the configured maximum gap.

        Raises:
            None.

        Behavior:
            Same-day labs use minimum interval separation; labs on different days
            must overlap in clock time and start within ``max_time_gap``.
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
        """Determine whether any meeting pair satisfies lecture adjacency semantics.

        Args:
            other: Time slot compared with this slot.

        Returns:
            ``True`` when at least one pair is within ``max_time_gap``.

        Raises:
            None.

        Behavior:
            Scans meeting pairs in stored order and returns on the first witness;
            cross-day comparisons use corresponding clock-time separation.
        """
        for t1 in self.times:
            for t2 in other.times:
                if TimeSlot._diff_between_slots(t1, t2) <= self.max_time_gap:
                    return True
        return False

    def overlaps(self, other: "TimeSlot") -> bool:
        """Determine whether any same-day meeting intervals overlap.

        Args:
            other: Time slot compared with this slot.

        Returns:
            ``True`` when any meeting pair intersects with positive duration.

        Raises:
            None.

        Behavior:
            Evaluates the Cartesian product of meetings; touching endpoints are not
            considered overlaps because stop points are exclusive.
        """
        return any(TimeSlot._overlaps(a, b) for a in self.times for b in other.times)

    def lab_overlaps(self, other: "TimeSlot") -> bool:
        """Determine whether the marked lab meetings overlap on the same day.

        Args:
            other: Time slot whose lab meeting is compared with this slot.

        Returns:
            ``False`` if either lab is absent; otherwise interval overlap status.

        Raises:
            None.

        Behavior:
            Ignores all non-lab meetings and applies the same exclusive-stop overlap
            semantics used by complete time slots.
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

        **Usage:**
        ```python
        TimeSlot._overlaps(a, b)
        ```

        **Args:**
        - a: First time instance
        - b: Second time instance

        **Returns:**
        True if the time instances overlap, False otherwise
        """
        return (a.day == b.day) and (a.start < b.stop) and (b.start < a.stop)

    def in_time_ranges(self, ranges: list[TimeInstance]) -> bool:
        """Check whether every meeting is contained in an availability interval.

        Args:
            ranges: Day-specific inclusive-start, inclusive-stop availability windows.

        Returns:
            ``True`` only when every meeting has at least one containing range.

        Raises:
            None.

        Behavior:
            Matches ranges by weekday, permits different ranges to cover different
            meetings, and treats an empty meeting list as vacuously available.
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
        return str([repr(t) for t in self.times])

    def __str__(self) -> str:
        return ",".join(f"{str(t)}{'^' if i == self.lab_index else ''}" for i, t in enumerate(self.times))
