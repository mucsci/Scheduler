import csv
import io
from dataclasses import dataclass, field

from pydantic import BaseModel, ConfigDict, Field, computed_field

from .time_slot import TimeInstance, TimeSlot


@dataclass
class Course:
    """
    A course with a course_id, section, credits, conflicts, potential labs, potential rooms, and potential faculty.

    **Usage:**
    ```python
    Course(course_id="CS 101", section=1, credits=3, capacity=30, labs=[], rooms=[], conflicts=[], faculties=[])
    ```
    """

    course_id: str
    """
    The base course identifier; repeated configured values are distinguished by section
    """

    credits: int
    """
    The number of credits for the course
    """

    capacity: int
    """
    Expected section enrollment that the assigned room and lab must accommodate
    """

    section: int
    """
    The section number for the course
    """

    labs: list[str]
    """
    The list of potential labs for the course
    """

    rooms: list[str]
    """
    The list of potential rooms for the course
    """

    conflicts: list[str]
    """
    The list of course conflicts for the course
    """

    faculties: list[str]
    """
    The list of potential faculty for the course
    """

    section_id: str | None = None
    """Explicit stable section suffix, or null when input-order numbering is used."""

    modality: str = "in_person"
    """Configured course delivery modality."""

    required_room_features: frozenset[str] = field(default_factory=frozenset)
    """Feature tags required on the selected lecture room."""

    required_lab_features: frozenset[str] = field(default_factory=frozenset)
    """Feature tags required on every selected lab."""

    reserve_room_during_lab: bool = True
    """Whether lab meetings also occupy the assigned lecture room."""

    time: object | None = field(default=None, repr=False, compare=False)
    """Legacy mirror of the solver-owned time assignment variable, when initialized."""

    faculty: object | None = field(default=None, repr=False, compare=False)
    """Legacy mirror of the solver-owned faculty assignment variable, when initialized."""

    room: object | None = field(default=None, repr=False, compare=False)
    """Legacy mirror of the solver-owned room assignment variable, when initialized."""

    lab: object | None = field(default=None, repr=False, compare=False)
    """Legacy mirror of the solver-owned lab assignment variable, when initialized."""

    def __str__(self) -> str:
        """
        Pretty Print representation of a course is its course_id and section

        **Usage:**
        ```python
        str(course)
        ```
        """
        suffix = self.section_id or f"{self.section:02d}"
        return f"{self.course_id}.{suffix}"


class CourseInstance(BaseModel):
    """
    A decoded course assignment with its meetings, faculty, room, and optional lab.

    **Usage:**
    ```python
    CourseInstance(course=c, time=slot, faculty="Dr. Smith", room="R1")
    ```
    """

    model_config = ConfigDict(extra="forbid", strict=True, arbitrary_types_allowed=True)
    """
    Configuration for the model which forbids extra fields and is strict (@private)
    """

    course: Course = Field(description="The corresponding course object", exclude=True)
    """
    The corresponding course object
    """

    time: TimeSlot = Field(description="The assigned time slot", exclude=True)
    """
    The assigned time slot
    """

    faculty: str = Field(description="The assigned faculty")
    """
    The assigned faculty
    """

    room: str | None = Field(default=None, description="The assigned room")
    """
    The assigned room
    """

    lab: str | None = Field(default=None, description="The assigned lab, or null for a no-lab section")
    """The assigned lab resource name."""

    @computed_field(alias="course")
    @property
    def course_str(self) -> str:
        """Return the stable display identifier for the assigned course section.

        Args:
            None.

        Returns:
            Course identifier plus zero-padded section number.

        Raises:
            None.

        Behavior:
            Delegates to the underlying course string representation and is emitted
            under the serialized ``course`` alias while the course object is excluded.
        """
        return str(self.course)

    @computed_field
    @property
    def times(self) -> list[TimeInstance]:
        """Expose the ordered meeting instances from the selected time slot.

        Args:
            None.

        Returns:
            The selected slot's meeting list in configured pattern order.

        Raises:
            None.

        Behavior:
            Returns the underlying list without reordering and includes it as the
            serialized ``times`` computed field.
        """
        return self.time.times

    @computed_field
    @property
    def lab_index(self) -> int | None:
        """Return the lab meeting's index in ``times`` when a lab is assigned.

        Args:
            None.

        Returns:
            The selected slot's lab index, or ``None`` for a no-lab section.

        Raises:
            None.

        Behavior:
            Exposes the selected pattern marker only when a concrete lab resource
            was decoded.
        """
        return self.time.lab_index if self.lab is not None else None

    @computed_field
    @property
    def reserve_room_during_lab(self) -> bool:
        """Return whether the lab meeting also occupies the assigned room.

        Args:
            None.

        Returns:
            The normalized course policy controlling lab-time room occupancy.

        Raises:
            None.

        Behavior:
            Exposes the compatibility course mirror as serialized metadata so
            schedule consumers can render physical room use correctly.
        """
        return self.course.reserve_room_during_lab

    def as_csv(self) -> str:
        """Serialize the assignment as one scheduler CSV row without a header.

        Args:
            None.

        Returns:
            RFC-compatible ``course,faculty,room,lab,times`` fields using display
            representations. Missing room and lab assignments are empty fields.

        Raises:
            None.

        Behavior:
            Uses the standard CSV writer so commas, quotes, and newlines are escaped.
            Preserves meeting order and marks the lab meeting with a caret. For a
            no-lab section, any internal marker is omitted.
        """
        room_str = self.room or ""
        time_str = str(self.time)
        if self.lab is None:
            time_str = time_str.replace("^", "")
        output = io.StringIO(newline="")
        csv.writer(output, lineterminator="").writerow(
            [str(self.course), self.faculty, room_str, self.lab or "", time_str]
        )
        return output.getvalue()
