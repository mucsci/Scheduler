from dataclasses import dataclass

import z3
from pydantic import BaseModel, ConfigDict, Field, computed_field

from .time_slot import TimeInstance, TimeSlot


@dataclass
class Course:
    """
    A course with a course_id, section, credits, conflicts, potential labs, potential rooms, and potential faculty.

    **Usage:**
    ```python
    Course(course_id="CS 101", section=1, labs=[], rooms=[], conflicts=[], faculties=[])
    ```
    """

    course_id: str
    """
    The unique identifier for the course
    """

    credits: int
    """
    The number of credits for the course
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

    lab: z3.ExprRef | None = None
    """
    The z3 variable used for assigning a lab
    """

    room: z3.ExprRef | None = None
    """
    The z3 variable used for assigning a room
    """

    time: z3.ExprRef | None = None
    """
    The z3 variable used for assigning a time slot
    """

    faculty: z3.ExprRef | None = None
    """
    The z3 variable used for assigning a faculty
    """

    def __str__(self) -> str:
        """
        Pretty Print representation of a course is its course_id and section

        **Usage:**
        ```python
        str(course)
        ```
        """
        return f"{self.course_id}.{self.section:02d}"


class CourseInstance(BaseModel):
    """
    A course instance with a course, time, faculty, room, and lab.

    **Usage:**
    ```python
    CourseInstance(course=c, time=slot, faculty="Dr. Smith", room="R1", lab=None)
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

    lab: str | None = Field(default=None, description="The assigned lab")
    """
    The assigned lab
    """

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
        """Return the meeting index reserved for the assigned lab, when any.

        Args:
            None.

        Returns:
            Selected slot lab index, or ``None`` when no lab resource is assigned.

        Raises:
            None.

        Behavior:
            Hides the internal slot lab marker for documented no-lab assignments so
            external payloads consistently report both ``lab`` and ``lab_index`` null.
        """
        return self.time.lab_index if (self.lab is not None) else None

    def as_csv(self) -> str:
        """Serialize the assignment as one scheduler CSV row without a header.

        Args:
            None.

        Returns:
            ``course,faculty,room,lab,times`` using display representations.

        Raises:
            None.

        Behavior:
            Preserves meeting order and the lab caret marker for lab assignments;
            removes that internal marker when the decoded assignment has no lab.
        """
        room_str = str(self.room)
        lab_str = str(self.lab)
        time_str = str(self.time)
        if self.lab is None:
            time_str = time_str.replace("^", "")
        return f"{self.course},{self.faculty},{room_str},{lab_str},{time_str}"
