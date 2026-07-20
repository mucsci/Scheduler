"""
Supplemental TypedDict definitions for serialized schedule rows.

Runtime configuration and REST validation are owned by Pydantic models in
``scheduler.config`` and ``scheduler.server``. These types describe the JSON rows
emitted by ``JSONWriter`` and are not runtime validators.

**Usage:**
```python
from scheduler.json_types import CourseInstanceJSON
# TypedDict shapes for JSON payloads
```
"""

from typing import Literal, NotRequired, TypedDict


class TimeInstanceJSON(TypedDict):
    """
    JSON representation of a TimeInstance.

    **Usage:**
    ```python
    {"day": 1, "start": 480, "duration": 90}
    ```
    """

    day: int
    """
    Day enum value (1 for Monday through 5 for Friday)

    **Usage:**
    ```python
    {"day": 1, "start": 480, "duration": 90}
    ```
    """
    start: int
    """
    Start time in minutes since midnight

    **Usage:**
    ```python
    {"day": 1, "start": 480, "duration": 90}
    ```
    """

    duration: int
    """
    Duration in minutes (e.g., 120)

    **Usage:**
    ```python
    {"day": 1, "start": 480, "duration": 120}
    ```
    """

    delivery: Literal["in_person", "online"]
    """Meeting delivery mode: ``in_person`` or ``online``."""


class CourseInstanceJSON(TypedDict):
    """
    JSON representation of a CourseInstance.

    **Usage:**
    ```python
    {"course": "CS101.01", "faculty": "...", "times": [...]}
    ```
    """

    course: str  # Course string representation (e.g., "CS101.01")
    """
    Course string representation (e.g., "CS101.01")

    **Usage:**
    ```python
    {"course": "CS101.01", "faculty": "Dr. Smith", "times": []}
    ```
    """

    faculty: str
    """
    Faculty string representation (e.g., "Dr. Smith")

    **Usage:**
    ```python
    {"course": "CS101.01", "faculty": "Dr. Smith", "times": []}
    ```
    """

    room: NotRequired[str | None]
    """
    Room string representation (e.g., "Room 101")

    **Usage:**
    ```python
    {"course": "CS101.01", "faculty": "Dr. Smith", "room": "Room 101", "times": []}
    ```
    """

    lab: NotRequired[str | None]
    """Assigned lab resource name, or null for a no-lab section."""

    times: list[TimeInstanceJSON]
    """
    Ordered serialized meeting instances

    **Usage:**
    ```python
    {"course": "CS101.01", "faculty": "Dr. Smith", "times": [{"day": 1, "start": 480, "duration": 120}]}
    ```
    """

    lab_index: NotRequired[int | None]
    """Index of the lab meeting in ``times``, or null for a no-lab section."""

    reserve_room_during_lab: bool
    """Whether the lab-marked meeting also occupies the assigned room."""
