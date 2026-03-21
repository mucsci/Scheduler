"""
TypedDict definitions for JSON structures used throughout the scheduler.

This module provides type-safe definitions for all JSON data structures,
including configuration, API requests/responses, and schedule outputs.

**Usage:**
```python
from scheduler.json_types import CourseInstanceJSON
# TypedDict shapes for JSON payloads
```
"""

from typing import NotRequired, TypedDict


class TimeInstanceJSON(TypedDict):
    """
    JSON representation of a TimeInstance.

    **Usage:**
    ```python
    {"day": 0, "start": 480, "duration": 90}
    ```
    """

    day: int
    """
    Day enum value (e.g., 0)

    **Usage:**
    ```python
    {"day": 0, "start": 480, "duration": 90}
    ```
    """
    start: int
    """
    Timepoint in minutes (e.g., 0)

    **Usage:**
    ```python
    {"day": 0, "start": 480, "duration": 90}
    ```
    """

    duration: int
    """
    Duration in minutes (e.g., 120)

    **Usage:**
    ```python
    {"day": 0, "start": 480, "duration": 120}
    ```
    """


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
    """
    Lab string representation (e.g., "Lab 101")

    **Usage:**
    ```python
    {"course": "CS101.01", "faculty": "Dr. Smith", "lab": "Lab 101", "times": []}
    ```
    """

    times: list[TimeInstanceJSON]
    """
    List of time instances (e.g., `[{"day": 0, "start": 0, "duration": 120}]`)

    **Usage:**
    ```python
    {"course": "CS101.01", "faculty": "Dr. Smith", "times": [{"day": 0, "start": 0, "duration": 120}]}
    ```
    """

    lab_index: NotRequired[int | None]
    """
    Lab index (e.g., 0)

    **Usage:**
    ```python
    {"course": "CS101.01", "faculty": "Dr. Smith", "times": [], "lab_index": 0}
    ```
    """
