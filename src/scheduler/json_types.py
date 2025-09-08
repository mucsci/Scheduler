"""
TypedDict definitions for JSON structures used throughout the scheduler.

This module provides type-safe definitions for all JSON data structures,
including configuration, API requests/responses, and schedule outputs.
"""

from typing import NotRequired, TypedDict


class TimeInstanceJSON(TypedDict):
    """JSON representation of a TimeInstance."""

    day: int  # Day enum value
    start: int  # Timepoint in minutes
    duration: int  # Duration in minutes


class CourseInstanceJSON(TypedDict):
    """JSON representation of a CourseInstance."""

    course: str  # Course string representation (e.g., "CS101.01")
    faculty: str
    room: NotRequired[str | None]
    lab: NotRequired[str | None]
    times: list[TimeInstanceJSON]
    lab_index: NotRequired[int | None]
