"""
TypedDict definitions for JSON structures used throughout the scheduler.

This module provides type-safe definitions for all JSON data structures,
including configuration, API requests/responses, and schedule outputs.
"""

from typing import NotRequired, TypedDict


class TimeInstanceJSON(TypedDict):
    """JSON representation of a TimeInstance."""

    day: int
    """
    Day enum value (e.g., 0)
    """
    start: int
    """
    Timepoint in minutes (e.g., 0)
    """

    duration: int
    """
    Duration in minutes (e.g., 120)
    """


class CourseInstanceJSON(TypedDict):
    """JSON representation of a CourseInstance."""

    course: str  # Course string representation (e.g., "CS101.01")
    """
    Course string representation (e.g., "CS101.01")
    """

    faculty: str
    """
    Faculty string representation (e.g., "Dr. Smith")
    """

    room: NotRequired[str | None]
    """
    Room string representation (e.g., "Room 101")
    """

    lab: NotRequired[str | None]
    """
    Lab string representation (e.g., "Lab 101")
    """

    times: list[TimeInstanceJSON]
    """
    List of time instances (e.g., [{"day": 0, "start": 0, "duration": 120}])
    """

    lab_index: NotRequired[int | None]
    """
    Lab index (e.g., 0)
    """
