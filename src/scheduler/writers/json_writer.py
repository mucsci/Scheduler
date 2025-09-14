import json

from ..json_types import CourseInstanceJSON
from ..models import CourseInstance


class JSONWriter:
    """
    Writer class for JSON output with consistent interface.

    This class provides a context manager interface for writing course schedules
    to JSON format, either to a file or stdout.
    """

    def __init__(self, filename: str | None = None):
        """
        Initialize the JSONWriter.

        **Args:**
        - filename: The name of the file to write the JSON to
        """
        self.filename = filename
        self.schedules: list[list[CourseInstanceJSON]] = []

    def __enter__(self):
        """
        Enter the context manager.

        **Returns:**
        The JSONWriter instance
        """
        return self

    def add_schedule(self, schedule: list[CourseInstance]) -> None:
        """
        Add a schedule to be written to the JSON file.

        **Args:**
        - schedule: The schedule to be written
        """
        schedule_data = []
        for course_instance in schedule:
            schedule_data.append(course_instance.model_dump(by_alias=True, exclude_none=True))
        if self.filename:
            self.schedules.append(schedule_data)
        else:
            print(json.dumps(schedule_data, separators=(",", ":")))

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        """
        Exit the context manager and write all accumulated schedules as one JSON array.

        **Args:**
        - exc_type: Exception type if an exception occurred
        - exc_value: Exception value if an exception occurred
        - traceback: Traceback if an exception occurred
        """
        if self.filename:
            content = json.dumps(self.schedules, separators=(",", ":"))
            with open(self.filename, "w", encoding="utf-8") as f:
                f.write(content)
