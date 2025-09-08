import json

from ..json_types import CourseInstanceJSON
from ..models import CourseInstance


class JSONWriter:
    """Writer class for JSON output with consistent interface."""

    def __init__(self, filename: str | None = None):
        self.filename = filename
        self.schedules: list[list[CourseInstanceJSON]] = []

    def __enter__(self):
        return self

    def add_schedule(self, schedule: list[CourseInstance]) -> None:
        """Add a schedule to be written."""
        schedule_data = []
        for course_instance in schedule:
            schedule_data.append(course_instance.model_dump(by_alias=True, exclude_none=True))
        if self.filename:
            self.schedules.append(schedule_data)
        else:
            print(json.dumps(schedule_data, separators=(",", ":")))

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        """Write all accumulated schedules as one JSON array."""
        if self.filename:
            content = json.dumps(self.schedules, separators=(",", ":"))
            with open(self.filename, "w", encoding="utf-8") as f:
                f.write(content)
