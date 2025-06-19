import json
import z3

from ..models import Course


class JSONWriter:
    """Writer class for JSON output with consistent interface."""

    def __init__(self, filename: str = None):
        self.filename = filename
        self.schedules = []

    def __enter__(self):
        return self

    def add_schedule(self, courses: list[Course], model: z3.ModelRef) -> None:
        """Add a schedule to be written."""

        schedule_data = [c.instance(model).as_json() for c in courses]
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
