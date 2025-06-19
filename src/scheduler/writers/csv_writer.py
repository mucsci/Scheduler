import json
import z3

from ..models import Course


class CSVWriter:
    """Writer class for CSV output with consistent interface."""

    def __init__(self, filename: str = None):
        self.filename = filename
        self.schedules = []

    def __enter__(self):
        return self

    def add_schedule(self, courses: list[Course], model: z3.ModelRef) -> None:
        """Add a schedule to be written."""
        schedule_data = "\n".join(c.instance(model).csv() for c in courses)
        if self.filename:
            self.schedules.append(schedule_data)
        else:
            print(schedule_data)

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        """Write all accumulated schedules."""
        if self.filename:
            content = "\n\n".join(self.schedules)
            with open(self.filename, "w", encoding="utf-8") as f:
                f.write(content)
