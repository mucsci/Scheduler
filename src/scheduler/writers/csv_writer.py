from ..models import CourseInstance


class CSVWriter:
    """Writer class for CSV output with consistent interface."""

    def __init__(self, filename: str | None = None):
        self.filename = filename
        self.schedules: list[str] = []

    def __enter__(self):
        return self

    def add_schedule(self, schedule: list[CourseInstance]) -> None:
        """Add a schedule to be written."""
        schedule_data = "\n".join(course_instance.as_csv() for course_instance in schedule)
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
