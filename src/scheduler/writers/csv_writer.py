from ..models import CourseInstance


class CSVWriter:
    """
    Writer class for CSV output with consistent interface.

    This class provides a context manager interface for writing course schedules
    to CSV format, either to a file or stdout.
    """

    def __init__(self, filename: str | None = None):
        """
        Initialize the CSVWriter.

        **Args:**
        - filename: The name of the file to write CSV data to, or None for stdout
        """
        self.filename = filename
        self.schedules: list[str] = []

    def __enter__(self):
        """
        Enter the context manager.

        **Returns:**
        The CSVWriter instance
        """
        return self

    def add_schedule(self, schedule: list[CourseInstance]) -> None:
        """
        Add a schedule to be written.

        **Args:**
        - schedule: List of CourseInstance objects representing a complete schedule
        """
        schedule_data = "\n".join(course_instance.as_csv() for course_instance in schedule)
        if self.filename:
            self.schedules.append(schedule_data)
        else:
            print(schedule_data)

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        """
        Exit the context manager and write all accumulated schedules.

        **Args:**
        - exc_type: Exception type if an exception occurred
        - exc_value: Exception value if an exception occurred
        - traceback: Traceback if an exception occurred
        """
        if self.filename:
            content = "\n\n".join(self.schedules)
            with open(self.filename, "w", encoding="utf-8") as f:
                f.write(content)
