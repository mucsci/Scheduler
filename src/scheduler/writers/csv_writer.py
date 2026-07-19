from ..models import CourseInstance


class CSVWriter:
    """
    Writer class for CSV output with consistent interface.

    This class provides a context manager interface for writing course schedules
    to CSV format, either to a file or stdout.

    **Usage:**
    ```python
    with CSVWriter("out.csv") as w:
        w.add_schedule(model)
    ```
    """

    def __init__(self, filename: str | None = None):
        """
        Initialize the CSVWriter.

        **Usage:**
        ```python
        CSVWriter("out.csv")
        ```

        **Args:**
        - filename: The name of the file to write CSV data to, or None for stdout
        """
        self.filename = filename
        self.schedules: list[str] = []

    def __enter__(self):
        """
        Enter the context manager.

        **Usage:**
        ```python
        with CSVWriter(None) as w:
        ```

        **Returns:**
        The CSVWriter instance
        """
        return self

    def add_schedule(self, schedule: list[CourseInstance]) -> None:
        """
        Serialize one complete schedule in the writer's CSV representation.

        Args:
            schedule: Ordered course assignments comprising one generated schedule.

        Returns:
            None.

        Raises:
            None directly; exceptions raised by course CSV serialization or stdout
            writing are allowed to propagate.

        Behavior:
            Course rows are joined with newlines. File-backed writers buffer the
            complete serialized schedule until context-manager exit, preserving a
            blank line between schedules. Stdout-backed writers print immediately.
        """
        schedule_data = "\n".join(course_instance.as_csv() for course_instance in schedule)
        if self.filename:
            self.schedules.append(schedule_data)
        else:
            print(schedule_data)

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        """
        Exit the context manager and write all accumulated schedules.

        **Usage:**
        ```python
        # Flushes accumulated rows to disk
        ```

        **Args:**
        - exc_type: Exception type if an exception occurred
        - exc_value: Exception value if an exception occurred
        - traceback: Traceback if an exception occurred
        """
        if self.filename:
            content = "\n\n".join(self.schedules)
            with open(self.filename, "w", encoding="utf-8") as f:
                f.write(content)
