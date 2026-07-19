import json

from ..json_types import CourseInstanceJSON
from ..models import CourseInstance


class JSONWriter:
    """
    Writer class for JSON output with consistent interface.

    This class provides a context manager interface for writing course schedules
    to JSON format, either to a file or stdout.

    **Usage:**
    ```python
    with JSONWriter("out.json") as w:
        w.add_schedule(model)
    ```
    """

    def __init__(self, filename: str | None = None):
        """
        Initialize the JSONWriter.

        **Usage:**
        ```python
        JSONWriter("out.json")
        ```

        **Args:**
        - filename: The name of the file to write the JSON to
        """
        self.filename = filename
        self.schedules: list[list[CourseInstanceJSON]] = []

    def __enter__(self):
        """
        Enter the context manager.

        **Usage:**
        ```python
        with JSONWriter(None) as w:
        ```

        **Returns:**
        The JSONWriter instance
        """
        return self

    def add_schedule(self, schedule: list[CourseInstance]) -> None:
        """
        Serialize one complete schedule in the writer's JSON representation.

        Args:
            schedule: Ordered course assignments comprising one generated schedule.

        Returns:
            None.

        Raises:
            TypeError: If a value emitted by a course model is not JSON serializable.
            OSError: If immediate stdout output fails.

        Behavior:
            Each course is dumped using aliases and with null fields omitted.
            File-backed writers buffer the resulting schedule so context-manager
            exit can emit one compact outer array. Stdout-backed writers print the
            individual schedule immediately as compact JSON.
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

        **Usage:**
        ```python
        # Writes JSON array of schedules
        ```

        **Args:**
        - exc_type: Exception type if an exception occurred
        - exc_value: Exception value if an exception occurred
        - traceback: Traceback if an exception occurred
        """
        if self.filename:
            content = json.dumps(self.schedules, separators=(",", ":"))
            with open(self.filename, "w", encoding="utf-8") as f:
                f.write(content)
