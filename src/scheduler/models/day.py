from enum import IntEnum, auto


class Day(IntEnum):
    """
    Enumeration representing days of the week for scheduling.

    This enum provides integer values for each weekday, starting from 1 (Monday)
    and incrementing through Friday. Used throughout the scheduler for day-based
    time slot management.

    **Usage:**
    ```python
    Day.MON
    Day.MON.name
    ```
    """

    MON = auto()
    TUE = auto()
    WED = auto()
    THU = auto()
    FRI = auto()

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        """
        Pretty Print representation of a day

        **Usage:**
        ```python
        repr(Day.MON)
        ```
        """
        return self.name
