from enum import IntEnum, auto


class Day(IntEnum):
    """
    Enumeration representing days of the week for scheduling.

    This enum provides integer values for each weekday, starting from 1 (Monday)
    and incrementing through Friday. Used throughout the scheduler for day-based
    time slot management.
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
        """
        return self.name
