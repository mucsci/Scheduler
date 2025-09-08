from enum import IntEnum, auto


class Day(IntEnum):
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
