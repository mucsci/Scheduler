from enum import IntEnum, auto


class Day(IntEnum):
    MON = auto()
    TUE = auto()
    WED = auto()
    THU = auto()
    FRI = auto()

    def __str__(self) -> str:
        return next(val.name for val in Day if self.value == val)

    def __repr__(self) -> str:
        """
        Pretty Print representation of a day
        """
        return next(val.name for val in Day if self.value == val)

    def __json__(self):
        return self.value
