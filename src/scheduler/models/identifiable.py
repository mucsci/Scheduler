from typing import ClassVar

from pydantic import BaseModel, Field


class Identifiable(BaseModel):
    _default_id: ClassVar[int]
    _id: ClassVar[int]
    _all: ClassVar[dict]

    id: int | None = Field(default=None)

    def __init_subclass__(cls, /, **kwargs):
        super().__init_subclass__(**kwargs)
        cls._default_id = 1
        cls._id = cls._default_id
        cls._all = dict()

    def __init__(self, **kwargs) -> None:
        super().__init__(**kwargs)
        if not hasattr(self, "id") or self.id is None:
            self.id = self.__class__._id
            self.__class__._all[self.id] = self
            self.__class__._id += 1

    @classmethod
    def min_id(cls):
        """
        Returns the minimum number for the lab IDs (always 200)
        """
        return cls._default_id

    @classmethod
    def max_id(cls):
        """
        Returns the maximum number for the lab IDs
        """
        return cls._id - 1

    @classmethod
    def get(cls, id):
        """
        Given an ID of a room, return the instance
        """
        if id:
            return cls._all[id]
        else:
            return None

    def __repr__(self):
        return str(self.id)
