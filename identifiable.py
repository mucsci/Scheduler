from abc import ABC


class Identifiable(ABC):

    def __init_subclass__(cls, default_id, **kwargs):
        super().__init_subclass__(**kwargs)
        cls._default_id = default_id
        cls._id = cls._default_id
        cls._all = dict()

    def __new__(cls, *args, **kwargs):
        instance = super(Identifiable, cls).__new__(cls)
        instance.id = cls._id
        cls._all[cls._id] = instance
        cls._id += 1
        return instance

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
