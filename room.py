# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

class Room:

    _all = dict()
    room_id = 100

    def min_id():
        """
        Returns the maximum number for the room IDs (always 100)
        """
        return 100

    def max_id():
        """
        Returns the maximum number for the room IDs
        """
        return Room.room_id - 1

    def get(id):
        """
        Given an ID of a room, return the instance
        """
        return Room._all[id]

    def __init__(self, name: str):
        # update id to be a unique identifier
        self.id = Room.room_id
        Room.room_id += 1
        self.name = name
        Room._all[self.id] = self

    def __repr__(self):
        """
        Pretty Print representation of a course is its subject, number, and section
        """
        return f'{self.name}'