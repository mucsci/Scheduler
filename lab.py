# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

class Lab:

    _all = dict()
    _lab_id = 200

    def min_id():
        """
        Returns the minimum number for the lab IDs (always 200)
        """
        return 200

    def max_id():
        """
        Returns the maximum number for the lab IDs
        """
        return Lab._lab_id - 1

    def get(id):
        """
        Given an ID of a lab, return the instance
        """
        return Lab._all[id]

    def __init__(self, name: str):
        # update id to be a unique identifier
        self.id = Lab._lab_id
        Lab._lab_id += 1
        self.name = name
        Lab._all[self.id] = self

    def __repr__(self):
        """
        Pretty Print representation of a course is its subject, number, and section
        """
        return f'{self.name}'