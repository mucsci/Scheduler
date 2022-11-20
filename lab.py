# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from identifiable import Identifiable
import json_fix


class Lab(Identifiable, default_id=200):

    def __init__(self, name: str):
        self.name = name

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return f'"{self.name}"'

    def __json__(self):
        return self.name
