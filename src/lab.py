from identifiable import Identifiable


class Lab(Identifiable):

    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return self.name
