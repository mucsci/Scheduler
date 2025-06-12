from identifiable import Identifiable


class Faculty(Identifiable, default_id=300):

    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return self.name

    def __json__(self):
        return self.name
