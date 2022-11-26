from typing import DefaultDict, Dict, List
from collections import defaultdict
import json
import itertools
import z3
import sys
from json import JSONEncoder
import json_fix

from course import Course
from lab import Lab
from room import Room
from time_slot import Day, TimeInstance, TimePoint, TimeSlot
from config import time_slots




def load_from_file(filename):
    with open(filename) as f:
        return json.load(f)


def load_from_raw(data):
    return json.loads(data)


class MyEncoder(JSONEncoder):
    def default(self, o):
        return o.__dict__


class Scheduler:

    def __init__(self, json_data):
        self.rooms = {r: Room(r) for r in json_data['rooms']}
        self.labs = {l: Lab(l) for l in json_data['labs']}
        self.courses = [Course(*(c[v] for v in ["credits", "subj", "num", "lab",
                               "room", "faculty", "conflicts"])) for c in json_data['courses']]

        def get_info(person):
            days = [Day.MON, Day.TUE, Day.WED, Day.THU, Day.FRI]

            def walk():
                for d, times in zip(days, person['times']):
                    for start, end in times:
                        start_time = TimePoint.make_from(*start)
                        end_time = TimePoint.make_from(*end)
                        duration = end_time - start_time
                        yield TimeInstance(d, start_time, duration)
            return list(walk())
        self.faculty = {x: get_info(
            json_data['faculty'][x]) for x in json_data['faculty']}
        self.ranges: DefaultDict[int, List[int]] = defaultdict(lambda: [0, 0])

        def generate_slots():
            low = TimeSlot.min_id()
            for credits in [3, 4]:
                yield from time_slots(credits)
                high = TimeSlot.max_id()
                self.ranges[credits] = [low, high]
                low = TimeSlot.max_id() + 1
        self.slots = list(generate_slots())
        self.constraints = self._build()

    @staticmethod
    def _simplify(x):
        return z3.simplify(x, cache_all=True, elim_and=True, rewrite_patterns=True)

    def _z3ify_time_constraint(self, name: str, fn):
        z3fn = z3.Function(name, z3.IntSort(), z3.IntSort(), z3.BoolSort())

        def generate():
            for i, j in itertools.combinations(self.slots, 2):
                ii, jj = z3.IntVal(i.id), z3.IntVal(j.id)
                if fn(i, j):
                    yield z3fn(ii, jj)
                    yield z3fn(jj, ii)
                else:
                    yield z3.Not(z3fn(ii, jj))
                    yield z3.Not(z3fn(jj, ii))
            for i in self.slots:
                ii = z3.IntVal(i.id)
                yield z3fn(ii, ii)
        return z3fn, list(Scheduler._simplify(x) for x in generate())

    def _z3ify_time_slot_fn(self, name: str, fn):
        z3fn = z3.Function(name, z3.IntSort(), z3.BoolSort())

        def generate():
            for i in self.slots:
                ii = z3.IntVal(i.id)
                if fn(i):
                    yield z3fn(ii)
                else:
                    yield z3.Not(z3fn(ii))
        return z3fn, list(Scheduler._simplify(x) for x in generate())

    def _build(self):

        # abstract function constraints
        overlaps, overlaps_C = self._z3ify_time_constraint(
            'overlaps', TimeSlot.overlaps)
        labs_on_same_day, labs_on_same_day_C = self._z3ify_time_constraint(
            'labs_on_same_day', TimeSlot.labs_on_same_day)
        lab_overlaps, lab_overlaps_C = self._z3ify_time_constraint(
            'lab_overlaps', TimeSlot.lab_overlaps)
        next_to, next_to_C = self._z3ify_time_constraint(
            'next_to', TimeSlot.next_to)
        has_lab, has_lab_C = self._z3ify_time_slot_fn(
            'has_lab', TimeSlot.has_lab)
        not_next_to, not_next_to_C = self._z3ify_time_constraint(
            'not_next_to', TimeSlot.not_next_to)

        fn_constraints = overlaps_C + lab_overlaps_C + next_to_C + \
            labs_on_same_day_C + has_lab_C + not_next_to_C

        # basic identity constraints and bounds
        def basic_constraints():
            for c in self.courses:
                yield z3.And(self.ranges[c.credits][0] <= c.time(), c.time() <= self.ranges[c.credits][1])

        def faculty_constraints():
            def assign_to_faculty():
                for c in self.courses:
                    ranges = self.faculty[c.faculty]
                    # check the faculty time constraint
                    yield z3.And(*(c.time() != slot.id for slot in self.slots if not slot.in_time_ranges(ranges)))

            # - check for unique, non-overlapping timeslots for each faculty
            def non_overlapping():
                for name in self.faculty.keys():
                    assigned = list(c.time()
                                    for c in self.courses if c.faculty == name)
                    yield z3.Not(z3.Or(list(overlaps(i, j) for i, j in itertools.combinations(assigned, 2))))

            # - ensure sections of the same class are adjacent
            # - and that sections of different classes are NOT adjacent
            def same_adjacent():
                for name in self.faculty.keys():
                    courses = (c for c in self.courses if c.faculty == name)
                    for i, j in itertools.combinations(courses, 2):
                        if i.subject == j.subject and i.num == j.num:
                            yield next_to(i.time(), j.time())
                            yield i.room() == j.room()
                            yield z3.Implies(z3.And(has_lab(i.time()), has_lab(j.time())), i.lab() == j.lab())
                        else:
                            yield not_next_to(i.time(), j.time())

            # add constraint that all three two-hour period must be on different days
            def no_crazy_days():
                for name in self.faculty.keys():
                    courses = [
                        c for c in self.courses if c.faculty == name and c.labs]
                    if len(courses) > 2:
                        yield z3.Not(z3.And(has_lab(courses[0].time()), *(z3.And(has_lab(r.time()), labs_on_same_day(courses[0].time(), r.time())) for r in courses[1:])))

            yield from assign_to_faculty()
            yield from non_overlapping()
            yield from same_adjacent()
            yield from no_crazy_days()

        def conflict_constraints():

            # - check the other courses time slot constraint(s)
            for c in self.courses:
                for conflict_num in c.conflicts:
                    for d in self.courses:
                        if c != d and d.num == conflict_num:
                            yield z3.Not(overlaps(c.time(), d.time()))

        # assign to a lab (or none)
        # - ensure no timeslot + lab conflicts exist
        def lab_assign_constraints():
            # we must assign to a lab when we have options
            yield from (z3.simplify(z3.Or(
                list(c.lab() == lab.id for name,
                     lab in self.labs.items() if name in c.labs)
            )) for c in self.courses if c.labs)

            # any two courses with a lab must not have a resource overlap
            with_labs = list(filter(lambda x: len(x.labs) >= 1, self.courses))
            yield from (z3.Implies(i.lab() == j.lab(), z3.Not(lab_overlaps(i.time(), j.time()))) for i, j in itertools.combinations(with_labs, 2))

        # assign to a classroom
        # - ensure no timeslot + classroom conflicts exist
        def room_assign_constraints():
            # we must assign to a lab when we have options
            yield from (z3.simplify(z3.Or(
                list(c.room() == room.id for name,
                     room in self.rooms.items() if name in c.rooms)
            )) for c in self.courses if c.rooms)

            # any two courses must not have a resource overlap
            yield from (z3.Implies(i.room() == j.room(), z3.Not(overlaps(i.time(), j.time()))) for i, j in itertools.combinations(self.courses, 2))

        C = list(Scheduler._simplify(x) for x in itertools.chain(basic_constraints(), faculty_constraints(
        ), conflict_constraints(), lab_assign_constraints(), room_assign_constraints()))
        return fn_constraints + C

    def get_models(self, limit=10):
        s = z3.Solver()
        s.add(self.constraints)
        i = 0
        while i < limit and s.check() == z3.sat:
            m = s.model()
            yield i, m, s.statistics()
            i += 1
            block = []
            for d in m:
                # d is a declaration     # ignore room differences in schedules
                if d.arity() <= 0 and not d.name().endswith('room') and not d.name().endswith('lab'):
                    # create a constant from declaration
                    c = d()
                    if not z3.is_array(c) and c.sort().kind() != z3.Z3_UNINTERPRETED_SORT:
                        block.append(c == m[d])
            s.add(z3.simplify(z3.Not(z3.And(*block))))


def concretize(map: Dict):
    def iter():
        for k, v in map.items():
            if k == 'room':
                yield (k, Room.get(map["room"]).name)
            elif k == 'lab':
                if v:
                    yield (k, {'room': Lab.get(map["lab"]).name, 'time': TimeSlot.get(map["time"]).lab_time()})
            elif k == 'time':
                yield (k, list(t for t in TimeSlot.get(map["time"])._times))
            else:
                yield (k, v)
    return dict(iter())


def generate_models(data, limit):
    s = Scheduler(load_from_file(data))

    def all():
        for _, m, _ in s.get_models(limit):
            yield list(concretize(c.evaluate(m)) for c in s.courses)
    return json.dumps(list(all()), cls=MyEncoder, separators=(',', ':'))


if __name__ == '__main__':

    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <json_config> [limit=10] [json]")
        exit(1)

    config_file = sys.argv[1]

    limit = 10 if len(sys.argv) == 2 else int(sys.argv[2])

    dump_json = len(sys.argv) == 4 and sys.argv[3] == "json"

    if dump_json:
        print(generate_models(config_file, limit))
        exit(0)

    print(f"> Using limit={limit}")
    sched = Scheduler(load_from_file(config_file))
    print(f"> Created all constraints")

    for i, m, s in sched.get_models(limit):
        print(f'Model {i}:')
        print('  ', end='')
        for j in s.keys():
            print(f'{j}:{s.get_key_value(j)}  ', end='')
        print('\n')

        #assigned = list(concretize(c.evaluate(m)) for c in sched.courses)
        # print(assigned)

        assigned = list(c.csv(m) for c in sched.courses)
        print('\n'.join(assigned))

        try:
            print()
            input('press <enter> for the next schedule (or Ctrl+D) to quit')
            print()
            print("> Getting next model...")
        except:
            exit(0)
