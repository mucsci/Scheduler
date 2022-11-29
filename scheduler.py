import json
import itertools
import sys
from typing import Any, Callable, Dict, Iterable, List, Tuple

import json_fix
import z3

from course import Course
from lab import Lab
from room import Room
from time_slot import Day, Duration, TimeInstance, TimePoint, TimeSlot
from config import time_slots


def load_from_file(filename):
    with open(filename) as f:
        return json.load(f)


class Scheduler:

    def __init__(self, json_data : Dict[str, Any]):
        
        LOOKUP: List[str] = ["credits", "subj", "num", "lab", "room", "faculty", "conflicts"]

        self.rooms: Dict[str, Room] = dict(
            (r, Room(r)) for r in json_data['rooms']
        )

        self.labs: Dict[str, Lab] = dict(
            (l, Lab(l)) for l in json_data['labs']
        )

        courses_sorted_by_faculty = list(sorted(json_data['courses'], key=lambda x:x["faculty"]))
        self.courses: List[Course] = [Course(*(c[v] for v in LOOKUP)) for c in courses_sorted_by_faculty]

        Time = Tuple[int, int]
        Range = Tuple[Time, Time]
        DayRanges = List[Range]

        def get_info(person: Dict[str, List[DayRanges]]) -> List[TimeInstance]:
            days: List[Day] = [Day.MON, Day.TUE, Day.WED, Day.THU, Day.FRI]
            result : List[TimeInstance] = list()
            for day, times in zip(days, person['times']):
                for start, end in times:
                    start_time: TimePoint = TimePoint.make_from(*start)
                    end_time: TimePoint = TimePoint.make_from(*end)
                    duration: Duration = end_time - start_time
                    result.append(TimeInstance(day, start_time, duration))
            return result

        self.faculty: dict[str, List[TimeInstance]] = {
            faculty: get_info(times) for faculty, times in json_data['faculty'].items()
        }

        def generate_slots() -> Tuple[Dict[int, Tuple[int, int]], List[TimeSlot]]:
            ranges: Dict[int, Tuple[int, int]] = dict()
            slots: List[TimeSlot] = list()
            low = TimeSlot.min_id()
            for credits in [3, 4]:
                for s in time_slots(credits):
                    slots.append(s)
                high = TimeSlot.max_id()
                ranges[credits] = (low, high)
                low = TimeSlot.max_id() + 1
            return ranges, slots
        
        ranges, slots = generate_slots()

        self.ranges: Dict[int, Tuple[int, int]] = ranges
        self.slots: List[TimeSlot] = slots
        
        hard, soft = self._build()

        self.constraints = hard
        self.soft_constraints = soft

    @staticmethod
    def _simplify(x):
        return z3.simplify(x, cache_all=True, rewrite_patterns=True)

    def _z3ify_time_constraint(self, name: str, fn: Callable[[TimeSlot,TimeSlot], bool]) -> Tuple[z3.Function, List[z3.ArithRef]]:
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
        return z3fn, [Scheduler._simplify(x) for x in generate()]

    def _z3ify_time_slot_fn(self, name: str, fn: Callable[[TimeSlot], bool]) -> Tuple[z3.Function, List[z3.ArithRef]]:
        z3fn = z3.Function(name, z3.IntSort(), z3.BoolSort())

        def generate():
            for i in self.slots:
                ii = z3.IntVal(i.id)
                if fn(i):
                    yield z3fn(ii)
                else:
                    yield z3.Not(z3fn(ii))
        return z3fn, [Scheduler._simplify(x) for x in generate()]

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
        next_to_tues_wed, next_to_tues_wed_C = self._z3ify_time_constraint(
            'next_to_tues_wed', TimeSlot.next_to_tues_wed)

        fn_constraints = overlaps_C + lab_overlaps_C + next_to_C + \
            labs_on_same_day_C + has_lab_C + not_next_to_C

        soft_fn_constraints = next_to_tues_wed_C

        def hard_constraints():

            for c in self.courses:

                start, stop = self.ranges[c.credits]
                yield z3.And([
                    # basic timeslot constraint
                    z3.And([start <= c.time(), c.time() <= stop]),
                    # we must assign to a lab when we have options
                    z3.Implies(len(c.labs) > 0, z3.Or([c.lab() == lab.id for name, lab in self.labs.items() if name in c.labs])),
                    # we must assign to a lab when we have options
                    z3.Implies(len(c.rooms) > 0, z3.Or([c.room() == room.id for name, room in self.rooms.items() if name in c.rooms])),
                    # check the other courses time slot constraint(s)
                    z3.And([z3.Not(overlaps(c.time(), d.time())) for conflict_num in c.conflicts for d in self.courses if d.num == conflict_num]),
                    # check the faculty time constraint
                    z3.Or([c.time() == slot.id for slot in self.slots if slot.in_time_ranges(self.faculty[c.faculty()])])
                ])

            for _, courses in itertools.groupby(self.courses, Course.faculty):

                for i, j in itertools.combinations(courses, 2):
                    yield z3.And([
                        # check for unique, non-overlapping timeslots for each faculty
                        z3.Not(overlaps(i.time(), j.time())),
                        # ensure sections of the same class are adjacent and that sections of different classes are NOT adjacent
                        z3.simplify(z3.If(
                            (i.subject == j.subject and i.num == j.num),
                            z3.And([
                                next_to(i.time(), j.time()), i.room() == j.room(),
                                z3.Implies(z3.And(has_lab(i.time()), has_lab(j.time())), i.lab() == j.lab())
                            ]),
                            not_next_to(i.time(), j.time())
                        ))
                    ])

                for i, j, k in itertools.combinations((c for c in courses if c.labs), 3):
                    # add constraint that all three two-hour period must be on different days
                    yield z3.Or(
                        z3.Not(labs_on_same_day(i.time(), j.time())),
                        z3.Not(labs_on_same_day(j.time(), k.time())),
                        z3.Not(labs_on_same_day(i.time(), k.time()))
                    )

            for i, j in itertools.combinations(self.courses, 2):
                yield z3.And([
                    # any two courses must not have a resource overlap
                    z3.Implies(i.room() == j.room(), z3.Not(overlaps(i.time(), j.time()))),
                    # any two courses with a lab must not have a resource overlap
                    z3.simplify(z3.Implies(
                        z3.And(
                            len(i.labs) > 0 and len(j.labs) > 0,
                            i.lab() == j.lab()
                        ),
                        z3.Not(lab_overlaps(i.time(), j.time()))
                    ))
                ])

        def soft_constraints():
            for _, courses in itertools.groupby(self.courses, Course.faculty):
                for _, v in itertools.groupby(courses, Course.uid):
                    yield z3.And([z3.Not(next_to_tues_wed(i.time(), j.time())) for i, j in itertools.combinations(v, 2)])

        C = [Scheduler._simplify(x) for x in hard_constraints()]
        S = [Scheduler._simplify(x) for x in soft_constraints()]

        hard = fn_constraints + C
        soft = soft_fn_constraints + S

        return hard, soft

    def get_models(self, limit=10):

        def update(i: int, s: z3.Solver) -> Iterable[Tuple[int, z3.ModelRef, z3.Statistics]]:
            m : z3.ModelRef = s.model()
            stat : z3.Statistics = s.statistics()

            yield i, m, stat

            def constraints():
                for _, courses in itertools.groupby(self.courses, Course.faculty):
                    for _, v in itertools.groupby(courses, Course.uid):
                        ordered = list(v)
                        yield z3.And(*(
                            z3.Or(list(act != exp.time()
                                        for act, exp in zip((m[c.time()] for c in ordered), r)
                                        ))
                            for r in itertools.permutations(ordered)
                        ))
            s.add(Scheduler._simplify(z3.Or(*constraints())))

        s = z3.Solver()
        s.add(self.constraints)
        s.push()
        s.add(self.soft_constraints)
        if s.check() != z3.sat:
            print("WARNING: Soft constraints are non-sat", file=sys.stderr)
            s.pop()
        for i in range(limit):
            if s.check() != z3.sat:
                if i == 0:
                    print("WARNING: no possible schedule", file=sys.stderr)
                else:
                    print(f"Generated {i} schedules", file=sys.stderr)
                break
            yield from update(i, s)


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
    return json.dumps(list(all()), separators=(',', ':'))


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

        print('\n'.join(c.csv(m) for c in sched.courses))

        try:
            print()
            input('press <enter> for the next schedule (or Ctrl+D) to quit')
            print()
            print("> Getting next model...")
        except:
            exit(0)
