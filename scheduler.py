# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from typing import Dict
from course import Course
from lab import Lab
from room import Room
from time_slot import Day, TimeSlot, hhmm_to_timeid
from config import time_slots

import json
import functools
import itertools
import operator
import z3
import sys

def load(filename):
    with open(filename) as f:
        data = json.load(f)
        rooms = {r : Room(r) for r in data['rooms']}
        labs = {l : Lab(l) for l in data['labs']}
        courses = [Course(*(c[v] for v in ["credits","subj","num","lab","room","faculty","conflicts"])) for c in data['courses']]
        
        def get_info(person):
            days = [Day.MON, Day.TUE, Day.WED, Day.THU, Day.FRI]
            masked = functools.reduce(operator.or_, (d for d, m in zip(days, person['days']) if m))
            low, high = person['times']
            return masked, hhmm_to_timeid(*low), hhmm_to_timeid(*high)
        faculty = { x : get_info(data['faculty'][x]) for x in data['faculty']}
        return (rooms, labs, courses, faculty)

def simplify(x):
    return z3.simplify(x, cache_all=True, elim_and=True)

def z3ify_time_constraint(name: str, fn):
    z3fn = z3.Function(name, z3.IntSort(), z3.IntSort(), z3.BoolSort())
    def generate():
        for i, j in itertools.combinations(ALL_SLOTS, 2):
            ii, jj = z3.IntVal(i.id), z3.IntVal(j.id)
            if fn(i, j):
                yield z3fn(ii, jj)
                yield z3fn(jj, ii)
            else:
                yield z3.Not(z3fn(ii, jj))
                yield z3.Not(z3fn(jj, ii))
        for i in ALL_SLOTS:
            ii = z3.IntVal(i.id)
            yield z3fn(ii, ii)
    return z3fn, list(simplify(x) for x in generate())

def z3ify_time_slot_fn(name: str, fn):
    z3fn = z3.Function(name, z3.IntSort(), z3.BoolSort())
    def generate():
        for i in ALL_SLOTS:
            ii = z3.IntVal(i.id)
            if fn(i):
                yield z3fn(ii)
            else:
                yield z3.Not(z3fn(ii))
    return z3fn, list(simplify(x) for x in generate())

def init_data(filename: str):
    global ROOMS
    global LABS
    global COURSES
    global FACULTY
    global ALL_SLOTS
    global HIGH3
    global HIGH4
    global LOW3
    global LOW4

    ROOMS, LABS, COURSES, FACULTY = load(filename)
    LOW3 = TimeSlot.min_id()
    three_credit = list(time_slots(3))
    HIGH3 = TimeSlot.max_id()
    LOW4 = HIGH3 + 1
    four_credit = list(time_slots(4))
    HIGH4 = TimeSlot.max_id()
    ALL_SLOTS = three_credit + four_credit

def make_constraints():

    # abstract function constraints
    overlaps, o_constraints = z3ify_time_constraint('overlaps', TimeSlot.overlaps)
    labs_on_same_day, o_labs_on_same_day = z3ify_time_constraint('labs_on_same_day', TimeSlot.labs_on_same_day)
    lab_overlaps, i_constraints = z3ify_time_constraint('lab_overlaps', TimeSlot.lab_overlaps)
    next_to, n_constraints = z3ify_time_constraint('next_to', TimeSlot.next_to)
    has_lab, l_constraints = z3ify_time_slot_fn('has_lab', TimeSlot.has_lab)
    
    fn_constraints = o_constraints + i_constraints + n_constraints + o_labs_on_same_day + l_constraints

    # basic identity constraints and bounds
    def basic_constraints():
        for c in COURSES:
            # assign the correct time slot for the number of credits
            if c.credits == 3:
                yield z3.And(LOW3 <= c.time(), c.time() <= HIGH3)
            elif c.credits == 4:
                yield z3.And(LOW4 <= c.time(), c.time() <= HIGH4)
            
    def faculty_constraints():
        def assign_to_faculty():
            for c in COURSES:
                mask, start, stop = FACULTY[c.faculty]
                # check the faculty time constraint
                yield z3.And(*(c.time() != slot.id for slot in ALL_SLOTS if not slot.in_time_range(mask, start, stop)))
        
        # - check for unique, non-overlapping timeslots for each faculty
        def non_overlapping():
            for name in FACULTY.keys():
                assigned = list(c.time() for c in COURSES if c.faculty == name)
                yield z3.And(list(z3.Not(overlaps(i,j)) for i,j in itertools.combinations(assigned, 2)))
        
        # - ensure sections of the same class are adjacent
        def same_adjacent():
            for name in FACULTY.keys():
                courses = [c for c in COURSES if c.faculty == name]
                for i, j in itertools.combinations(courses, 2):
                    if i.num == j.num:
                        yield next_to(i.time(), j.time())
                        yield i.room() == j.room()
                        yield z3.Implies(z3.And(has_lab(i.time()), has_lab(j.time())), i.lab() == j.lab())
        
        # add constraint that all three two-hour period must be on different days
        def no_crazy_days():
            for name in FACULTY.keys():
                if FACULTY[name][0] ^ (Day.TUE | Day.THU) or FACULTY[name][0] ^ (Day.MON | Day.WED):
                    courses = [c for c in COURSES if c.faculty == name]
                    if len(courses) >= 3:
                        yield z3.Not(z3.And(
                            list(z3.Implies(z3.And(has_lab(c.time()), has_lab(d.time())), labs_on_same_day(c.time(), d.time())) for c,d in itertools.combinations(courses, 2))
                        ))

        yield from assign_to_faculty()
        yield from non_overlapping()
        yield from same_adjacent()
        # NOTE: may need to comment this out
        yield from no_crazy_days()        

    def conflict_constraints():

        # - check the other courses time slot constraint(s)
        for c in COURSES:
            for conflict_num in c.conflicts:
                for other in filter(lambda x: x.num == conflict_num, (c for c in COURSES)):
                    yield z3.Not(overlaps(c.time(), other.time()))

    # assign to a lab (or none)
    # - ensure no timeslot + lab conflicts exist
    def lab_assign_constraints():

        # make all constraints for room assignment for lab
        def gen(c):
            for name,lab in LABS.items():
                if name in c.labs:
                    yield c.lab() == lab.id
        
        # we must assign to a lab when we have options
        yield from (z3.simplify(z3.Or(list(gen(c)))) for c in COURSES if c.labs)

        # any two courses with a lab must not have a resource overlap
        with_labs = list(filter(lambda x: len(x.labs) >= 1, COURSES))
        for i, j in itertools.combinations(with_labs, 2):
            yield z3.Implies(i.lab() == j.lab(), z3.Not(lab_overlaps(i.time(), j.time())))

    # assign to a classroom
    # - ensure no timeslot + classroom conflicts exist
    def room_assign_constraints():
        
        # make all constraints for room assignment for lab
        def gen(c):
            yield from (c.room() == room.id for name,room in ROOMS.items() if name in c.rooms)
        
        # we must assign to a lab when we have options
        yield from (z3.simplify(z3.Or(list(gen(c)))) for c in COURSES if c.rooms)
        
        # any two courses with a lab must not have a resource overlap
        yield from (z3.Implies(overlaps(i.time(), j.time()), i.room() != j.room()) for i, j in itertools.combinations(COURSES, 2))

    C = list(simplify(x) for x in itertools.chain(basic_constraints(),faculty_constraints(),conflict_constraints(),lab_assign_constraints(),room_assign_constraints()))
    return fn_constraints + C

def get_models(F, M=10):
    s = z3.Solver()
    s.add(F)
    i = 0
    while i < M and s.check() == z3.sat:
        m = s.model()
        yield i, m, s.statistics()
        i += 1
        block = []
        for d in m:
            # d is a declaration     # ignore room differences in schedules
            if d.arity() <= 0 and    not d.name().endswith('room'):
                # create a constant from declaration
                c = d()
                if not z3.is_array(c) and c.sort().kind() != z3.Z3_UNINTERPRETED_SORT:
                    block.append(c == m[d])
        s.add(z3.simplify(z3.Not(z3.And(*block))))

def convert(map : Dict):
    def iter():
        for k,v in map.items():
            if k == 'room':
                yield (k, Room.get(map["room"]))
            elif k == 'lab':
                yield (k, Lab.get(map["lab"]))
            elif k == 'time':
                yield (k, TimeSlot.get(map["time"]))
            else:
                yield (k, v)
    return dict(iter())

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <json_config> [limit=10]")
        exit(1)
    
    limit = 10 if len(sys.argv) == 2 else int(sys.argv[2])
    print(f"> Using limit={limit}")
    init_data(sys.argv[1])
    print("> Initialized data")
    C = make_constraints()
    print("> Made all constraints")
    for i, m, s in get_models(C, limit):
        print (f'Model {i}:')
        print('  ',end='')
        for j in ['time', 'conflicts', 'decisions', 'max memory', 'propagations']:
            print(f'{j}:{s.get_key_value(j)}   ',end='')
        print('\n')

        assigned = list(convert(c.evaluate(m)) for c in COURSES)

        for map in assigned:
            print(','.join(str(map[k]) for k in ["name", "faculty", "room", "lab", "time"]))

        with open(f'model{i}.json', 'w') as outfile:
            # eval(repr()) is okay to use in some cases!
            obj = eval(repr(assigned))
            json.dump({'schedule' : obj }, outfile)

        try:
            print()
            input('press <enter> for the next schedule (or Ctrl+D) to quit')
            print()
            print("> Getting next model...")
        except:
            exit(0)
