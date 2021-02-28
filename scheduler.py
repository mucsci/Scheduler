# Author: Will Killian
#         https://www.github.com/willkill07
#
# Copyright 2021
# All Rights Reserved

from course import Course
from lab import Lab
from room import Room
from time_slot import Day, TimeSlot
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
        ROOMS = {r : Room(r) for r in data['rooms']}
        LABS = {l : Lab(l) for l in data['labs']}
        COURSES = [Course(*(c[v] for v in ["subj","num","lab","room","faculty","conflicts"])) for c in data['courses']]
        
        def get_info(person):
            days = [Day.MON, Day.TUE, Day.WED, Day.THU, Day.FRI]
            masked = functools.reduce(operator.or_, (d for d, m in zip(days, person['days']) if m))
            low, high = person['times']
            return masked, low * 60, high * 60
        FACULTY = { x : get_info(data['faculty'][x]) for x in data['faculty']}
        return (ROOMS, LABS, COURSES, FACULTY)



def z3ify_time_constraint(name: str, fn):
    constraints = []
    z3fn = z3.Function(name, z3.IntSort(), z3.IntSort(), z3.BoolSort())
    for i, j in itertools.combinations(ALL_SLOTS, 2):
        ii, jj = z3.IntVal(i.id), z3.IntVal(j.id)
        if fn(i, j):
            constraints += [z3fn(ii, jj), z3fn(jj, ii)]
        else:
            constraints += [z3.Not(z3fn(ii, jj)), z3.Not(z3fn(jj, ii))]
    for i in ALL_SLOTS:
        ii = z3.IntVal(i.id)
        constraints += [z3fn(ii, ii)]
    return z3fn, constraints


def init_data(filename: str):
    global ROOMS
    global LABS
    global COURSES
    global FACULTY
    global ALL_SLOTS

    ROOMS, LABS, COURSES, FACULTY = load(filename)
    ALL_SLOTS = list(time_slots())

def make_constraints():

    # abstract function constraints
    overlaps, o_constraints = z3ify_time_constraint('overlaps', TimeSlot.overlaps)
    labs_on_same_day, o_labs_on_same_day = z3ify_time_constraint('labs_on_same_day', TimeSlot.labs_on_same_day)
    lab_overlaps, i_constraints = z3ify_time_constraint('lab_overlaps', TimeSlot.lab_overlaps)
    next_to, n_constraints = z3ify_time_constraint('next_to', TimeSlot.next_to)
    
    fn_constraints = o_constraints + i_constraints + n_constraints + o_labs_on_same_day
    
    # basic identity constraints and bounds
    def basic_constraints():
        for c in COURSES:
            # can the time slot be assigned?
            yield z3.And(TimeSlot.min_id() <= c.time(), c.time() <= TimeSlot.max_id())
            mask, start, stop = FACULTY[c.faculty]
            # check the faculty time constraint
            yield z3.And(*(c.time() != slot.id for slot in ALL_SLOTS if not slot.in_time_range(mask, start, stop)))
            # add constraint that all three two-hour period must be on different days
            # TODO -- must restrict this to NOT apply to TR-only faculty
            if len(list(x for x in COURSES if x.faculty == c.faculty)) == 3:
                yield z3.Or(*(z3.Not(labs_on_same_day(c.time(), d.time())) for d in COURSES if c != d and c.faculty == d.faculty))

    def overlapping_constraints():
        # - check for unique, non-overlapping timeslots for each faculty
        for name in FACULTY.keys():
            assigned = list(c.time() for c in COURSES if c.faculty == name)
            yield z3.And(*(z3.Not(overlaps(i,j)) for i,j in itertools.combinations(assigned, 2)))
        
        # - check the other courses time slot constraint(s)
        for c in COURSES:
            for conflict_num in c.conflicts:
                for other in filter(lambda x: x.num == conflict_num, (c for c in COURSES)):
                    yield z3.Not(overlaps(c.time(), other.time()))

    def next_to_constraints():
        # - check for unique, non-overlapping timeslots for each faculty
        for name in FACULTY.keys():
            courses = [c for c in COURSES if c.faculty == name]
            for i, j in itertools.combinations(courses, 2):
                if i.num == j.num:
                    yield next_to(i.time(), j.time())

    # assign to a lab (or none)
    # - ensure no timeslot + lab conflicts exist
    def lab_assign_constraints():
        for c in COURSES:
            if c.labs:
                pass
                yield z3.Or(*(c.lab() == lab.id for name,lab in LABS.items() if name in c.labs))
        for i, j in itertools.combinations(COURSES, 2):
            if i.labs and j.labs:
                yield z3.simplify(z3.Implies(i.lab() == j.lab(), z3.Not(lab_overlaps(i.time(), j.time()))))

    # assign to a classroom
    # - ensure no timeslot + classroom conflicts exist
    def room_assign_constraints():
        for c in COURSES:
            if c.rooms:
                yield z3.Or(*(c.room() == room.id for name,room in ROOMS.items() if name in c.rooms))
        for i, j in itertools.combinations(COURSES, 2):
            # use implication as the filter
            yield z3.Implies(i.room() == j.room(), z3.Not(overlaps(i.time(), j.time())))

    all_constraints = [
        z3.simplify(z3.And(*(x for x in basic_constraints()))),
        z3.simplify(z3.And(*(x for x in overlapping_constraints()))),
        z3.simplify(z3.And(*(x for x in lab_assign_constraints()))),
        z3.simplify(z3.And(*(x for x in room_assign_constraints()))),
        # NOTE: comment out if no schedules are generated and you tweeked faculty days already
        z3.simplify(z3.And(*(x for x in next_to_constraints())))
    ]
    
    return fn_constraints + all_constraints

def get_models(F, M=10):
    s = z3.Solver()
    s.add(F)
    i = 0
    while i < M and s.check() == z3.sat:
        m = s.model()
        yield i, m
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
    else:
        # failed or limit -- print stats of last check
        print(s.statistics())

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
    for i, m in get_models(C, limit):
        print (f'Model {i}:')
        for c in COURSES:
            timeslot = str(TimeSlot.get(m.eval(c.time()).as_long()))
            room = str(Room.get(m.eval(c.room()).as_long()))
            lab = 'None' if not c.labs else str(Lab.get(m.eval(c.lab()).as_long()))
            print (f'{c},{c.faculty},{room},{lab},{timeslot}')
        try:
            input('press <enter> for the next schedule (or Ctrl+D) to quit')
        except:
            exit(0)
