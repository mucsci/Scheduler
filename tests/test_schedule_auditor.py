"""Unit tests for independent schedule auditing."""

import pytest

from scheduler import CombinedConfig
from scheduler.audit import ScheduleAuditor
from scheduler.models import Day, Duration, TimeInstance, TimePoint, TimeSlot
from scheduler.problem import SchedulingProblem
from scheduler.solver import SolverEngine
from tests.scenario_builders import config_from, minimal_config_data, two_course_config_data


def _solved(config: CombinedConfig):
    problem = SchedulingProblem.from_config(config)
    schedule = next(SolverEngine(problem).get_models())
    return problem, schedule, ScheduleAuditor(problem)


def _unexpected_slot() -> TimeSlot:
    return TimeSlot(
        times=[
            TimeInstance(
                day=Day.FRI,
                start=TimePoint.make_from(6, 0),
                duration=Duration(duration=30),
            )
        ]
    )


def test_auditor_validates_a_decoded_schedule_without_a_model(
    minimal_combined_config: CombinedConfig,
) -> None:
    problem = SchedulingProblem.from_config(minimal_combined_config)
    schedule = next(SolverEngine(problem).get_models())
    auditor = ScheduleAuditor(problem)

    assert auditor.audit_schedule(schedule).is_valid is True

    schedule[0].room = "not-eligible"
    invalid = auditor.audit_schedule(schedule)
    assert invalid.is_valid is False
    assert any(item.kind == "course_room_eligibility" for item in invalid.constraint_violations)
    unknown_usage = next(item for item in invalid.resource_usage if item.resource == "not-eligible")
    assert unknown_usage.capacity is None
    assert unknown_usage.capacity_violations == ()


@pytest.mark.parametrize(
    "mutation,expected_kind",
    [
        (lambda schedule: schedule.clear(), "schedule_course_coverage"),
        (lambda schedule: setattr(schedule[0], "faculty", "not-eligible"), "course_faculty_eligibility"),
        (lambda schedule: setattr(schedule[0], "room", "not-eligible"), "course_room_eligibility"),
        (lambda schedule: setattr(schedule[0], "lab", "not-eligible"), "course_lab_eligibility"),
        (lambda schedule: setattr(schedule[0], "time", _unexpected_slot()), "course_time_pattern"),
    ],
)
def test_auditor_reports_each_assignment_violation(
    minimal_combined_config: CombinedConfig,
    mutation,
    expected_kind: str,
) -> None:
    _problem, schedule, auditor = _solved(minimal_combined_config)
    mutation(schedule)

    audit = auditor.audit_schedule(schedule)
    diagnostic = next(item for item in audit.constraint_violations if item.kind == expected_kind)

    assert diagnostic.code == "SCHED." + expected_kind.upper().replace("_", ".")
    assert diagnostic.locations


def test_auditor_reports_faculty_availability_violation() -> None:
    data = minimal_config_data()
    data["config"]["faculty"][0]["times"] = {day: ["08:00-10:00"] for day in ("MON", "TUE", "WED", "THU", "FRI")}
    problem, schedule, auditor = _solved(config_from(data))
    schedule[0].time = problem.compatible_slots(problem.courses[0])[-1]

    audit = auditor.audit_schedule(schedule)

    assert any(item.kind == "faculty_availability" for item in audit.constraint_violations)


@pytest.mark.parametrize(
    "field,value,expected_kind",
    [
        ("_faculty_minimum_credits", 5, "faculty_credit_range"),
        ("_faculty_maximum_credits", 3, "faculty_credit_range"),
        ("_faculty_maximum_days", 1, "faculty_maximum_days"),
        ("_faculty_unique_course_limits", 0, "faculty_unique_course_limit"),
    ],
)
def test_auditor_reports_each_workload_violation(
    minimal_combined_config: CombinedConfig,
    field: str,
    value: int,
    expected_kind: str,
) -> None:
    _problem, schedule, auditor = _solved(minimal_combined_config)
    getattr(auditor, field)["F1"] = value

    audit = auditor.audit_schedule(schedule)

    assert any(item.kind == expected_kind for item in audit.constraint_violations)


def test_auditor_reports_missing_mandatory_day(minimal_combined_config: CombinedConfig) -> None:
    _problem, schedule, auditor = _solved(minimal_combined_config)
    auditor._faculty_mandatory_days["F1"] = {Day.TUE}

    audit = auditor.audit_schedule(schedule)

    assert audit.faculty_workloads[0].mandatory_days_satisfied is False
    assert any(item.kind == "faculty_mandatory_day" for item in audit.constraint_violations)


def test_auditor_detects_overlapping_resources_faculty_and_conflicts() -> None:
    data = two_course_config_data()
    problem, schedule, auditor = _solved(config_from(data))
    problem.courses[0].conflicts.append("CS102")
    schedule[1].time = schedule[0].time

    audit = auditor.audit_schedule(schedule)
    kinds = {item.kind for item in audit.constraint_violations}

    assert {
        "shared_room_overlap",
        "shared_lab_overlap",
        "shared_faculty_overlap",
        "course_conflict",
    } <= kinds
    assert all(usage.collisions for usage in audit.resource_usage)


def test_auditor_detects_same_course_resource_and_adjacency_rules() -> None:
    data = two_course_config_data(same_course=True)
    data["config"]["rooms"] = [{"name": "R1", "capacity": 30}, {"name": "R2", "capacity": 30}]
    data["config"]["labs"] = [{"name": "L1", "capacity": 30}, {"name": "L2", "capacity": 30}]
    for course in data["config"]["courses"]:
        course["room"] = ["R1", "R2"]
        course["lab"] = ["L1", "L2"]
    problem, schedule, auditor = _solved(config_from(data))
    schedule[1].room = "R2" if schedule[0].room == "R1" else "R1"
    schedule[1].lab = "L2" if schedule[0].lab == "L1" else "L1"
    slots = problem.compatible_slots(problem.courses[0])
    first, second = next(
        (left, right)
        for left in slots
        for right in slots
        if not left.overlaps(right) and not left.lecture_next_to(right) and not left.lab_next_to(right)
    )
    schedule[0].time, schedule[1].time = first, second

    kinds = {item.kind for item in auditor.audit_schedule(schedule).constraint_violations}

    assert {
        "same_course_room",
        "same_course_lab",
        "same_course_lecture_adjacency",
        "same_course_lab_adjacency",
    } <= kinds


def test_auditor_detects_different_course_adjacency_rules() -> None:
    problem, schedule, auditor = _solved(config_from(two_course_config_data()))
    slots = problem.compatible_slots(problem.courses[0])
    first, second = next(
        (left, right)
        for left in slots
        for right in slots
        if not left.overlaps(right) and left.lecture_next_to(right) and left.lab_next_to(right)
    )
    schedule[0].time, schedule[1].time = first, second

    kinds = {item.kind for item in auditor.audit_schedule(schedule).constraint_violations}

    assert "different_course_lecture_separation" in kinds
    assert "different_course_lab_separation" in kinds


def test_auditor_explains_unselected_faculty_preference() -> None:
    data = minimal_config_data()
    data["optimizer_flags"] = ["faculty_course"]
    data["config"]["faculty"][0].update({"minimum_credits": 0, "course_preferences": {"CS101": 10}})
    data["config"]["faculty"].append(
        {
            "name": "F2",
            "maximum_credits": 4,
            "minimum_credits": 0,
            "unique_course_limit": 1,
            "course_preferences": {"CS101": 0},
            "times": {day: ["08:00-20:00"] for day in ("MON", "TUE", "WED", "THU", "FRI")},
        }
    )
    data["config"]["courses"][0]["faculty"] = ["F1", "F2"]
    _problem, schedule, auditor = _solved(config_from(data))
    schedule[0].faculty = "F2"

    audit = auditor.audit_schedule(schedule)

    assert audit.objective_scores[0].score == 0
    assert audit.objective_scores[0].independent_upper_bound == 10
    assert audit.preference_outcomes[0].kind == "preference_not_selected"


def test_auditor_scores_and_explains_all_pair_objectives() -> None:
    data = two_course_config_data()
    data["optimizer_flags"] = ["same_room", "same_lab", "pack_rooms", "pack_labs"]
    data["config"]["rooms"] = [{"name": "R1", "capacity": 30}, {"name": "R2", "capacity": 30}]
    data["config"]["labs"] = [{"name": "L1", "capacity": 30}, {"name": "L2", "capacity": 30}]
    for course in data["config"]["courses"]:
        course["room"] = ["R1", "R2"]
        course["lab"] = ["L1", "L2"]
    _problem, schedule, auditor = _solved(config_from(data))
    schedule[1].room = "R2" if schedule[0].room == "R1" else "R1"
    schedule[1].lab = "L2" if schedule[0].lab == "L1" else "L1"

    audit = auditor.audit_schedule(schedule)

    assert {score.objective for score in audit.objective_scores} == {
        "same_room",
        "same_lab",
        "pack_rooms",
        "pack_labs",
    }
    assert all(score.score == 0 for score in audit.objective_scores)
    assert {item.subjects[-1] for item in audit.preference_outcomes} == {
        "same_room",
        "same_lab",
        "pack_rooms",
        "pack_labs",
    }


@pytest.mark.parametrize("resource_kind", ["room", "lab"])
def test_auditor_reports_undersized_assigned_resources(resource_kind: str) -> None:
    data = minimal_config_data()
    data["config"]["courses"][0]["capacity"] = 30
    plural = resource_kind + "s"
    field = resource_kind
    data["config"][plural] = [
        {"name": f"small-{resource_kind}", "capacity": 29},
        {"name": f"large-{resource_kind}", "capacity": 30},
    ]
    data["config"]["courses"][0][field] = [f"small-{resource_kind}", f"large-{resource_kind}"]
    problem, schedule, auditor = _solved(config_from(data))
    setattr(schedule[0], field, f"small-{resource_kind}")

    audit = auditor.audit_schedule(schedule)
    usage = next(item for item in audit.resource_usage if item.kind == resource_kind)

    assert any(item.kind == f"course_{resource_kind}_capacity" for item in audit.constraint_violations)
    assert usage.capacity == 29
    assert usage.maximum_assigned_section_capacity == 30
    assert usage.capacity_violations
