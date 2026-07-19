"""Unit tests for solver-independent problem normalization."""

from scheduler import CombinedConfig
from scheduler.problem import SchedulingProblem
from tests.scenario_builders import config_from, minimal_config_data, no_lab_config_data


def test_problem_normalizes_null_faculty_from_preferences(
    minimal_combined_config: CombinedConfig,
) -> None:
    config = minimal_combined_config.model_copy(deep=True)
    config.config.courses[0].faculty = None
    config.config.faculty[0].course_preferences = {"CS101": 7}

    problem = SchedulingProblem.from_config(config)

    assert problem.courses[0].faculties == ["F1"]
    assert problem.course_faculty_origins["CS101.01"] == "derived_from_preferences"
    assert problem.course_policies["CS101.01"].faculties == ("F1",)
    assert problem.course_policies["CS101.01"].faculty_origin == "derived_from_preferences"


def test_problem_caches_compatible_slot_domains(
    minimal_combined_config: CombinedConfig,
) -> None:
    problem = SchedulingProblem.from_config(minimal_combined_config)
    course = problem.courses[0]

    first = problem.compatible_slots(course)
    second = problem.compatible_slots(course)

    assert first is second
    assert first
    assert all(slot.has_lab() for slot in first)
    assert len(problem.configuration_fingerprint()) == 64


def test_problem_builds_separate_credit_ranges_and_source_paths() -> None:
    data = minimal_config_data()
    data["config"]["courses"].append(
        {
            "course_id": "CS102",
            "credits": 3,
            "room": ["R1"],
            "lab": [],
            "conflicts": [],
            "faculty": ["F1"],
        }
    )
    data["config"]["faculty"][0].update({"maximum_credits": 7, "unique_course_limit": 2})
    data["time_slot_config"]["classes"].append(
        {
            "credits": 3,
            "meetings": [{"day": "TUE", "duration": 75, "lab": False}],
            "start_time": "09:00",
        }
    )

    problem = SchedulingProblem.from_config(config_from(data))

    assert set(problem.slot_ranges) == {3, 4}
    assert problem.course_policies["CS102.01"].config_path == "/config/courses/1"
    assert problem.faculty_policies["F1"].config_path == "/config/faculty/0"
    assert [item.day.name for item in problem.faculty_policies["F1"].availability] == [
        "MON",
        "TUE",
        "WED",
        "THU",
        "FRI",
    ]


def test_problem_separates_lab_and_no_lab_domains_for_same_credits() -> None:
    data = minimal_config_data()
    data["config"]["courses"].append(
        {
            "course_id": "CS102",
            "credits": 4,
            "room": ["R1"],
            "lab": [],
            "conflicts": [],
            "faculty": ["F1"],
        }
    )
    data["config"]["faculty"][0].update({"maximum_credits": 8, "unique_course_limit": 2})
    data["time_slot_config"]["classes"].append(
        {
            "credits": 4,
            "meetings": [
                {"day": "TUE", "duration": 110, "lab": False},
                {"day": "THU", "duration": 110, "lab": False},
            ],
            "start_time": "10:00",
        }
    )

    problem = SchedulingProblem.from_config(config_from(data))
    lab_slots = problem.compatible_slots(problem.courses[0])
    lecture_slots = problem.compatible_slots(problem.courses[1])

    assert lab_slots and lecture_slots
    assert all(slot.has_lab() for slot in lab_slots)
    assert all(not slot.has_lab() for slot in lecture_slots)
    assert set(lab_slots).isdisjoint(lecture_slots)


def test_problem_supports_globally_empty_labs_and_snapshots_preferences() -> None:
    config = config_from(no_lab_config_data())
    config.config.faculty[0].course_preferences = {"CS101": 8}
    problem = SchedulingProblem.from_config(config)

    config.config.faculty[0].course_preferences["CS101"] = 1

    assert problem.labs == []
    assert problem.faculty_policies["F1"].course_preferences == {"CS101": 8}
    assert all(not slot.has_lab() for slot in problem.compatible_slots(problem.courses[0]))
