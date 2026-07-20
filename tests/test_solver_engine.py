"""Unit tests for Z3 solver ownership."""

import pytest

from scheduler import CombinedConfig
from scheduler.problem import SchedulingProblem
from scheduler.solver import SolverEngine
from tests.scenario_builders import config_from, minimal_config_data, no_lab_config_data, two_course_config_data


def test_solver_artifacts_are_read_only_and_legacy_mirrors_do_not_leak_into_problem(
    minimal_combined_config: CombinedConfig,
) -> None:
    problem = SchedulingProblem.from_config(minimal_combined_config)
    engine = SolverEngine(problem)
    course = problem.courses[0]
    variables = engine.artifacts.course_variables[str(course)]

    assert course.time is None
    assert course.faculty is None
    assert course.room is None
    assert course.lab is None
    solver_course = engine._courses[0]
    assert solver_course.time is variables.time
    assert solver_course.faculty is variables.faculty
    assert solver_course.room is variables.room
    assert solver_course.lab is variables.lab
    assert engine.artifacts.constraints
    assert engine.artifacts.diagnostic_constraints
    with pytest.raises(TypeError):
        engine.artifacts.course_variables[str(course)] = variables  # ty: ignore[invalid-assignment]


def test_solver_engine_enumerates_models_directly(
    minimal_combined_config: CombinedConfig,
) -> None:
    engine = SolverEngine(SchedulingProblem.from_config(minimal_combined_config))

    schedule = next(engine.get_models())

    assert [str(instance.course) for instance in schedule] == ["CS101.01"]
    assert schedule[0].course.time is engine.artifacts.course_variables["CS101.01"].time
    schedule[0].course.rooms.append("caller mutation")
    assert "caller mutation" not in engine._courses[0].rooms


def _has_model(data: dict) -> bool:
    engine = SolverEngine(SchedulingProblem.from_config(config_from(data)))
    return next(engine.get_models(), None) is not None


@pytest.mark.parametrize(
    "constraint_family,mutate",
    [
        (
            "minimum credits",
            lambda data: data["config"]["faculty"].append(
                {
                    "name": "F2",
                    "maximum_credits": 4,
                    "minimum_credits": 4,
                    "unique_course_limit": 1,
                    "times": {"MON": ["08:00-20:00"]},
                }
            ),
        ),
        (
            "maximum days",
            lambda data: data["config"]["faculty"][0].update({"maximum_days": 1}),
        ),
        (
            "mandatory day",
            lambda data: data["config"]["faculty"][0].update({"mandatory_days": ["TUE"]}),
        ),
    ],
)
def test_solver_enforces_faculty_constraint_families(constraint_family: str, mutate) -> None:
    data = minimal_config_data()
    mutate(data)

    assert _has_model(data) is False, constraint_family


def test_solver_enforces_unique_course_limit() -> None:
    data = two_course_config_data()
    data["config"]["faculty"][0]["unique_course_limit"] = 1

    assert _has_model(data) is False


@pytest.mark.parametrize("kind", ["room", "faculty", "conflict"])
def test_solver_enforces_pairwise_hard_constraints(kind: str) -> None:
    data = two_course_config_data()
    data["time_slot_config"]["classes"][0]["start_time"] = "08:00"
    data["config"]["labs"].append({"name": "L2", "capacity": 30})
    data["config"]["courses"][1]["lab"] = ["L2"]
    if kind == "faculty":
        data["config"]["rooms"] = [{"name": "R1", "capacity": 30}, {"name": "R2", "capacity": 30}]
        data["config"]["courses"][1]["room"] = ["R2"]
    elif kind == "room":
        data["config"]["faculty"].append(
            {
                "name": "F2",
                "maximum_credits": 4,
                "minimum_credits": 0,
                "unique_course_limit": 1,
                "times": {day: ["08:00-20:00"] for day in ("MON", "TUE", "WED", "THU", "FRI")},
            }
        )
        data["config"]["courses"][1]["faculty"] = ["F2"]
    else:
        data["config"]["rooms"] = [{"name": "R1", "capacity": 30}, {"name": "R2", "capacity": 30}]
        data["config"]["courses"][1]["room"] = ["R2"]
        data["config"]["faculty"].append(
            {
                "name": "F2",
                "maximum_credits": 4,
                "minimum_credits": 0,
                "unique_course_limit": 1,
                "times": {day: ["08:00-20:00"] for day in ("MON", "TUE", "WED", "THU", "FRI")},
            }
        )
        data["config"]["courses"][1]["faculty"] = ["F2"]
        data["config"]["courses"][0]["conflicts"] = ["CS102"]
        data["config"]["courses"][1]["conflicts"] = ["CS101"]

    assert _has_model(data) is False


def test_solver_blocks_models_and_preserves_deterministic_symbol_names() -> None:
    data = minimal_config_data()
    data["limit"] = 3
    problem = SchedulingProblem.from_config(config_from(data))
    engine = SolverEngine(problem)

    schedules = list(engine.get_models())
    signatures = [tuple(item.as_csv() for item in schedule) for schedule in schedules]

    assert len(signatures) == 3
    assert len(set(signatures)) == 3
    assert [str(value) for value in engine.artifacts.symbols.faculty_constants.values()] == ["faculty_0"]
    assert [str(value) for value in engine.artifacts.symbols.room_constants.values()] == ["room_0"]
    assert str(engine.artifacts.symbols.lab_constants[None]) == "lab_none"


def test_solver_decodes_no_lab_and_honors_each_check_timeout() -> None:
    problem = SchedulingProblem.from_config(config_from(no_lab_config_data()))
    engine = SolverEngine(problem, solver_timeout_ms=250)

    schedule = next(engine.get_models())

    assert schedule[0].lab is None
    assert engine._solver_timeout_ms == 250


@pytest.mark.parametrize("timeout", [0, -1, True, 1.5, "250"])
def test_solver_rejects_invalid_timeouts(timeout) -> None:
    with pytest.raises(ValueError, match="positive integer"):
        SolverEngine(SchedulingProblem.from_config(config_from(minimal_config_data())), solver_timeout_ms=timeout)


def test_solver_enumerates_faculty_only_assignment_differences() -> None:
    data = minimal_config_data()
    data["limit"] = 10
    data["time_slot_config"]["classes"][0]["start_time"] = "08:00"
    data["config"]["faculty"][0]["minimum_credits"] = 0
    data["config"]["faculty"].append(
        {
            "name": "F2",
            "maximum_credits": 4,
            "minimum_credits": 0,
            "unique_course_limit": 1,
            "times": {day: ["08:00-20:00"] for day in ("MON", "TUE", "WED", "THU", "FRI")},
        }
    )
    data["config"]["courses"][0]["faculty"] = ["F1", "F2"]

    schedules = list(SolverEngine(SchedulingProblem.from_config(config_from(data))).get_models())

    assert {schedule[0].faculty for schedule in schedules} == {"F1", "F2"}
    assert len(schedules) == 2


def test_solver_handles_empty_generated_time_domain_as_unsatisfiable() -> None:
    data = minimal_config_data()
    data["time_slot_config"]["classes"][0]["start_time"] = "23:00"
    problem = SchedulingProblem.from_config(config_from(data))
    engine = SolverEngine(problem)

    assert list(engine.get_models()) == []
    assert engine.enumeration_completion_reason == "solution_space_exhausted"
    assert str(engine.artifacts.symbols.time_slot_constants[None]) == "time_slot_none"


def test_decoded_schedules_do_not_expose_solver_owned_mutable_objects() -> None:
    data = minimal_config_data()
    data["limit"] = 2
    engine = SolverEngine(SchedulingProblem.from_config(config_from(data)))
    models = engine.get_models()
    first = next(models)
    first[0].course.capacity = 1
    first[0].time.times.clear()

    second = next(models)

    assert second[0].course.capacity == 30
    assert second[0].time.times


def test_solver_optimizes_faculty_course_room_and_lab_preferences() -> None:
    data = minimal_config_data()
    data["optimizer_flags"] = ["faculty_course", "faculty_room", "faculty_lab"]
    data["config"]["rooms"] = [{"name": "R1", "capacity": 30}, {"name": "R2", "capacity": 30}]
    data["config"]["labs"] = [{"name": "L1", "capacity": 30}, {"name": "L2", "capacity": 30}]
    data["config"]["courses"][0].update(
        {
            "room": ["R1", "R2"],
            "lab": ["L1", "L2"],
            "faculty": ["F1", "F2"],
        }
    )
    data["config"]["faculty"][0].update(
        {
            "minimum_credits": 0,
            "course_preferences": {"CS101": 1},
            "room_preferences": {"R1": 1, "R2": 0},
            "lab_preferences": {"L1": 1, "L2": 0},
        }
    )
    data["config"]["faculty"].append(
        {
            "name": "F2",
            "maximum_credits": 4,
            "minimum_credits": 0,
            "unique_course_limit": 1,
            "course_preferences": {"CS101": 10},
            "room_preferences": {"R1": 0, "R2": 10},
            "lab_preferences": {"L1": 0, "L2": 10},
            "times": {day: ["08:00-20:00"] for day in ("MON", "TUE", "WED", "THU", "FRI")},
        }
    )

    schedule = next(SolverEngine(SchedulingProblem.from_config(config_from(data))).get_models())

    assert (schedule[0].faculty, schedule[0].room, schedule[0].lab) == ("F2", "R2", "L2")


def test_solver_optimizes_same_resources_for_one_faculty() -> None:
    data = two_course_config_data()
    data["optimizer_flags"] = ["same_room", "same_lab"]
    data["config"]["rooms"] = [{"name": "R1", "capacity": 30}, {"name": "R2", "capacity": 30}]
    data["config"]["labs"] = [{"name": "L1", "capacity": 30}, {"name": "L2", "capacity": 30}]
    for course in data["config"]["courses"]:
        course["room"] = ["R1", "R2"]
        course["lab"] = ["L1", "L2"]

    schedule = next(SolverEngine(SchedulingProblem.from_config(config_from(data))).get_models())

    assert schedule[0].room == schedule[1].room
    assert schedule[0].lab == schedule[1].lab


def test_solver_optimizes_packed_resources_for_different_faculty() -> None:
    data = two_course_config_data()
    data["optimizer_flags"] = ["pack_rooms", "pack_labs"]
    data["config"]["faculty"].append(
        {
            "name": "F2",
            "maximum_credits": 4,
            "minimum_credits": 0,
            "unique_course_limit": 1,
            "times": {day: ["08:00-20:00"] for day in ("MON", "TUE", "WED", "THU", "FRI")},
        }
    )
    data["config"]["courses"][1]["faculty"] = ["F2"]

    schedule = next(SolverEngine(SchedulingProblem.from_config(config_from(data))).get_models())

    assert schedule[0].room == schedule[1].room
    assert schedule[0].lab == schedule[1].lab
    assert schedule[0].time.lecture_next_to(schedule[1].time)
    assert schedule[0].time.lab_next_to(schedule[1].time)


def test_capacity_constraints_override_undersized_resource_preferences() -> None:
    data = minimal_config_data()
    data["optimizer_flags"] = ["faculty_room", "faculty_lab"]
    data["config"]["courses"][0]["capacity"] = 30
    data["config"]["rooms"] = [
        {"name": "small-room", "capacity": 29},
        {"name": "exact-room", "capacity": 30},
    ]
    data["config"]["labs"] = [
        {"name": "small-lab", "capacity": 29},
        {"name": "exact-lab", "capacity": 30},
    ]
    data["config"]["courses"][0].update({"room": ["small-room", "exact-room"], "lab": ["small-lab", "exact-lab"]})
    data["config"]["faculty"][0].update(
        {
            "room_preferences": {"small-room": 10, "exact-room": 1},
            "lab_preferences": {"small-lab": 10, "exact-lab": 1},
        }
    )

    schedule = next(SolverEngine(SchedulingProblem.from_config(config_from(data))).get_models())

    assert schedule[0].room == "exact-room"
    assert schedule[0].lab == "exact-lab"


@pytest.mark.parametrize("resource_kind", ["room", "lab"])
def test_solver_rejects_sections_when_all_allowed_resources_are_undersized(resource_kind: str) -> None:
    data = minimal_config_data()
    data["config"]["courses"][0]["capacity"] = 31
    if resource_kind == "room":
        data["config"]["labs"][0]["capacity"] = 31
    else:
        data["config"]["rooms"][0]["capacity"] = 31

    assert _has_model(data) is False
