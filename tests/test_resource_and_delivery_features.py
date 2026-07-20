"""Regression coverage for resource metadata and delivery modes."""

from copy import deepcopy

import pytest
from pydantic import ValidationError

from scheduler import Scheduler, validate_combined_config_data
from scheduler.config import RoomConfig
from scheduler.problem import SchedulingProblem
from scheduler.server import _estimate_candidate_slots, _schedule_response_rows
from scheduler.solver import SolverEngine
from tests.scenario_builders import config_from, minimal_config_data


def test_explicit_section_id_is_stable_and_duplicate_display_names_are_rejected() -> None:
    data = minimal_config_data()
    data["config"]["courses"][0]["section_id"] = "HON"

    schedule = next(Scheduler(config_from(data)).get_models())

    assert str(schedule[0].course) == "CS101.HON"

    duplicate = deepcopy(data)
    duplicate["config"]["courses"].append(deepcopy(duplicate["config"]["courses"][0]))
    with pytest.raises(ValidationError, match="Duplicate course section identifiers"):
        config_from(duplicate)


def test_resource_features_filter_rooms_and_lab() -> None:
    data = minimal_config_data()
    data["config"]["rooms"] = [
        {"name": "plain-room", "capacity": 30},
        {"name": "accessible-room", "capacity": 30, "features": ["accessible"]},
    ]
    data["config"]["labs"] = [
        {"name": "plain-lab", "capacity": 30},
        {"name": "gpu-lab", "capacity": 30, "features": ["gpu"]},
    ]
    data["config"]["courses"][0].update(
        {
            "room": ["plain-room", "accessible-room"],
            "lab": ["plain-lab", "gpu-lab"],
            "required_room_features": ["accessible"],
            "required_lab_features": ["gpu"],
        }
    )

    scheduler = Scheduler(config_from(data))
    schedule = next(scheduler.get_models())

    assert schedule[0].room == "accessible-room"
    assert schedule[0].lab == "gpu-lab"
    assert scheduler.audit_schedule(schedule).is_valid

    schedule[0].room = "plain-room"
    room_feature_violation = next(
        item for item in scheduler.audit_schedule(schedule).constraint_violations if item.kind == "course_room_features"
    )
    assert "/config/rooms/0/features" in room_feature_violation.locations


def test_removed_lab_groups_are_rejected_instead_of_silently_ignored() -> None:
    data = minimal_config_data()
    data["config"]["courses"][0]["lab_groups"] = [{"group_id": "A", "capacity": 30}]

    with pytest.raises(ValidationError, match="lab_groups"):
        config_from(data)


@pytest.mark.parametrize("reserve_room_during_lab,has_model", [(True, False), (False, True)])
def test_room_availability_can_exclude_lab_occupancy(reserve_room_during_lab: bool, has_model: bool) -> None:
    data = minimal_config_data()
    data["config"]["rooms"][0]["times"] = {"WED": ["08:00-20:00"]}
    data["config"]["courses"][0]["reserve_room_during_lab"] = reserve_room_during_lab

    schedule = next(Scheduler(config_from(data)).get_models(), None)

    assert (schedule is not None) is has_model
    if schedule is not None:
        assert Scheduler(config_from(data)).audit_schedule(schedule).is_valid


@pytest.mark.parametrize("reserve_room_during_lab,has_model", [(True, False), (False, True)])
def test_lab_meeting_option_controls_lecture_room_collisions(reserve_room_during_lab: bool, has_model: bool) -> None:
    data = minimal_config_data()
    data["time_slot_config"]["classes"][0]["start_time"] = "08:00"
    data["time_slot_config"]["classes"].append(
        {
            "credits": 3,
            "start_time": "08:00",
            "meetings": [{"day": "MON", "duration": 110, "lab": False}],
        }
    )
    data["config"]["courses"][0]["reserve_room_during_lab"] = reserve_room_during_lab
    data["config"]["courses"].append(
        {
            "course_id": "CS102",
            "credits": 3,
            "capacity": 30,
            "room": ["R1"],
            "lab": [],
            "conflicts": [],
            "faculty": ["F2"],
        }
    )
    data["config"]["faculty"].append(
        {
            "name": "F2",
            "maximum_credits": 3,
            "minimum_credits": 3,
            "unique_course_limit": 1,
            "times": {"MON": ["08:00-20:00"]},
        }
    )

    schedule = next(Scheduler(config_from(data)).get_models(), None)

    assert (schedule is not None) is has_model


def _separate_lab_section_data(*, lab_first: bool) -> dict:
    data = minimal_config_data()
    lab_section = {
        "course_id": "CS101",
        "section_id": "LAB",
        "credits": 1,
        "capacity": 30,
        "room": [],
        "lab": ["L1"],
        "reserve_room_during_lab": False,
        "conflicts": [],
        "faculty": ["F1"],
    }
    lecture_section = {
        "course_id": "CS101",
        "section_id": "LEC",
        "credits": 3,
        "capacity": 30,
        "room": ["R1"],
        "lab": [],
        "conflicts": [],
        "faculty": ["F1"],
    }
    data["config"]["courses"] = [lab_section, lecture_section] if lab_first else [lecture_section, lab_section]
    data["config"]["faculty"][0].update({"maximum_credits": 4, "minimum_credits": 4, "unique_course_limit": 1})
    data["time_slot_config"]["classes"] = [
        {
            "credits": 1,
            "start_time": "08:00",
            "meetings": [{"day": "MON", "duration": 110, "lab": True}],
        },
        {
            "credits": 3,
            "start_time": "08:00",
            "meetings": [{"day": "WED", "duration": 110, "lab": False}],
        },
    ]
    return data


@pytest.mark.parametrize("lab_first", [True, False])
def test_separate_lab_section_is_roomless_and_order_independent(lab_first: bool) -> None:
    scheduler = Scheduler(config_from(_separate_lab_section_data(lab_first=lab_first)))

    schedule = next(scheduler.get_models())

    lab_assignment = next(item for item in schedule if str(item.course) == "CS101.LAB")
    assert lab_assignment.room is None
    assert lab_assignment.lab == "L1"
    assert scheduler.audit_schedule(schedule).is_valid


def test_lab_only_pattern_ignores_unused_undersized_lecture_room() -> None:
    data = minimal_config_data()
    data["config"]["rooms"][0]["capacity"] = 1
    data["config"]["courses"][0]["reserve_room_during_lab"] = False
    data["time_slot_config"]["classes"][0]["meetings"] = [{"day": "MON", "duration": 110, "lab": True}]
    scheduler = Scheduler(config_from(data))

    schedule = next(scheduler.get_models())
    diagnosis = scheduler.diagnose()

    assert schedule[0].room is None
    assert schedule[0].lab == "L1"
    assert scheduler.audit_schedule(schedule).is_valid
    assert diagnosis.status == "satisfiable"
    assert not any(item.kind.startswith("course_room_capacity") for item in diagnosis.preflight_findings)
    assert not any(item.kind == "course_room_capacity_coverage" for item in diagnosis.capacity_analysis)


def test_roomless_physical_lecture_pattern_is_rejected() -> None:
    data = minimal_config_data()
    data["config"]["courses"][0].update({"room": [], "lab": []})
    data["time_slot_config"]["classes"][0]["meetings"] = [{"day": "MON", "duration": 110, "lab": False}]

    with pytest.raises(ValidationError, match="run without a room"):
        config_from(data)


def test_missing_lab_assignment_does_not_change_room_occupancy_audit() -> None:
    data = minimal_config_data()
    data["config"]["rooms"][0]["times"] = {"WED": ["08:00-20:00"]}
    data["config"]["courses"][0]["reserve_room_during_lab"] = False
    scheduler = Scheduler(config_from(data))
    schedule = next(scheduler.get_models())
    schedule[0].lab = None

    audit = scheduler.audit_schedule(schedule)
    kinds = {violation.kind for violation in audit.constraint_violations}

    assert "course_lab_eligibility" in kinds
    assert "course_room_availability" not in kinds


def test_room_overlap_relations_are_reused_for_equivalent_course_domains() -> None:
    data = minimal_config_data()
    base_course = data["config"]["courses"][0]
    base_course.update({"course_id": "CS100", "section_id": "A", "lab": []})
    data["time_slot_config"]["classes"][0]["meetings"][0]["lab"] = False
    data["config"]["courses"] = []
    data["config"]["faculty"] = []
    for index in range(3):
        faculty = f"F{index}"
        course = deepcopy(base_course)
        course.update({"course_id": f"CS10{index}", "section_id": "A", "faculty": [faculty]})
        data["config"]["courses"].append(course)
        data["config"]["faculty"].append(
            {
                "name": faculty,
                "maximum_credits": 4,
                "minimum_credits": 4,
                "unique_course_limit": 1,
                "times": {day: ["08:00-20:00"] for day in ("MON", "TUE", "WED", "THU", "FRI")},
            }
        )

    engine = SolverEngine(SchedulingProblem.from_config(config_from(data)))

    assert len(engine.artifacts.relations.room_overlaps) == 1


def test_room_overlap_repairs_cannot_escape_through_relaxed_time_domains() -> None:
    data = minimal_config_data()
    data["config"]["labs"] = []
    data["config"]["courses"] = [
        {
            "course_id": "A",
            "credits": 1,
            "capacity": 30,
            "room": ["R1"],
            "lab": [],
            "conflicts": [],
            "faculty": ["F1"],
        },
        {
            "course_id": "B",
            "credits": 2,
            "capacity": 30,
            "room": ["R1"],
            "lab": [],
            "conflicts": [],
            "faculty": ["F2"],
        },
    ]
    data["config"]["faculty"] = [
        {
            "name": "F1",
            "maximum_credits": 1,
            "minimum_credits": 1,
            "unique_course_limit": 1,
            "times": {"MON": ["08:00-20:00"]},
        },
        {
            "name": "F2",
            "maximum_credits": 2,
            "minimum_credits": 2,
            "unique_course_limit": 1,
            "times": {"MON": ["08:00-20:00"]},
        },
    ]
    data["time_slot_config"]["classes"] = [
        {
            "credits": credits,
            "start_time": "08:00",
            "meetings": [{"day": "MON", "duration": 120, "lab": False}],
        }
        for credits in (1, 2)
    ]

    diagnosis = Scheduler(config_from(data)).diagnose()

    assert diagnosis.status == "unsatisfiable"
    assert [tuple(item.kind for item in repair.relaxed_constraints) for repair in diagnosis.repair_sets] == [
        ("shared_room_overlap",)
    ]


def test_online_course_uses_no_physical_room_and_serializes_delivery() -> None:
    data = minimal_config_data()
    data["config"]["courses"][0].update({"room": [], "lab": [], "modality": "online"})
    for meeting in data["time_slot_config"]["classes"][0]["meetings"]:
        meeting["lab"] = False
        meeting["delivery"] = "online"

    scheduler = Scheduler(config_from(data))
    instance = next(scheduler.get_models())[0]

    assert instance.room is None
    assert instance.lab is None
    assert {meeting.delivery for meeting in instance.times} == {"online"}
    assert scheduler.audit_schedule([instance]).is_valid
    row = _schedule_response_rows([instance])[0].model_dump(mode="json")
    assert {meeting["delivery"] for meeting in row["times"]} == {"online"}
    assert row["lab"] is None
    assert row["lab_index"] is None


def test_hybrid_course_combines_online_lecture_and_in_person_lab() -> None:
    data = minimal_config_data()
    data["config"]["courses"][0]["modality"] = "hybrid"
    data["time_slot_config"]["classes"][0]["meetings"][1]["delivery"] = "online"

    scheduler = Scheduler(config_from(data))
    instance = next(scheduler.get_models())[0]

    assert {meeting.delivery for meeting in instance.times} == {"in_person", "online"}
    lab_time = instance.time.lab_time()
    assert lab_time is not None
    assert lab_time.delivery == "in_person"
    assert scheduler.audit_schedule([instance]).is_valid


def test_supporting_facts_use_the_modality_filtered_time_domain() -> None:
    data = minimal_config_data()
    data["config"]["labs"] = []
    data["config"]["courses"][0].update({"room": [], "lab": [], "modality": "online"})
    data["config"]["faculty"][0]["mandatory_days"] = ["TUE"]
    data["time_slot_config"]["classes"] = [
        {
            "credits": 4,
            "start_time": "08:00",
            "meetings": [{"day": "MON", "duration": 110, "lab": False, "delivery": "online"}],
        },
        {
            "credits": 4,
            "start_time": "08:00",
            "meetings": [{"day": "TUE", "duration": 110, "lab": False, "delivery": "in_person"}],
        },
    ]

    diagnosis = Scheduler(config_from(data)).diagnose()
    possible_days = next(item for item in diagnosis.supporting_facts if item.kind == "course_possible_teaching_days")

    assert possible_days.subjects == ("F1", "CS101.01", "MON")
    assert any(
        item.kind == "course_day_pattern_gap" and item.subjects == ("CS101.01", "TUE")
        for item in diagnosis.supporting_facts
    )


def test_reverse_declared_course_conflict_is_audited() -> None:
    data = minimal_config_data()
    data["config"]["courses"][0].update({"lab": [], "faculty": ["F1"]})
    data["time_slot_config"]["classes"][0]["meetings"][0]["lab"] = False
    data["config"]["courses"].append(
        {
            "course_id": "CS102",
            "credits": 4,
            "capacity": 30,
            "room": ["R1"],
            "lab": [],
            "conflicts": ["CS101"],
            "faculty": ["F2"],
        }
    )
    data["config"]["faculty"].append(
        {
            "name": "F2",
            "maximum_credits": 4,
            "minimum_credits": 4,
            "unique_course_limit": 1,
            "times": {day: ["08:00-20:00"] for day in ("MON", "TUE", "WED", "THU", "FRI")},
        }
    )
    scheduler = Scheduler(config_from(data))
    schedule = next(scheduler.get_models())
    schedule[1].time = schedule[0].time

    audit = scheduler.audit_schedule(schedule)

    assert any(item.kind == "course_conflict" for item in audit.constraint_violations)


@pytest.mark.parametrize(
    ("resource_field", "constraint_kind", "resource_path"),
    [
        ("features", "course_room_features", "/config/rooms/0/features"),
        ("times", "course_room_availability", "/config/rooms/0/times"),
    ],
)
def test_room_diagnostic_cores_include_resource_source_paths(
    resource_field: str,
    constraint_kind: str,
    resource_path: str,
) -> None:
    data = minimal_config_data()
    if resource_field == "features":
        data["config"]["rooms"][0]["features"] = []
        data["config"]["courses"][0]["required_room_features"] = ["accessible"]
    else:
        data["config"]["rooms"][0]["times"] = {"TUE": ["08:00-20:00"]}

    diagnosis = Scheduler(config_from(data)).diagnose()
    conflict = next(item for item in diagnosis.conflicting_constraints if item.kind == constraint_kind)

    assert resource_path in conflict.locations
    assert any(edge.source == resource_path for edge in diagnosis.provenance)


def test_lab_availability_selects_valid_candidate_and_auditor_detects_mutation() -> None:
    data = minimal_config_data()
    data["config"]["labs"] = [
        {"name": "closed-monday", "capacity": 30, "times": {"TUE": ["08:00-20:00"]}},
        {"name": "open-monday", "capacity": 30, "times": {"MON": ["08:00-20:00"]}},
    ]
    data["config"]["courses"][0]["lab"] = ["closed-monday", "open-monday"]
    scheduler = Scheduler(config_from(data))
    schedule = next(scheduler.get_models())

    assert schedule[0].lab == "open-monday"
    schedule[0].lab = "closed-monday"
    audit = scheduler.audit_schedule(schedule)
    violation = next(item for item in audit.constraint_violations if item.kind == "course_lab_availability")
    assert "/config/labs/0/times" in violation.locations


@pytest.mark.parametrize(
    "mutation,message",
    [
        ({"lab_groups": [{"group_id": "A", "capacity": 30}]}, "lab_groups"),
        ({"modality": "online", "room": ["R1"], "lab": []}, "cannot require rooms"),
    ],
)
def test_course_metadata_cross_field_validation(mutation: dict, message: str) -> None:
    data = minimal_config_data()
    data["config"]["courses"][0].update(mutation)

    with pytest.raises(ValidationError, match=message):
        config_from(data)


@pytest.mark.parametrize(
    ("mutation", "expected_path"),
    [
        ({"room": [], "lab": []}, "/config/courses/0/room"),
        ({"room": [], "lab": [], "modality": "online"}, "/config/courses/0/modality"),
    ],
)
def test_combined_pattern_validation_reports_course_field_paths(
    mutation: dict,
    expected_path: str,
) -> None:
    data = minimal_config_data()
    data["config"]["courses"][0].update(mutation)
    data["time_slot_config"]["classes"][0]["meetings"] = [{"day": "MON", "duration": 110, "lab": False}]

    result = validate_combined_config_data(data)

    assert result.is_valid is False
    assert result.diagnostics[0].path == expected_path


def test_duplicate_section_validation_reports_duplicate_item_path() -> None:
    data = minimal_config_data()
    data["config"]["courses"][0]["section_id"] = "A"
    data["config"]["courses"].append(deepcopy(data["config"]["courses"][0]))

    result = validate_combined_config_data(data)

    assert result.is_valid is False
    assert result.diagnostics[0].path == "/config/courses/1/section_id"


@pytest.mark.parametrize("features", [None, 3, [None], [""]])
def test_resource_features_report_validation_errors_for_malformed_values(features) -> None:
    with pytest.raises(ValidationError):
        RoomConfig.model_validate({"name": "R1", "capacity": 10, "features": features})


def test_diagnostics_expose_feature_and_capacity_domains() -> None:
    data = minimal_config_data()
    data["config"]["rooms"][0]["features"] = []
    data["config"]["courses"][0]["required_room_features"] = ["accessible"]

    diagnosis = Scheduler(config_from(data)).diagnose()
    domain = diagnosis.candidate_domains[0]

    assert diagnosis.status == "unsatisfiable"
    assert domain.required_room_features == ("accessible",)
    assert domain.feature_compatible_room_candidates == ()
    assert domain.capacity_compatible_lab_candidates == ("L1",)
    assert any(item.kind == "course_room_feature_shortfall" for item in diagnosis.preflight_findings)
    assert any(item.kind == "course_room_features" for item in diagnosis.conflicting_constraints)


def test_problem_normalizes_resource_availability_and_course_policy() -> None:
    data = minimal_config_data()
    data["config"]["rooms"][0].update({"features": ["projector"], "times": {"WED": ["08:00-12:00"]}})
    data["config"]["courses"][0].update(
        {"section_id": "A", "required_room_features": ["projector"], "reserve_room_during_lab": False}
    )

    problem = SchedulingProblem.from_config(config_from(data))

    assert problem.room_policies["R1"].features == frozenset({"projector"})
    assert problem.room_policies["R1"].availability is not None
    assert problem.course_policies["CS101.A"].reserve_room_during_lab is False


def test_api_slot_estimate_is_bounded_for_single_lab_sections() -> None:
    config = config_from(minimal_config_data())
    estimate = _estimate_candidate_slots(config, 1_000_000)

    assert estimate > 0
    assert _estimate_candidate_slots(config, estimate - 1) >= estimate


def test_feature_order_does_not_change_configuration_fingerprint() -> None:
    first = minimal_config_data()
    first["config"]["rooms"][0]["features"] = ["projector", "accessible"]
    first["config"]["courses"][0]["required_room_features"] = ["accessible", "projector"]
    second = deepcopy(first)
    second["config"]["rooms"][0]["features"].reverse()
    second["config"]["courses"][0]["required_room_features"].reverse()

    first_result = validate_combined_config_data(first)
    second_result = validate_combined_config_data(second)

    assert first_result.configuration_fingerprint == second_result.configuration_fingerprint
    assert SchedulingProblem.from_config(config_from(first)).configuration_fingerprint() == (
        first_result.configuration_fingerprint
    )
