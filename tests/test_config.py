"""Tests for Pydantic configuration models (target: full coverage of config.py)."""

import json
from pathlib import Path

import pytest
from pydantic import ValidationError

from scheduler.config import (
    ClassPattern,
    CombinedConfig,
    CourseConfig,
    FacultyConfig,
    Meeting,
    OptimizerFlags,
    SchedulerConfig,
    StrictBaseModel,
    TimeBlock,
    TimeRange,
    TimeSlotConfig,
)
from scheduler.scheduler import load_config_from_file


class SampleStrict(StrictBaseModel):
    """Concrete model for StrictBaseModel behavior tests."""

    name: str
    value: int = 0


# --- TimeBlock / TimeRange ---


@pytest.mark.parametrize(
    ("start", "end"),
    [("09:00", "17:00"), ("00:00", "23:59"), ("09:00", "09:01")],
)
def test_time_block_valid(start: str, end: str) -> None:
    tb = TimeBlock(start=start, spacing=60, end=end)
    assert tb.start == start
    assert tb.spacing == 60


def test_time_block_invalid_end_before_start() -> None:
    with pytest.raises(ValidationError):
        TimeBlock(start="17:00", spacing=30, end="09:00")


def test_time_range_valid_and_str() -> None:
    tr = TimeRange(start="10:00", end="12:00")
    assert str(tr) == "10:00-12:00"


def test_time_range_from_string() -> None:
    tr = TimeRange.from_string("08:30-16:45")
    assert tr.start == "08:30"
    assert tr.end == "16:45"


def test_time_range_invalid_order() -> None:
    with pytest.raises(ValidationError):
        TimeRange(start="12:00", end="10:00")


# --- Meeting / ClassPattern ---


def test_meeting_optional_start_time_and_lab_default() -> None:
    m = Meeting(day="MON", duration=50)
    assert m.start_time is None
    assert m.lab is False


def test_meeting_with_start_time() -> None:
    m = Meeting(day="TUE", start_time="10:00", duration=75, lab=True)
    assert m.lab is True


def test_meeting_invalid_day() -> None:
    with pytest.raises(ValidationError):
        Meeting(day="SAT", duration=50)  # type: ignore[arg-type]


def test_class_pattern_valid() -> None:
    p = ClassPattern(
        credits=3,
        meetings=[Meeting(day="MON", duration=50), Meeting(day="WED", duration=50)],
    )
    assert not p.disabled


def test_class_pattern_empty_meetings() -> None:
    with pytest.raises(ValidationError, match="At least one meeting"):
        ClassPattern(credits=3, meetings=[])


def test_class_pattern_duplicate_days() -> None:
    with pytest.raises(ValidationError, match="Duplicate meeting days"):
        ClassPattern(
            credits=3,
            meetings=[Meeting(day="MON", duration=50), Meeting(day="MON", duration=50)],
        )


def test_class_pattern_disabled_and_start_time() -> None:
    p = ClassPattern(
        credits=4,
        meetings=[Meeting(day="MON", duration=110), Meeting(day="WED", duration=110)],
        disabled=True,
        start_time="10:00",
    )
    assert p.disabled
    assert p.start_time == "10:00"


# --- TimeSlotConfig ---


def _valid_times() -> dict:
    block = {"start": "08:00", "spacing": 60, "end": "20:00"}
    return {d: [block] for d in ("MON", "TUE", "WED", "THU", "FRI")}


def test_time_slot_config_defaults() -> None:
    cfg = TimeSlotConfig(
        times=_valid_times(),
        classes=[ClassPattern(credits=3, meetings=[Meeting(day="MON", duration=50)])],
    )
    assert cfg.max_time_gap == 30
    assert cfg.min_time_overlap == 45


def test_time_slot_config_missing_day() -> None:
    times = _valid_times()
    del times["FRI"]
    with pytest.raises(ValidationError, match="No time blocks defined for FRI"):
        TimeSlotConfig(
            times=times,
            classes=[ClassPattern(credits=3, meetings=[Meeting(day="MON", duration=50)])],
        )


def test_time_slot_config_empty_blocks_for_day() -> None:
    times = _valid_times()
    times["MON"] = []
    with pytest.raises(ValidationError, match="No time blocks defined for MON"):
        TimeSlotConfig(
            times=times,
            classes=[ClassPattern(credits=3, meetings=[Meeting(day="MON", duration=50)])],
        )


def test_time_slot_config_invalid_day_via_validate() -> None:
    """Hit defensive branch when ``times`` contains a non-weekday key (e.g. via ``model_construct``)."""
    b = [TimeBlock(start="08:00", spacing=60, end="20:00")]
    cfg = TimeSlotConfig.model_construct(
        times={"BAD": b, "MON": b, "TUE": b, "WED": b, "THU": b, "FRI": b},
        classes=[ClassPattern(credits=3, meetings=[Meeting(day="MON", duration=50)])],
        max_time_gap=30,
        min_time_overlap=45,
    )
    with pytest.raises(ValueError, match="Invalid day"):
        cfg.validate()


def test_time_slot_config_invalid_day_key() -> None:
    times = _valid_times()
    times["SAT"] = [{"start": "09:00", "spacing": 60, "end": "17:00"}]  # type: ignore[assignment]
    with pytest.raises(ValidationError, match="MON.*FRI|literal_error"):
        TimeSlotConfig(
            times=times,
            classes=[ClassPattern(credits=3, meetings=[Meeting(day="MON", duration=50)])],
        )


def test_time_slot_config_no_classes() -> None:
    with pytest.raises(ValidationError, match="At least one class pattern"):
        TimeSlotConfig(times=_valid_times(), classes=[])


def test_time_slot_config_all_disabled_patterns() -> None:
    with pytest.raises(ValidationError, match="All class patterns are disabled"):
        TimeSlotConfig(
            times=_valid_times(),
            classes=[
                ClassPattern(
                    credits=3,
                    meetings=[Meeting(day="MON", duration=50)],
                    disabled=True,
                )
            ],
        )


# --- FacultyConfig ---


def test_faculty_config_times_from_strings() -> None:
    f = FacultyConfig(
        name="DrX",
        maximum_credits=12,
        minimum_credits=3,
        unique_course_limit=2,
        times={"MON": ["09:00-12:00", "14:00-17:00"], "TUE": ["10:00-11:00"]},
    )
    assert f.times["MON"][0].start == "09:00"
    assert f.times["MON"][0].end == "12:00"


def test_faculty_convert_times_non_dict_returns_unchanged() -> None:
    assert FacultyConfig._convert_time_strings(None) is None


def test_faculty_config_times_passthrough_time_range_objects() -> None:
    tr = TimeRange(start="09:00", end="12:00")
    f = FacultyConfig(
        name="DrTR",
        maximum_credits=6,
        minimum_credits=0,
        unique_course_limit=1,
        times={"MON": [tr]},
    )
    assert f.times["MON"][0] is tr


def test_faculty_config_mandatory_days_list_to_set() -> None:
    f = FacultyConfig(
        name="DrY",
        maximum_credits=12,
        minimum_credits=0,
        unique_course_limit=1,
        times={"MON": ["09:00-17:00"], "WED": ["09:00-17:00"]},
        mandatory_days={"MON", "WED"},
    )
    assert f.mandatory_days == {"MON", "WED"}


def test_faculty_config_mandatory_days_coerced_from_list_via_model_validate() -> None:
    """Config/JSON uses lists; validator coerces to set."""
    data = {
        "name": "DrY",
        "maximum_credits": 12,
        "minimum_credits": 0,
        "unique_course_limit": 1,
        "times": {"MON": ["09:00-17:00"], "WED": ["09:00-17:00"]},
        "mandatory_days": ["MON", "WED"],
    }
    f = FacultyConfig.model_validate(data)
    assert f.mandatory_days == {"MON", "WED"}


def test_faculty_config_mandatory_days_coerced_from_tuple_via_model_validate() -> None:
    """Config/JSON may use tuples; validator coerces to set."""
    data = {
        "name": "DrZ",
        "maximum_credits": 12,
        "minimum_credits": 0,
        "unique_course_limit": 1,
        "times": {"MON": ["09:00-17:00"]},
        "mandatory_days": ("MON",),
    }
    f = FacultyConfig.model_validate(data)
    assert f.mandatory_days == {"MON"}


def test_faculty_config_mandatory_days_already_set() -> None:
    f = FacultyConfig(
        name="DrSet",
        maximum_credits=12,
        minimum_credits=0,
        unique_course_limit=1,
        times={"MON": ["09:00-17:00"], "WED": ["09:00-17:00"]},
        mandatory_days={"MON"},
    )
    assert f.mandatory_days == {"MON"}


def test_faculty_config_min_gt_max() -> None:
    with pytest.raises(ValidationError, match="Minimum credits"):
        FacultyConfig(
            name="DrA",
            maximum_credits=3,
            minimum_credits=10,
            unique_course_limit=1,
            times={"MON": ["09:00-17:00"]},
        )


def test_faculty_config_maximum_days_lt_mandatory() -> None:
    with pytest.raises(ValidationError, match="maximum_days"):
        FacultyConfig(
            name="DrB",
            maximum_credits=12,
            minimum_credits=0,
            unique_course_limit=3,
            maximum_days=1,
            times={"MON": ["09:00-17:00"], "WED": ["09:00-17:00"]},
            mandatory_days={"MON", "WED"},
        )


def test_faculty_config_mandatory_not_in_times() -> None:
    with pytest.raises(ValidationError, match="Mandatory days"):
        FacultyConfig(
            name="DrC",
            maximum_credits=12,
            minimum_credits=0,
            unique_course_limit=1,
            times={"TUE": ["09:00-17:00"]},
            mandatory_days={"MON"},
        )


def test_faculty_preferences_optional() -> None:
    f = FacultyConfig(
        name="DrD",
        maximum_credits=6,
        minimum_credits=0,
        unique_course_limit=1,
        times={"MON": ["09:00-17:00"]},
        course_preferences={"CS101": 5},
        room_preferences={"RoomA": 10},
        lab_preferences={"Lab1": 0},
    )
    assert f.course_preferences["CS101"] == 5


# --- SchedulerConfig cross-refs & uniqueness ---


def _minimal_scheduler_kwargs():
    return {
        "rooms": ["R1"],
        "labs": ["L1"],
        "courses": [
            CourseConfig(
                course_id="CS101",
                credits=3,
                room=["R1"],
                lab=["L1"],
                conflicts=[],
                faculty=["F1"],
            )
        ],
        "faculty": [
            FacultyConfig(
                name="F1",
                maximum_credits=12,
                minimum_credits=3,
                unique_course_limit=1,
                times={"MON": ["09:00-17:00"]},
            )
        ],
    }


def test_scheduler_config_valid() -> None:
    SchedulerConfig(**_minimal_scheduler_kwargs())


def test_scheduler_config_duplicate_rooms() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["rooms"] = ["R1", "R1"]
    with pytest.raises(ValidationError, match="Duplicate room"):
        SchedulerConfig(**kw)


def test_scheduler_config_duplicate_labs() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["labs"] = ["L1", "L1"]
    with pytest.raises(ValidationError, match="Duplicate lab"):
        SchedulerConfig(**kw)


def test_scheduler_config_duplicate_faculty() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["faculty"] = [
        FacultyConfig(
            name="F1",
            maximum_credits=12,
            minimum_credits=0,
            unique_course_limit=1,
            times={"MON": ["09:00-17:00"]},
        ),
        FacultyConfig(
            name="F1",
            maximum_credits=6,
            minimum_credits=0,
            unique_course_limit=1,
            times={"TUE": ["09:00-17:00"]},
        ),
    ]
    with pytest.raises(ValidationError, match="Duplicate faculty"):
        SchedulerConfig(**kw)


def test_scheduler_config_invalid_course_room() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["courses"] = [
        CourseConfig(
            course_id="CS101",
            credits=3,
            room=["Nope"],
            lab=["L1"],
            conflicts=[],
            faculty=["F1"],
        )
    ]
    with pytest.raises(ValidationError, match="invalid rooms"):
        SchedulerConfig(**kw)


def test_scheduler_config_invalid_course_lab() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["courses"] = [
        CourseConfig(
            course_id="CS101",
            credits=3,
            room=["R1"],
            lab=["BadLab"],
            conflicts=[],
            faculty=["F1"],
        )
    ]
    with pytest.raises(ValidationError, match="invalid labs"):
        SchedulerConfig(**kw)


def test_scheduler_config_invalid_conflict_course() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["courses"] = [
        CourseConfig(
            course_id="CS101",
            credits=3,
            room=["R1"],
            lab=["L1"],
            conflicts=["MISSING"],
            faculty=["F1"],
        )
    ]
    with pytest.raises(ValidationError, match="invalid conflict"):
        SchedulerConfig(**kw)


def test_scheduler_config_self_conflict() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["courses"] = [
        CourseConfig(
            course_id="CS101",
            credits=3,
            room=["R1"],
            lab=["L1"],
            conflicts=["CS101"],
            faculty=["F1"],
        )
    ]
    with pytest.raises(ValidationError, match="cannot conflict with itself"):
        SchedulerConfig(**kw)


def test_scheduler_config_invalid_course_faculty() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["courses"] = [
        CourseConfig(
            course_id="CS101",
            credits=3,
            room=["R1"],
            lab=["L1"],
            conflicts=[],
            faculty=["Nobody"],
        )
    ]
    with pytest.raises(ValidationError, match="invalid faculty"):
        SchedulerConfig(**kw)


def test_scheduler_config_invalid_faculty_course_pref() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["faculty"] = [
        FacultyConfig(
            name="F1",
            maximum_credits=12,
            minimum_credits=0,
            unique_course_limit=1,
            times={"MON": ["09:00-17:00"]},
            course_preferences={"BAD": 5},
        )
    ]
    with pytest.raises(ValidationError, match="invalid courses in preferences"):
        SchedulerConfig(**kw)


def test_scheduler_config_invalid_faculty_room_pref() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["faculty"] = [
        FacultyConfig(
            name="F1",
            maximum_credits=12,
            minimum_credits=0,
            unique_course_limit=1,
            times={"MON": ["09:00-17:00"]},
            room_preferences={"X": 1},
        )
    ]
    with pytest.raises(ValidationError, match="invalid rooms in preferences"):
        SchedulerConfig(**kw)


def test_scheduler_config_invalid_faculty_lab_pref() -> None:
    kw = _minimal_scheduler_kwargs()
    kw["faculty"] = [
        FacultyConfig(
            name="F1",
            maximum_credits=12,
            minimum_credits=0,
            unique_course_limit=1,
            times={"MON": ["09:00-17:00"]},
            lab_preferences={"Y": 1},
        )
    ]
    with pytest.raises(ValidationError, match="invalid labs in preferences"):
        SchedulerConfig(**kw)


# --- CombinedConfig & OptimizerFlags ---


def test_optimizer_flags_enum_values() -> None:
    assert OptimizerFlags.FACULTY_COURSE.value == "faculty_course"
    assert OptimizerFlags.PACK_LABS.value == "pack_labs"
    assert len(OptimizerFlags) == 7


def test_combined_config_optimizer_flags_from_strings() -> None:
    base = json.loads((Path(__file__).parent / "fixtures" / "minimal_config.json").read_text(encoding="utf-8"))
    base["optimizer_flags"] = ["faculty_course", "pack_rooms"]
    c = CombinedConfig(**base)
    assert OptimizerFlags.FACULTY_COURSE in c.optimizer_flags


def test_combined_config_optimizer_flags_validator_non_list() -> None:
    assert CombinedConfig._convert_optimizer_flags("skip") == "skip"


def test_combined_config_defaults() -> None:
    data = json.loads((Path(__file__).parent / "fixtures" / "minimal_config.json").read_text(encoding="utf-8"))
    del data["limit"]
    del data["optimizer_flags"]
    c = CombinedConfig(**data)
    assert c.limit == 10
    assert c.optimizer_flags == []


def test_combined_config_extra_forbidden() -> None:
    data = json.loads((Path(__file__).parent / "fixtures" / "minimal_config.json").read_text(encoding="utf-8"))
    data["bogus"] = 1
    with pytest.raises(ValidationError):
        CombinedConfig(**data)


# --- StrictBaseModel.edit_mode ---


def test_strict_edit_mode_success() -> None:
    m = SampleStrict(name="a")
    with m.edit_mode() as w:
        w.name = "b"
        w.value = 2
    assert m.name == "b"
    assert m.value == 2


def test_strict_edit_mode_rollback() -> None:
    class StrictWithInt(StrictBaseModel):
        x: int

    m2 = StrictWithInt(x=1)
    with pytest.raises(ValidationError), m2.edit_mode() as w:
        w.x = "not_int"  # type: ignore[assignment]
    assert m2.x == 1


@pytest.mark.filterwarnings("ignore:.*Pydantic serializer warnings.*:UserWarning")
def test_strict_edit_mode_rollback_on_rebuild() -> None:
    """Invalid nested state passes assignment but fails full model rebuild (covers ``raise e`` path)."""

    class BrokenList(StrictBaseModel):
        items: list[int]

    m = BrokenList(items=[1])
    with pytest.raises(ValidationError), m.edit_mode() as w:
        w.items.append("bad")  # type: ignore[arg-type]
    assert m.items == [1]


# --- Type alias strictness (via models) ---


@pytest.mark.parametrize("t", ["00:00", "09:30", "22:00"])
def test_time_string_valid(t: str) -> None:
    TimeBlock(start=t, spacing=1, end="23:59")


@pytest.mark.parametrize("t", ["24:00", "9:30", "10:60", ""])
def test_time_string_invalid(t: str) -> None:
    with pytest.raises(ValidationError):
        TimeBlock(start=t, spacing=1, end="23:59")  # type: ignore[arg-type]


@pytest.mark.parametrize("p", [0, 5, 10])
def test_preference_valid(p: int) -> None:
    FacultyConfig(
        name="P",
        maximum_credits=1,
        minimum_credits=0,
        unique_course_limit=1,
        times={"MON": ["09:00-10:00"]},
        course_preferences={"CS101": p},
    )


@pytest.mark.parametrize("p", [-1, 11])
def test_preference_invalid(p: int) -> None:
    with pytest.raises(ValidationError):
        FacultyConfig(
            name="P",
            maximum_credits=1,
            minimum_credits=0,
            unique_course_limit=1,
            times={"MON": ["09:00-10:00"]},
            course_preferences={"CS101": p},  # type: ignore[arg-type]
        )


def test_load_config_from_file_valid(minimal_config_path: Path) -> None:
    c = load_config_from_file(CombinedConfig, str(minimal_config_path))
    assert isinstance(c, CombinedConfig)


def test_load_config_from_file_missing() -> None:
    with pytest.raises(FileNotFoundError):
        load_config_from_file(CombinedConfig, "/nonexistent/path/config.json")


def test_load_config_from_file_bad_json(tmp_path: Path) -> None:
    p = tmp_path / "bad.json"
    p.write_text("{ not json", encoding="utf-8")
    with pytest.raises(json.JSONDecodeError):
        load_config_from_file(CombinedConfig, str(p))
