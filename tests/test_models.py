"""Unit tests for domain models under ``scheduler.models``."""

import pytest
from pydantic import ValidationError

from scheduler.models import Course, CourseInstance, Day, Duration, TimeInstance, TimePoint, TimeSlot


def test_day_str_repr() -> None:
    assert str(Day.MON) == "MON"
    assert repr(Day.FRI) == "FRI"


def test_duration_ordering_and_abs() -> None:
    a = Duration(duration=30)
    b = Duration(duration=60)
    assert a < b
    assert a <= b
    assert b > a
    assert abs(Duration(duration=-5)).value == 5


def test_time_point_make_from_and_arithmetic() -> None:
    t = TimePoint.make_from(10, 30)
    assert t.hour == 10
    assert t.minute == 30
    d = Duration(duration=45)
    assert (t + d).value == t.value + 45
    assert (t + d - t).value == 45


def test_time_point_ordering() -> None:
    t1 = TimePoint.make_from(9, 0)
    t2 = TimePoint.make_from(10, 0)
    assert t1 < t2
    assert t1 != t2


def test_time_instance_stop_and_str() -> None:
    ti = TimeInstance(
        day=Day.MON,
        start=TimePoint.make_from(9, 0),
        duration=Duration(duration=60),
    )
    assert ti.stop.value == ti.start.value + 60
    assert "MON" in str(ti)
    assert "09:00" in str(ti)


def test_time_slot_lab_time_and_has_lab() -> None:
    t0 = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=50))
    t1 = TimeInstance(day=Day.MON, start=TimePoint.make_from(10, 0), duration=Duration(duration=50))
    slot = TimeSlot(times=[t0, t1], lab_index=1, max_time_gap=Duration(duration=30))
    assert slot.has_lab()
    assert slot.lab_time() == t1


def test_time_slot_no_lab() -> None:
    t0 = TimeInstance(day=Day.TUE, start=TimePoint.make_from(8, 0), duration=Duration(duration=75))
    slot = TimeSlot(times=[t0], lab_index=None)
    assert not slot.has_lab()
    assert slot.lab_time() is None


def test_time_slot_overlaps_same_day() -> None:
    a = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=90))
    b = TimeInstance(day=Day.MON, start=TimePoint.make_from(10, 0), duration=Duration(duration=60))
    s1 = TimeSlot(times=[a])
    s2 = TimeSlot(times=[b])
    assert s1.overlaps(s2)


def test_time_slot_no_overlap_different_days_non_overlapping_clock() -> None:
    a = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=60))
    b = TimeInstance(day=Day.TUE, start=TimePoint.make_from(9, 0), duration=Duration(duration=60))
    s1 = TimeSlot(times=[a])
    s2 = TimeSlot(times=[b])
    assert not s1.overlaps(s2)


def test_time_slot_lab_overlaps() -> None:
    lab_a = TimeInstance(day=Day.MON, start=TimePoint.make_from(14, 0), duration=Duration(duration=60))
    lec_a = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=50))
    lab_b = TimeInstance(day=Day.MON, start=TimePoint.make_from(14, 30), duration=Duration(duration=60))
    lec_b = TimeInstance(day=Day.MON, start=TimePoint.make_from(10, 0), duration=Duration(duration=50))
    s1 = TimeSlot(times=[lec_a, lab_a], lab_index=1)
    s2 = TimeSlot(times=[lec_b, lab_b], lab_index=1)
    assert s1.lab_overlaps(s2)


def test_time_slot_lab_overlaps_none() -> None:
    t = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=50))
    s1 = TimeSlot(times=[t], lab_index=None)
    s2 = TimeSlot(times=[t], lab_index=None)
    assert not s1.lab_overlaps(s2)


def test_time_slot_lecture_next_to() -> None:
    a = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=50))
    b = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 55), duration=Duration(duration=50))
    s1 = TimeSlot(times=[a], max_time_gap=Duration(duration=30))
    s2 = TimeSlot(times=[b], max_time_gap=Duration(duration=30))
    assert s1.lecture_next_to(s2)


def test_time_slot_lab_next_to_different_days() -> None:
    gap = Duration(duration=30)
    lab1 = TimeInstance(day=Day.MON, start=TimePoint.make_from(16, 0), duration=Duration(duration=60))
    lec1 = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=50))
    lab2 = TimeInstance(day=Day.WED, start=TimePoint.make_from(16, 0), duration=Duration(duration=60))
    lec2 = TimeInstance(day=Day.WED, start=TimePoint.make_from(9, 0), duration=Duration(duration=50))
    s1 = TimeSlot(times=[lec1, lab1], lab_index=1, max_time_gap=gap)
    s2 = TimeSlot(times=[lec2, lab2], lab_index=1, max_time_gap=gap)
    assert s1.lab_next_to(s2)


def test_time_slot_in_time_ranges() -> None:
    t = TimeInstance(day=Day.MON, start=TimePoint.make_from(10, 0), duration=Duration(duration=60))
    slot = TimeSlot(times=[t])
    window = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=180))
    assert slot.in_time_ranges([window])
    outside = TimeInstance(day=Day.MON, start=TimePoint.make_from(20, 0), duration=Duration(duration=60))
    assert not slot.in_time_ranges([outside])


def test_course_str() -> None:
    c = Course(
        course_id="CS101",
        section=2,
        credits=3,
        labs=["L1"],
        rooms=["R1"],
        conflicts=[],
        faculties=["F1"],
    )
    assert str(c) == "CS101.02"


def test_course_instance_as_csv_and_computed() -> None:
    c = Course(
        course_id="X",
        section=1,
        credits=3,
        labs=["L1"],
        rooms=["R1"],
        conflicts=[],
        faculties=["F1"],
    )
    t = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=50))
    slot = TimeSlot(times=[t], lab_index=None)
    ci = CourseInstance(course=c, time=slot, faculty="F1", room="R1", lab=None)
    row = ci.as_csv()
    assert "X.01" in row
    assert ci.course_str == "X.01"
    assert ci.times == slot.times
    assert ci.lab_index is None


def test_course_instance_lab_index_when_lab_set() -> None:
    c = Course(
        course_id="Y",
        section=1,
        credits=4,
        labs=["L1"],
        rooms=["R1"],
        conflicts=[],
        faculties=["F1"],
    )
    lab = TimeInstance(day=Day.MON, start=TimePoint.make_from(14, 0), duration=Duration(duration=60))
    lec = TimeInstance(day=Day.MON, start=TimePoint.make_from(9, 0), duration=Duration(duration=50))
    slot = TimeSlot(times=[lec, lab], lab_index=1)
    ci = CourseInstance(course=c, time=slot, faculty="F1", room="R1", lab="L1")
    assert ci.lab_index == 1


def test_duration_serializer_roundtrip() -> None:
    d = Duration(duration=90)
    assert d.model_dump() == 90


def test_time_point_serializer_roundtrip() -> None:
    t = TimePoint.make_from(12, 15)
    assert t.model_dump() == 12 * 60 + 15


def test_models_reject_extra_fields() -> None:
    with pytest.raises(ValidationError):
        Duration(duration=1, extra=2)  # type: ignore[call-arg]
