"""Unit tests for JSON and CSV schedule writers."""

import json
from pathlib import Path

from scheduler import CombinedConfig, Scheduler
from scheduler.writers import CSVWriter, JSONWriter


def _schedule(config: CombinedConfig):
    return next(Scheduler(config).get_models())


def test_csv_writer_buffers_file_schedules_and_separates_them(
    minimal_combined_config: CombinedConfig,
    tmp_path: Path,
) -> None:
    schedule = _schedule(minimal_combined_config)
    path = tmp_path / "schedules.csv"

    with CSVWriter(str(path)) as writer:
        assert writer.filename == str(path)
        writer.add_schedule(schedule)
        writer.add_schedule(schedule)

    serialized = "\n".join(instance.as_csv() for instance in schedule)
    assert path.read_text(encoding="utf-8") == f"{serialized}\n\n{serialized}"


def test_csv_writer_prints_immediately_without_a_file(
    minimal_combined_config: CombinedConfig,
    capsys,
) -> None:
    schedule = _schedule(minimal_combined_config)

    with CSVWriter() as writer:
        writer.add_schedule(schedule)

    assert capsys.readouterr().out.rstrip("\n") == "\n".join(instance.as_csv() for instance in schedule)


def test_json_writer_emits_file_array_and_stdout_schedule(
    minimal_combined_config: CombinedConfig,
    tmp_path: Path,
    capsys,
) -> None:
    schedule = _schedule(minimal_combined_config)
    expected = [instance.model_dump(by_alias=True, exclude_none=True) for instance in schedule]
    path = tmp_path / "schedules.json"

    with JSONWriter(str(path)) as writer:
        writer.add_schedule(schedule)
    assert json.loads(path.read_text(encoding="utf-8")) == [expected]

    with JSONWriter() as writer:
        writer.add_schedule(schedule)
    assert json.loads(capsys.readouterr().out) == expected
