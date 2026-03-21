"""Smoke tests for package import and example configuration."""

from pathlib import Path

from scheduler import CombinedConfig, Scheduler, load_config_from_file


def test_package_exports_scheduler():
    assert Scheduler is not None


def test_load_example_json_config():
    root = Path(__file__).resolve().parent.parent
    example = root / "example.json"
    assert example.is_file()
    cfg = load_config_from_file(CombinedConfig, str(example))
    assert cfg.limit >= 1
