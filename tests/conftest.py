"""Shared pytest fixtures."""

import json
from pathlib import Path

import pytest

from scheduler import CombinedConfig, load_config_from_file

FIXTURES = Path(__file__).resolve().parent / "fixtures"
REPO_ROOT = Path(__file__).resolve().parent.parent


@pytest.fixture
def minimal_config_path() -> Path:
    return FIXTURES / "minimal_config.json"


@pytest.fixture
def minimal_combined_config(minimal_config_path: Path) -> CombinedConfig:
    return load_config_from_file(CombinedConfig, str(minimal_config_path))


@pytest.fixture
def example_json_path() -> Path:
    return REPO_ROOT / "example.json"


def _two_course_template() -> dict:
    base = json.loads((FIXTURES / "minimal_config.json").read_text(encoding="utf-8"))
    base["config"]["courses"] = [
        {
            "course_id": "CS101",
            "credits": 4,
            "room": ["R1"],
            "lab": ["L1"],
            "conflicts": ["CS102"],
            "faculty": ["F1"],
        },
        {
            "course_id": "CS102",
            "credits": 4,
            "room": ["R1"],
            "lab": ["L1"],
            "conflicts": ["CS101"],
            "faculty": ["F1"],
        },
    ]
    base["config"]["faculty"] = [
        {
            "name": "F1",
            "maximum_credits": 12,
            "minimum_credits": 8,
            "unique_course_limit": 2,
            "times": {
                "MON": ["08:00-20:00"],
                "TUE": ["08:00-20:00"],
                "WED": ["08:00-20:00"],
                "THU": ["08:00-20:00"],
                "FRI": ["08:00-20:00"],
            },
        }
    ]
    base["limit"] = 2
    return base


@pytest.fixture
def two_course_combined_config() -> CombinedConfig:
    return CombinedConfig(**_two_course_template())


@pytest.fixture
def unsatisfiable_combined_config() -> CombinedConfig:
    """Two 4-credit courses both assigned only to F1; F1 max credits 4."""
    data = json.loads((FIXTURES / "minimal_config.json").read_text(encoding="utf-8"))
    data["config"]["courses"] = [
        {
            "course_id": "CS101",
            "credits": 4,
            "room": ["R1"],
            "lab": ["L1"],
            "conflicts": [],
            "faculty": ["F1"],
        },
        {
            "course_id": "CS102",
            "credits": 4,
            "room": ["R1"],
            "lab": ["L1"],
            "conflicts": [],
            "faculty": ["F1"],
        },
    ]
    data["config"]["faculty"] = [
        {
            "name": "F1",
            "maximum_credits": 4,
            "minimum_credits": 0,
            "unique_course_limit": 2,
            "times": {
                "MON": ["08:00-20:00"],
                "TUE": ["08:00-20:00"],
                "WED": ["08:00-20:00"],
                "THU": ["08:00-20:00"],
                "FRI": ["08:00-20:00"],
            },
        }
    ]
    data["limit"] = 3
    return CombinedConfig(**data)
