"""Small, reusable configuration and output builders for scheduler tests."""

import json
from dataclasses import asdict, is_dataclass
from pathlib import Path
from typing import Any

from scheduler import CombinedConfig

FIXTURES = Path(__file__).resolve().parent / "fixtures"


def minimal_config_data() -> dict[str, Any]:
    return json.loads((FIXTURES / "minimal_config.json").read_text(encoding="utf-8"))


def two_course_config_data(*, same_course: bool = False) -> dict[str, Any]:
    data = minimal_config_data()
    second_id = "CS101" if same_course else "CS102"
    data["config"]["courses"].append(
        {
            "course_id": second_id,
            "credits": 4,
            "room": ["R1"],
            "lab": ["L1"],
            "conflicts": [],
            "faculty": ["F1"],
        }
    )
    data["config"]["faculty"][0].update(
        {
            "maximum_credits": 8,
            "minimum_credits": 0,
            "unique_course_limit": 2,
        }
    )
    data["limit"] = 2
    return data


def no_lab_config_data() -> dict[str, Any]:
    data = minimal_config_data()
    data["config"]["labs"] = []
    data["config"]["courses"][0]["lab"] = []
    data["time_slot_config"]["classes"][0]["meetings"][0]["lab"] = False
    return data


def config_from(data: dict[str, Any]) -> CombinedConfig:
    return CombinedConfig.model_validate(data)


def stable_payload(value: Any) -> Any:
    """Convert contracts to stable JSON data and normalize runtime-only fields."""
    payload = asdict(value) if is_dataclass(value) else value
    payload = json.loads(json.dumps(payload, sort_keys=True))
    if isinstance(payload, dict) and "elapsed_ms" in payload:
        payload["elapsed_ms"] = 0
    return payload


def schedule_signature(schedule: list[Any]) -> list[str]:
    return [instance.as_csv() for instance in schedule]
