"""Configuration loading and non-throwing validation helpers."""

import hashlib
import json
import os
from collections.abc import Mapping
from typing import Any

from pydantic import BaseModel, ValidationError

from .config import CombinedConfig
from .contracts import ConfigurationDiagnostic, ConfigurationValidationResult


def load_config_from_file[T: BaseModel](
    config_cls: type[T],
    filename: str | os.PathLike[str],
) -> T:
    """Load and validate one JSON configuration file."""
    with open(filename, encoding="utf-8") as config_file:
        data = json.load(config_file)
    return config_cls(**data)


def _json_pointer(location: tuple[object, ...]) -> str:
    if not location:
        return ""
    return "/" + "/".join(str(part).replace("~", "~0").replace("/", "~1") for part in location)


def validate_combined_config_data(payload: Mapping[str, Any]) -> ConfigurationValidationResult:
    """Validate raw configuration data without raising a Pydantic exception."""
    try:
        config = CombinedConfig.model_validate(payload)
    except ValidationError as exc:
        diagnostics: list[ConfigurationDiagnostic] = []
        for error in exc.errors(include_url=False):
            invalid_value = error.get("input")
            value = repr(invalid_value) if isinstance(invalid_value, str | int | float | bool) else None
            diagnostics.append(
                ConfigurationDiagnostic(
                    code="SCHED.CONFIG." + str(error["type"]).upper().replace("_", "."),
                    path=_json_pointer(tuple(error["loc"])),
                    message=str(error["msg"]),
                    value=value,
                )
            )
        return ConfigurationValidationResult(is_valid=False, diagnostics=tuple(diagnostics))

    canonical = json.dumps(config.model_dump(mode="json"), sort_keys=True, separators=(",", ":"))
    return ConfigurationValidationResult(
        is_valid=True,
        configuration_fingerprint=hashlib.sha256(canonical.encode()).hexdigest(),
    )
