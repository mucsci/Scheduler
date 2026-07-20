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
    """Load one JSON file and validate it as the requested Pydantic model.

    Args:
        config_cls: Pydantic model class used to validate decoded JSON data.
        filename: Filesystem path to a UTF-8 JSON document.

    Returns:
        A validated instance of ``config_cls``.

    Raises:
        OSError: If the file cannot be opened or read.
        json.JSONDecodeError: If the document is not valid JSON.
        pydantic.ValidationError: If decoded data does not satisfy ``config_cls``.

    Behavior:
        Reads the complete document as UTF-8, decodes exactly one JSON value, and
        delegates all schema and cross-field validation to the supplied model.
    """
    with open(filename, encoding="utf-8") as config_file:
        data = json.load(config_file)
    return config_cls.model_validate(data)


def _json_pointer(location: tuple[object, ...]) -> str:
    if not location:
        return ""
    return "/" + "/".join(str(part).replace("~", "~0").replace("/", "~1") for part in location)


def _canonicalize_configuration_value(value):
    """Convert unordered configuration containers into stable JSON data."""
    if isinstance(value, dict):
        return {str(key): _canonicalize_configuration_value(item) for key, item in value.items()}
    if isinstance(value, set | frozenset):
        return sorted((_canonicalize_configuration_value(item) for item in value), key=str)
    if isinstance(value, list | tuple):
        return [_canonicalize_configuration_value(item) for item in value]
    return value


def _configuration_fingerprint(config: CombinedConfig) -> str:
    canonical_data = _canonicalize_configuration_value(config.model_dump(mode="python"))
    canonical = json.dumps(canonical_data, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode()).hexdigest()


def validate_combined_config_data(payload: Mapping[str, Any]) -> ConfigurationValidationResult:
    """Validate untrusted combined configuration data into a structured result.

    Args:
        payload: Raw mapping expected to match :class:`CombinedConfig`.

    Returns:
        A result containing ordered path-aware errors, or a stable fingerprint
        when validation succeeds.

    Raises:
        TypeError: If successful validated data cannot be canonically serialized.

    Behavior:
        Converts Pydantic validation failures into stable diagnostic codes and
        JSON Pointers without raising them. Valid input is canonicalized and hashed;
        rejected scalar values are represented without retaining complex payloads.
    """
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

    return ConfigurationValidationResult(
        is_valid=True,
        configuration_fingerprint=_configuration_fingerprint(config),
    )
