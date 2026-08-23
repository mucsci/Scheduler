"""Write CombinedConfig JSON Schema for download from the docs site."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

from pydantic import BaseModel

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from scheduler import config as config_module  # noqa: E402
from scheduler.config import CombinedConfig  # noqa: E402


def _python_type_name(annotation: object) -> str:
    """Return a concise, source-like representation of a Python annotation."""
    if isinstance(annotation, type):
        return annotation.__name__

    type_name = str(annotation).replace("scheduler.config.", "")
    return type_name.replace("typing.", "")


def _append_python_type(description: str, annotation: object) -> str:
    """Add the field's Python type to a human-readable schema description."""
    return f"{description}\n\nPython type: `{_python_type_name(annotation)}`."


def add_python_type_descriptions(
    schema: dict[str, Any], *, definitions_key: str = "$defs", strip_schema_suffix: bool = False
) -> None:
    """Annotate generated schema descriptions with their source Python types.

    JSON Schema distinguishes only JSON primitives and containers. Configuration
    users also benefit from the more precise Python annotations: for example,
    a JSON array can represent ``list[Room]`` or ``set[str]``. The metadata is
    kept in descriptions so the schema remains valid standard JSON Schema.
    """
    definitions = schema.get(definitions_key, {})

    for definition_name, definition in definitions.items():
        source_name = definition_name.split("-", maxsplit=1)[0] if strip_schema_suffix else definition_name
        source_type = getattr(config_module, source_name, None)
        if source_type is None or not isinstance(definition, dict):
            continue

        description = definition.get("description")
        if isinstance(description, str):
            definition["description"] = _append_python_type(description, source_type)

        if not isinstance(source_type, type) or not issubclass(source_type, BaseModel):
            continue

        properties = definition.get("properties", {})
        for field_name, field in source_type.model_fields.items():
            property_schema = properties.get(field_name)
            if not isinstance(property_schema, dict):
                continue
            description = property_schema.get("description")
            if isinstance(description, str):
                property_schema["description"] = _append_python_type(description, field.annotation)


def main() -> None:
    assets = ROOT / "fern" / "docs" / "assets"
    assets.mkdir(parents=True, exist_ok=True)
    out = assets / "combined-config.schema.json"
    schema = CombinedConfig.model_json_schema()
    add_python_type_descriptions(schema)
    out.write_text(json.dumps(schema, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
