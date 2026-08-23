"""Write FastAPI OpenAPI JSON to fern/openapi.json for Fern API reference."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from export_config_schema import add_python_type_descriptions  # noqa: E402

from scheduler.server import app  # noqa: E402


def main() -> None:
    out = ROOT / "fern" / "openapi.json"
    schema = app.openapi()
    add_python_type_descriptions(schema["components"], definitions_key="schemas", strip_schema_suffix=True)
    out.write_text(json.dumps(schema, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
