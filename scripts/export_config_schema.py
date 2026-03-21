"""Write CombinedConfig JSON Schema for download from the docs site."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from scheduler.config import CombinedConfig  # noqa: E402


def main() -> None:
    assets = ROOT / "fern" / "docs" / "assets"
    assets.mkdir(parents=True, exist_ok=True)
    out = assets / "combined-config.schema.json"
    schema = CombinedConfig.model_json_schema()
    out.write_text(json.dumps(schema, indent=2), encoding="utf-8")
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
