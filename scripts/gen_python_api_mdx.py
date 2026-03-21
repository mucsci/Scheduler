"""Generate fern/docs/pages/python/reference.mdx from scheduler package docstrings."""

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "fern" / "docs" / "pages" / "python" / "reference.mdx"

FRONTMATTER = """---
title: Python API reference
description: Auto-generated from docstrings for the scheduler package.
---

"""


def main() -> None:
    pydoc = shutil.which("pydoc-markdown")
    if not pydoc:
        print("pydoc-markdown not found on PATH; install dev dependencies (uv sync).", file=sys.stderr)
        sys.exit(1)
    proc = subprocess.run(
        [pydoc, "-p", "scheduler", "-I", "src"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(FRONTMATTER + proc.stdout, encoding="utf-8")
    print(f"Wrote {OUT}")


if __name__ == "__main__":
    main()
