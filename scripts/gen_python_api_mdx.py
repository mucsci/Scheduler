"""Generate fern/docs/pages/python/reference.mdx from scheduler package docstrings."""

from __future__ import annotations

import re
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

EMPTY_USAGE_PATTERN = re.compile(r"\*\*Usage:\*\*\n\n(?=\*\*(?:Args|Returns|Raises):\*\*)")


def strip_empty_usage_sections(text: str) -> str:
    """Remove empty Usage headings emitted by pydoc-markdown.

    Some docstrings include a usage code block, but pydoc-markdown can reorder
    recognized sections (`Args`, `Returns`, `Raises`) ahead of that block,
    leaving a visually empty `**Usage:**` heading in rendered docs.
    """
    return EMPTY_USAGE_PATTERN.sub("", text)


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
    rendered = strip_empty_usage_sections(proc.stdout)
    OUT.write_text(FRONTMATTER + rendered, encoding="utf-8")
    print(f"Wrote {OUT}")


if __name__ == "__main__":
    main()
