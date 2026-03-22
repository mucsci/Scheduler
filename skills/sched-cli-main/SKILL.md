---
name: sched-cli-main
description: >-
  Changes the scheduler command-line interface in main.py (Click), arguments,
  output paths, and format options. Use when adding CLI flags or adjusting how
  schedules are printed or written to disk.
---

# CLI (`scheduler`)

## Entry

- **`src/scheduler/main.py`** → **`scheduler`** console script (`scheduler.main:main`).

## Typical flow

- Load config (Pydantic / file helpers from **`config`**).
- Construct **`Scheduler`**, iterate models, write via **`writers`** (`json` / `csv`).

## Checklist

- Keep **`--help`** accurate; Click option names stable when possible.
- If default output or formats change, update **README**, **Fern** pages, and **tests**.
- Large or slow paths: consider documenting use of **`pytest` markers** for integration tests.

## Validation

```bash
uv run python -m scheduler.main --help
uv run pytest
```

Cross-skill references:

- [sched-output-writers](../sched-output-writers/SKILL.md) for JSON/CSV behavior
- [sched-testing-pytest](../sched-testing-pytest/SKILL.md) for test strategy
