---
name: sched-output-writers
description: >-
  Implements or modifies JSON and CSV schedule output in the writers package.
  Use when changing serialization, export formats, or CLI --format behavior.
---

# Writers (JSON / CSV)

## Location

`src/scheduler/writers/` — **`json_writer.py`**, **`csv_writer.py`**, re-exported via **`writers/__init__.py`**.

## Guidelines

- Keep output **stable and documented** if users parse files in production.
- Thread changes through **CLI** (`src/scheduler/main.py`) and any **API** responses that reuse the same structures.
- Add or extend **tests** under `tests/` for new fields or format changes.

## Validation

```bash
uv run python -m scheduler.main --help
uv run pytest
```

Cross-skill references:

- [sched-cli-main](../sched-cli-main/SKILL.md)
- [sched-testing-pytest](../sched-testing-pytest/SKILL.md)
