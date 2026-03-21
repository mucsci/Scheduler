---
name: sched-ruff-ty-prek
description: >-
  Lints, formats, and type-checks Python code using Ruff, ty, and prek
  (pre-commit-compatible hooks). Use when fixing style errors, CI failures, or
  before submitting changes in this repository.
---

# Lint, format, typecheck

## Ruff

```bash
uv run ruff check .
uv run ruff format .
```

- **Line length**: 120 (`pyproject.toml` → `[tool.ruff]`).
- **Target**: Python 3.12.
- **Per-file ignores**: `B019` intentionally ignored on `scheduler.py` and `time_slot_generator.py` (cached methods for solver performance).

## ty

```bash
uv run ty check . --ignore unresolved-import
```

Matches the **prek** hook in `.pre-commit-config.yaml`.

## Full suite (matches CI)

```bash
uv run prek run --all-files
```

Install hooks locally after sync: `uv run prek install` (see CONTRIBUTING).

## Practices

- Run **ruff** after substantive edits; run **prek** before treating work as done.
- Do not “fix” `B019` in the two ignored files without maintainer intent.
