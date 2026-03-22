---
name: sched-uv-workflow
description: >-
  Develops and runs the course-constraint-scheduler package with uv. Use when
  installing dependencies, syncing the lockfile, running CLI/server modules, or
  setting up a local environment for this repository.
---

# UV workflow (this repo)

## Defaults

- **Python**: 3.12+ (`requires-python` in `pyproject.toml`).
- **Package**: `course-constraint-scheduler`; code under `src/scheduler/`, import **`scheduler`**.
- **Lockfile**: `uv.lock` — prefer `uv sync --locked` in CI-like checks.

## Setup

```bash
uv sync
```

Dev tools (ruff, pytest, ty, prek, …) are in the **`dev`** dependency group; `tool.uv.default-groups` includes `dev`, so plain `uv sync` is enough for normal work.

## Run entrypoints

```bash
uv run python -m scheduler.main --help
uv run python -m scheduler.server --help
uv run pytest
uv run prek run --all-files
```

Use `uv run <command>` so the project venv and paths stay consistent.

For CI parity and GitHub Actions behavior, see [sched-github-ci](../sched-github-ci/SKILL.md).
