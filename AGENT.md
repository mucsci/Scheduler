# Agent guide — Course Constraint Scheduler

This file orients coding agents to the repository: how to build, test, and change the right places without guesswork.
If you are a human contributor, start with [README.md](README.md) and [CONTRIBUTING.md](CONTRIBUTING.md) for user-facing and process details.

## What this project is

Python **3.12+** package **`course-constraint-scheduler`**: a **Z3**-backed constraint solver for academic schedules, with **Pydantic** configuration, **CLI** (`scheduler`), **FastAPI** server (`scheduler-server`), and **Fern**-hosted docs.

- **Source**: `src/scheduler/` (import name `scheduler`)
- **Tests**: `tests/` (`pytest`, coverage gate in `pyproject.toml`)
- **User-facing docs site**: `fern/` (MDX + generated OpenAPI / schema / Python reference)

Human-oriented detail lives in [CONTRIBUTING.md](CONTRIBUTING.md) and [README.md](README.md).

## Commands agents should use

Prefer **`uv`** (lockfile: `uv.lock`). From repo root:

| Goal | Command |
|------|---------|
| Install deps + editable package | `uv sync` |
| Tests (with coverage gate) | `uv run pytest` |
| Lint | `uv run ruff check .` |
| Format | `uv run ruff format .` |
| Typecheck (matches hooks) | `uv run ty check . --ignore unresolved-import` |
| Full pre-commit suite (matches CI) | `uv run prek run --all-files` |
| Regenerate OpenAPI for Fern | `uv run python scripts/export_openapi.py` |
| Regenerate config JSON Schema asset | `uv run python scripts/export_config_schema.py` |
| Regenerate Python API MDX | `uv run python scripts/gen_python_api_mdx.py` |

CLI help: `uv run python -m scheduler.main --help`, `uv run python -m scheduler.server --help`.

## Layout (short)

```
src/scheduler/     # Package: config, scheduler (Z3), server, models, writers, CLI
tests/             # pytest; @pytest.mark.slow for heavy cases
scripts/           # export_openapi, export_config_schema, gen_python_api_mdx
fern/              # docs site; openapi.json and some assets are generated — do not hand-edit
skills/            # task playbooks (SKILL.md per subfolder) for assistants and contributors
.github/workflows/ # linting (prek + pytest), docs, publish
```

## Conventions that trip people up

1. **`Course` naming**: `scheduler.config` uses `Course` as a **course-id string** type in JSON config. `scheduler.models` defines a **`Course` class** (credits, meetings, etc.). `CourseInstance.course` is the model; use **`.course.course_id`** for the config-style id. (See README “Note on naming”.)
2. **Generated artifacts**: After changing **`src/scheduler/server.py`** or API-facing models, refresh **`fern/openapi.json`**. After **`CombinedConfig`** / config models change, refresh **`fern/docs/assets/combined-config.schema.json`**. After public **docstrings** change, refresh **`fern/docs/pages/python/reference.mdx`** — see CONTRIBUTING.
3. **Style**: **Ruff** is authoritative (`pyproject.toml`: line length **120**, `py312`). CONTRIBUTING matches this; when in doubt follow **`pyproject.toml`**.

## Skills

Reusable, task-specific instructions live under **`skills/`** — one directory per topic, each with a **`SKILL.md`** (YAML frontmatter + body). See **[skills/README.md](skills/README.md)** for an index. Read the skill that matches the task (docs, tests, API, solver, CI) before large changes.

**Cursor:** **`.cursor/skills`** is a symlink to **`skills/`** so the editor can load project skills from the canonical tree without duplicating files.

## PR / commits

Use **Conventional Commits** (`feat:`, `fix:`, `docs:`, …). Before opening a PR: tests green, `prek` (or equivalent ruff + ty) clean, docs/regenerated artifacts updated when APIs or config schema change.
