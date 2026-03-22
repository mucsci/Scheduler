---
name: sched-fastapi-server
description: >-
  Changes or reviews the FastAPI REST server, routes, and HTTP behavior for the
  scheduler. Use when editing server.py, async job flow, or API contracts.
---

# FastAPI server

## Entry

- **Module**: `src/scheduler/server.py`
- **Console script**: `scheduler-server` → `scheduler.server:main`

Run locally with `uv run python -m scheduler.server` (plus host/port flags from `--help`).

## Contracts

- Keep request/response models consistent with **OpenAPI** consumers.
- After **route**, **model**, or **status code** changes, regenerate **`fern/openapi.json`**:

```bash
uv run python scripts/export_openapi.py
```

## Typical workflow

1. Edit route/model behavior in **`src/scheduler/server.py`**.
2. Regenerate OpenAPI with `uv run python scripts/export_openapi.py`.
3. Run validation (`uv run pytest` and/or focused API tests).
4. Update Fern narrative docs in `fern/docs/pages/` when user-facing behavior changed.

## Integration tests

- Use **`httpx`** (dev dependency) for async client tests where appropriate; see existing patterns in `tests/`.

## Documentation

- User-facing API narrative lives under **`fern/docs/pages/`**; machine-readable spec is **`fern/openapi.json`**.

Cross-skill references:

- [sched-fern-openapi-docs](../sched-fern-openapi-docs/SKILL.md)
- [sched-maintain-scripts](../sched-maintain-scripts/SKILL.md)
- [sched-testing-pytest](../sched-testing-pytest/SKILL.md)
