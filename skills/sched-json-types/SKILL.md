---
name: sched-json-types
description: >-
  Maintains TypedDict and JSON-shaped type definitions for API and config
  payloads. Use when editing json_types.py or aligning wire formats with
  Pydantic models and OpenAPI.
---

# JSON types (`json_types.py`)

## Edit locations

- **`src/scheduler/json_types.py`** (primary)
- Related shape sources: **`src/scheduler/config.py`**, **`src/scheduler/server.py`**

## Role

- Supplemental **TypedDict** descriptions for JSON-shaped values used by callers and writers.
- Runtime configuration and REST validation remain authoritative in Pydantic models from **`config.py`** and
  **`server.py`**; do not treat duplicated TypedDicts as runtime schema.

## Practices

- Prefer **one source of truth**: when possible, derive or mirror shapes from Pydantic rather than duplicating divergent definitions.
- After changes that affect the HTTP API surface, regenerate **`fern/openapi.json`**.
- Run **ty** and **tests** — JSON typing mistakes often show up as runtime validation errors in tests.

## Validation

```bash
uv run ty check . --ignore unresolved-import
uv run pytest
uv run python scripts/export_openapi.py  # if API request/response shapes changed
```

Cross-skill references:

- [sched-ruff-ty-prek](../sched-ruff-ty-prek/SKILL.md)
- [sched-fastapi-server](../sched-fastapi-server/SKILL.md)
- [sched-fern-openapi-docs](../sched-fern-openapi-docs/SKILL.md)
