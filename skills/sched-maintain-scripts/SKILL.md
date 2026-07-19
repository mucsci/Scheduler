---
name: sched-maintain-scripts
description: >-
  Maintains or extends repository scripts under scripts/ for OpenAPI and JSON
  Schema export. Use when changing export pipelines or adding codegen steps for
  documentation.
---

# scripts/

| Script | Role |
|--------|------|
| `export_openapi.py` | Refresh **`fern/openapi.json`** from the FastAPI app |
| `export_config_schema.py` | Refresh **`fern/docs/assets/combined-config.schema.json`** |

Python library reference generation is owned by Fern itself:

```bash
fern docs md generate --local --library scheduler-python
```

Run with:

```bash
uv run python scripts/<script>.py
```

When editing these scripts:

- Keep output paths stable unless **`fern/docs.yml`** / publishers are updated too.
- Prefer deterministic ordering in generated JSON/MDX when possible to reduce noisy diffs.

Cross-skill references:

- [sched-fern-openapi-docs](../sched-fern-openapi-docs/SKILL.md) for authoring rules and local Fern preview
- [sched-fastapi-server](../sched-fastapi-server/SKILL.md) when changes originate from route/model updates
