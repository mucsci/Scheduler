---
name: sched-maintain-scripts
description: >-
  Maintains or extends repository scripts under scripts/ for OpenAPI export,
  JSON Schema export, and Python API MDX generation. Use when changing export
  pipelines or adding codegen steps for documentation.
---

# scripts/

| Script | Role |
|--------|------|
| `export_openapi.py` | Refresh **`fern/openapi.json`** from the FastAPI app |
| `export_config_schema.py` | Refresh **`fern/docs/assets/combined-config.schema.json`** |
| `gen_python_api_mdx.py` | Refresh **`fern/docs/pages/python/reference.mdx`** from docstrings |

Run with:

```bash
uv run python scripts/<script>.py
```

When editing these scripts:

- Keep output paths stable unless **`fern/docs.yml`** / publishers are updated too.
- Prefer deterministic ordering in generated JSON/MDX when possible to reduce noisy diffs.
