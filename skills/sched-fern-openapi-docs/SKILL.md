---
name: sched-fern-openapi-docs
description: >-
  Maintains Fern documentation, OpenAPI, JSON Schema assets, and Python API
  reference MDX for this project. Use when changing FastAPI routes, public
  docstrings, Pydantic config models, or user-facing docs under fern/docs.
---

# Fern docs and generated files

## Do not hand-edit

- **`fern/openapi.json`** — generated from FastAPI.
- **`fern/docs/assets/combined-config.schema.json`** — generated from config models.
- **`fern/docs/pages/python/reference.mdx`** — generated from docstrings (see script).

## Regenerate after changes

| Change | Command |
|--------|---------|
| `server.py`, API models, routes | `uv run python scripts/export_openapi.py` |
| `CombinedConfig` / config schema | `uv run python scripts/export_config_schema.py` |
| Public API docstrings | `uv run python scripts/gen_python_api_mdx.py` |

## Authoring

- **Guides / prose**: `fern/docs/pages/` (MDX), navigation in `fern/docs.yml`.
- **Site config**: `fern/fern.config.json`, `fern/generators.yml`.

## Local preview

After regenerating as needed: install Fern CLI (`npm install -g fern-api`), then `fern docs dev` from the `fern/` directory (see CONTRIBUTING).

## CI

Docs deployment is in `.github/workflows/docs.yml` — keep generated artifacts committed when CI or publishers expect them.
