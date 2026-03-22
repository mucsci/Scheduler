# Configuration guide (moved)

The configuration documentation now lives on the **Fern** docs site:

**[https://mucsci-scheduler.docs.buildwithfern.com](https://mucsci-scheduler.docs.buildwithfern.com)** — start under **Configuration → Overview and schema**.

Source for those pages is in the repository under [`fern/docs/pages/configuration/`](../fern/docs/pages/configuration/).

A machine-readable JSON Schema for the full config is at [`fern/docs/assets/combined-config.schema.json`](../fern/docs/assets/combined-config.schema.json).

If you are working from a fresh checkout and the schema file is missing, regenerate it with:

```bash
uv run python scripts/export_config_schema.py
```
