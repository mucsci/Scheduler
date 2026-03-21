---
name: sched-github-ci
description: >-
  Interprets or updates GitHub Actions workflows for linting, tests, docs, and
  publishing. Use when CI fails, when adding checks, or when aligning local
  commands with automation.
---

# GitHub Actions

## Workflows

- **`.github/workflows/linting.yml`**: `uv sync --locked --group dev`, then `uv run prek run --all-files` and `uv run pytest`.
- **`.github/workflows/docs.yml`**: Fern docs build/deploy (see file for triggers and secrets).
- **`.github/workflows/publish.yml`**: Package publish pipeline.

## Aligning locally

If CI fails, reproduce with the same **locked** install:

```bash
uv sync --locked --group dev
uv run prek run --all-files
uv run pytest
```

## Dependabot

- **`.github/dependabot.yml`** schedules dependency updates; bump workflows if action major versions change.
