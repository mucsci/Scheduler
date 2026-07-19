---
name: sched-testing-pytest
description: >-
  Writes and runs tests for the scheduler package with pytest and coverage.
  Use when adding tests, fixing failures, or running the test suite for this
  repository.
---

# Testing (pytest)

## Run

```bash
uv run pytest
```

- **Config**: `pyproject.toml` → `[tool.pytest.ini_options]`: `testpaths = ["tests"]`, `pythonpath = ["src"]`.
- **Coverage**: `--cov=scheduler` with **`--cov-fail-under=75`** — PRs must keep coverage above the gate unless maintainers agree to adjust it.

## Markers

- **`@pytest.mark.integration`**: Cross-component solver or HTTP boundary tests.
- **`@pytest.mark.characterization`**: Golden public compatibility outputs and signatures.
- **`@pytest.mark.slow`**: Heavy tests (e.g. full `example.json`, long solver paths).

## Conventions

- Shared fixtures: `tests/conftest.py`.
- Reusable config builders: `tests/scenario_builders.py`; golden outputs: `tests/fixtures/characterization/`.
- Prefer testing **public behavior** of `scheduler` modules; reach into internals only when necessary for Z3 or config edge cases.
- After behavior changes, update or add tests near related modules under `tests/`.
- Keep source-driven docs coverage in `tests/test_documentation_parity.py` aligned with new configuration fields,
  façade methods, routes, environment limits, and canonical examples.
