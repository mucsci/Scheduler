---
name: sched-pr-conventional-commits
description: >-
  Prepares commits and pull requests using Conventional Commits and the
  contributing checklist for this repository. Use when drafting commit
  messages, summarizing changes, or before opening a PR.
---

# Commits and PRs

## Conventional Commits

Format:

```
<type>[optional scope]: <description>

[optional body]
```

Common **types**: `feat`, `fix`, `docs`, `style`, `refactor`, `test`, `chore`.

## Pre-PR checklist (from CONTRIBUTING)

- `uv run ruff check .` (and format if needed)
- `uv run ty check . --ignore unresolved-import`
- `uv run pytest`
- Docs and **generated Fern artifacts** updated when APIs or config schema change
- Breaking changes called out in the PR description

## PR description

- What changed and why
- Linked issues
- Note performance impact for solver-heavy work
