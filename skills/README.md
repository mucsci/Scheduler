# Agent skills

This directory holds **task-focused playbooks** for anyone (or any automated assistant) working on the repository. Each subfolder is one skill; open **`SKILL.md`** inside it for the full instructions. Files use YAML frontmatter (`name`, `description`) so tools that ingest skills can discover them consistently.

| Skill | Use when |
|-------|----------|
| [sched-cli-main](sched-cli-main/SKILL.md) | CLI (`main.py`, Click, `--format`, output) |
| [sched-domain-z3-config](sched-domain-z3-config/SKILL.md) | Solver, Z3, config vs models, time slots |
| [sched-fastapi-server](sched-fastapi-server/SKILL.md) | REST API, `server.py`, OpenAPI |
| [sched-fern-openapi-docs](sched-fern-openapi-docs/SKILL.md) | Fern site, regenerating openapi/schema/MDX |
| [sched-github-ci](sched-github-ci/SKILL.md) | GitHub Actions, CI failures |
| [sched-json-types](sched-json-types/SKILL.md) | `json_types.py`, wire shapes |
| [sched-maintain-scripts](sched-maintain-scripts/SKILL.md) | `scripts/*.py` exporters |
| [sched-output-writers](sched-output-writers/SKILL.md) | JSON/CSV writers |
| [sched-pr-conventional-commits](sched-pr-conventional-commits/SKILL.md) | Commits, PR checklist |
| [sched-ruff-ty-prek](sched-ruff-ty-prek/SKILL.md) | Lint, format, typecheck, prek |
| [sched-testing-pytest](sched-testing-pytest/SKILL.md) | pytest, coverage, markers |
| [sched-uv-workflow](sched-uv-workflow/SKILL.md) | `uv sync`, local env, `uv run` |

Orientation for the whole repo: **[AGENT.md](../AGENT.md)**.
