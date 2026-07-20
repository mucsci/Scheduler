---
name: sched-domain-z3-config
description: >-
  Implements or debugs scheduling logic, Z3 constraints, and JSON configuration
  for the course constraint scheduler. Use when working in normalized problems,
  solver/diagnostic/audit engines, config models, time slots, or solver behavior.
---

# Domain: Z3, config, models

## Core files

- **`src/scheduler/problem.py`**: Z3-free normalized policies, time domains, provenance paths, and cached queries.
- **`src/scheduler/solver.py`**: Z3 context, symbols, constraints, objectives, decoding, and enumeration.
- **`src/scheduler/diagnostics.py`**: Preflight facts, cores, provenance, suggestions, and verified repairs.
- **`src/scheduler/audit.py`**: Independent hard-rule validation and objective scoring.
- **`src/scheduler/scheduler.py`**: Stable public façade and compatibility re-exports; keep it orchestration-only.
- **`src/scheduler/config.py`**: Pydantic models, validation, loading (`CombinedConfig`, etc.).
- **`src/scheduler/time_slot_generator.py`**: Time slot generation utilities.
- **`src/scheduler/models/`**: Runtime schedule representations (`CourseInstance`, `TimeSlot`, ...).

## Naming trap: `Course`

- **`scheduler.config`**: `Course` (and related types) align with **JSON config** — often **course id strings** and config-shaped structures.
- **`scheduler.models`**: **`Course`** is a **class** (credits, meetings, …). Instances in schedules use **`CourseInstance`**; the config id is **`course_instance.course.course_id`**.

When touching types or docs, preserve this distinction to avoid breaking configs or the public API.

## Config workflow

- Representative sample: **`example.json`**; smaller fixtures under **`tests/fixtures/`**.
- Global rooms and labs are `RoomConfig` / `LabConfig` objects with positive capacity, feature tags, and optional
  availability. Courses and preference maps reference their names; every course section has expected enrollment
  and may require features, stable identity, modality, and one optional lab assignment.
- Capacity, features, resource availability, delivery mode, lab assignment, and optional lecture-room
  occupancy during labs are separate hard solver rules with tracked artifacts and independent auditor checks; do
  not fold them invisibly into reference validation.
- After schema-affecting config changes, regenerate **`fern/docs/assets/combined-config.schema.json`** (see [sched-fern-openapi-docs](../sched-fern-openapi-docs/SKILL.md)).

## Z3

- Prefer clear, testable encodings; watch performance on large inputs.
- Respect existing **caching** patterns; do not remove `@cache` on hot paths without analysis (Ruff **B019** is suppressed on intentional method caches).
- Track each actionable hard rule with a granular `DiagnosticConstraintArtifact`, then mirror it independently in
  `ScheduleAuditor` and document it under Fern's **Scheduling rules and objectives** page.
