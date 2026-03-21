---
name: sched-domain-z3-config
description: >-
  Implements or debugs scheduling logic, Z3 constraints, and JSON configuration
  for the course constraint scheduler. Use when working in scheduler.py,
  config models, time slots, or solver behavior.
---

# Domain: Z3, config, models

## Core files

- **`scheduler.py`**: Z3 problem construction, solving, optimization flags.
- **`config.py`**: Pydantic models, validation, loading (`CombinedConfig`, etc.).
- **`time_slot_generator.py`**: Time slot generation utilities.
- **`models/`**: Runtime schedule representations (`CourseInstance`, `TimeSlot`, …).

## Naming trap: `Course`

- **`scheduler.config`**: `Course` (and related types) align with **JSON config** — often **course id strings** and config-shaped structures.
- **`scheduler.models`**: **`Course`** is a **class** (credits, meetings, …). Instances in schedules use **`CourseInstance`**; the config id is **`course_instance.course.course_id`**.

When touching types or docs, preserve this distinction to avoid breaking configs or the public API.

## Config workflow

- Representative sample: **`example.json`**; smaller fixtures under **`tests/fixtures/`**.
- After schema-affecting config changes, regenerate **`fern/docs/assets/combined-config.schema.json`** (see [sched-fern-openapi-docs](../sched-fern-openapi-docs/SKILL.md)).

## Z3

- Prefer clear, testable encodings; watch performance on large inputs.
- Respect existing **caching** patterns; do not remove `@cache` on hot paths without analysis (Ruff **B019** is suppressed on intentional method caches).
