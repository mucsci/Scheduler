# Course Constraint Scheduler

A powerful constraint satisfaction solver for generating academic course schedules using the Z3 theorem prover.

## Start Here by Audience

- **Coding agents and contributors**: read [AGENT.md](AGENT.md), [CONTRIBUTING.md](CONTRIBUTING.md), and [skills/README.md](skills/README.md).
- **Python API users**: jump to [Python API](#python-api).
- **REST API users**: jump to [REST API](#rest-api).

### Naming Cheat Sheet

- **Repository**: `mucsci/scheduler`
- **Package on PyPI**: `course-constraint-scheduler`
- **Python import**: `scheduler`

## Overview

The Course Constraint Scheduler is designed to solve complex academic scheduling problems by modeling them as constraint satisfaction problems. It can handle:

- **Faculty constraints**: Availability, credit ranges, teaching-day rules, distinct-course limits, and preferences
- **Resource constraints**: Eligible room/lab assignment and collision prevention
- **Time constraints**: Credit/lab-compatible meeting patterns, fixed starts, alignment, overlap, and adjacency
- **Course constraints**: Repeated sections, declared conflicts, faculty eligibility, and no-lab schedules
- **Diagnostics and optimization**: Unsat cores, verified repairs, independent audits, and Pareto objectives

## Features

- **Z3 Integration**: Uses Microsoft's Z3 theorem prover for efficient constraint solving
- **Flexible Configuration**: JSON-based configuration with comprehensive validation
- **Multiple Output Formats**: JSON and CSV output support with type-safe serialization
- **REST API**: Full HTTP API for integration with web applications
- **Asynchronous Processing**: Background schedule generation for large problems
- **Session Management**: In-memory, expiring sessions for iterative schedule generation
- **Optimization Flags**: Configurable optimization strategies
- **Type Safety**: Strict Pydantic configuration and response models plus typed runtime objects
- **Enhanced Validation**: Cross-reference validation and business logic constraints
- **Improved Error Handling**: Detailed error messages for configuration debugging
- **Strict Type Validation**: Pydantic models with strict validation and custom type definitions
- **Computed Fields**: Automatic serialization with computed fields for clean JSON output

## Quick Start

Requires a minimum version of Python 3.12

### Installation

```bash
pip install course-constraint-scheduler
```

### Command Line Usage

```bash
# Generate schedules from configuration file
scheduler example.json --limit 10 --format json --output schedules

# Interactive mode
scheduler example.json --limit 5
```

### Python API

```python
from scheduler import (
    Scheduler,
    load_config_from_file,
)
from scheduler.config import CombinedConfig

# Load configuration
config = load_config_from_file(CombinedConfig, "example.json")

# Create scheduler
scheduler = Scheduler(config)

# Generate schedules
for schedule in scheduler.get_models():
    print("Schedule:")
    for course in schedule:
        print(f"{course.as_csv()}")

# Diagnose hard-constraint feasibility without consuming a model
diagnosis = scheduler.diagnose()

# Independently validate and score a decoded schedule
first_schedule = next(scheduler.get_models())
audit = scheduler.audit_schedule(first_schedule)
```

**Note on naming:** `scheduler.config` defines `Course` as a **course-id string** type alias (used in JSON config). `scheduler.models` defines a `Course` **class** representing a course with credits and meetings. Schedules from `get_models()` yield `CourseInstance` objects whose `.course` attribute is the models `Course`; use `.course.course_id` to get the config-style course id.

`Scheduler(config, solver_timeout_ms=...)` applies an optional timeout to each Z3 check. Structured raw validation
is available through `validate_combined_config_data`. The published **Diagnostics and auditing** guide documents
status, core, repair, provenance, completeness, and audit-score semantics.

### REST API

```bash
# Start the server with custom options
scheduler-server --port 8000 --host 0.0.0.0 --log-level info --workers 16

# 1) Submit a schedule request
curl -X POST "http://localhost:8000/submit" \
  -H "Content-Type: application/json" \
  -d @example.json

# 2) The submit response includes the schedule_id you need
# {"schedule_id":"f9f2...","endpoint":"/schedules/f9f2..."}

# 3) Use that schedule_id for schedule generation and progress
curl -X POST "http://localhost:8000/schedules/f9f2.../next"
curl -X GET "http://localhost:8000/schedules/f9f2.../count"

# Optional endpoints
curl -X POST "http://localhost:8000/validate" -H "Content-Type: application/json" -d @example.json
curl -X GET "http://localhost:8000/schedules/f9f2.../details"
curl -X GET "http://localhost:8000/schedules/f9f2.../diagnosis"
curl -X GET "http://localhost:8000/schedules/f9f2.../audit/0"
curl -X GET "http://localhost:8000/schedules/f9f2.../status"
curl -X GET "http://localhost:8000/schedules/f9f2.../index/0"
curl -X DELETE "http://localhost:8000/schedules/f9f2.../delete"
```

### Server deployment and security

The REST API is convenient for local use and trusted integrations. For production or internet-facing deployments:

- **No built-in authentication** — use a reverse proxy, API gateway, or private network; do not expose the process directly without controls you trust.
- **In-memory sessions** — active schedule sessions are lost on restart and are not shared across multiple server processes.
- **Resource limits** — the server caps active sessions, courses, requested schedules, candidate slots, solve time, and idle-session age. Tune the `SCHEDULER_API_*` environment variables documented in the REST quickstart for your deployment.
- **CORS** — set the `CORS_ORIGINS` environment variable to a comma-separated list of allowed origins when browsers must send credentials. If unset, the server allows all origins without credentials (typical for local development).

See [SECURITY.md](SECURITY.md) for how to report vulnerabilities.

## Documentation

**Published docs (configuration, Python API, REST API, development):**
[https://mucsci-scheduler.docs.buildwithfern.com](https://mucsci-scheduler.docs.buildwithfern.com)

If you are changing code or docs in this repo:

- Contributor workflow: [CONTRIBUTING.md](CONTRIBUTING.md)
- Agent workflow: [AGENT.md](AGENT.md)
- Skill playbooks: [skills/README.md](skills/README.md)

CI publishes this site on pushes to `main` that touch `fern/`, `scripts/`, or `src/scheduler/` (see `.github/workflows/docs.yml`). The repository needs a **`FERN_TOKEN`** Actions secret from the Fern CLI (`fern token`) or dashboard.

### Local REST API (OpenAPI UI)

```console
scheduler-server
# open http://localhost:8000/docs/ in a web browser
```

The `/submit` request body matches `CombinedConfig` (same JSON as the CLI and Python API).

### Local Fern preview

With [Node.js 22](https://nodejs.org/), Docker, and the Python development dependencies installed:

```console
npm install -g fern-api@5.75.4
uv run python scripts/export_openapi.py
uv run python scripts/export_config_schema.py
fern docs md generate --local --library scheduler-python
fern check --warnings
fern docs dev
```

Tracked generated artifacts used by Fern:

- `fern/openapi.json` (from FastAPI routes/models)
- `fern/docs/assets/combined-config.schema.json` (from `CombinedConfig`)

The Python library reference is generated from `src/scheduler` into the ignored
`fern/static/python-reference/` directory. Regenerate it with the Fern command above after public API or
docstring changes. CI performs the same generation before validating or publishing the site.

### Configuration quick link

A short pointer to the new docs location: [docs/configuration.md](./docs/configuration.md).

`example.json` is included in this repository for local cloning workflows. If you need a minimal sample, use `tests/fixtures/minimal_config.json`.

## Configuration

The scheduler uses a JSON configuration file that defines:

- **Rooms and Labs**: Available facilities and their constraints
- **Courses**: Course requirements, conflicts, and faculty assignments
- **Faculty**: Availability, preferences, and teaching constraints
- **Time Slots**: Available time blocks and class patterns
- **Optimization**: Flags for different optimization strategies

Use the validated [`tests/fixtures/minimal_config.json`](tests/fixtures/minimal_config.json) as the canonical small
example and [`example.json`](example.json) for a larger scheduling problem. The Fern configuration guide documents
every required field, default, validation rule, lab semantic, and time-slot generation rule.

## Architecture

The scheduler is built with a modular architecture:

- **SchedulingProblem**: Z3-free normalized policies, resources, time domains, source paths, and compatibility cache
- **SolverEngine**: Z3 symbols, relation tables, hard constraints, objectives, decoding, and model blocking
- **DiagnosticEngine**: Preflight analysis, provenance, unsat cores, suggestions, and verified repairs
- **ScheduleAuditor**: Independent hard-rule verification, summaries, and objective scoring
- **Scheduler**: Stable façade delegating enumeration, diagnosis, and auditing
- **Configuration and output**: Strict Pydantic validation plus JSON/CSV writers
- **REST server**: FastAPI sessions, serialized generation, background work, limits, and idle expiry

## Performance

- **Small Problems** (< 10 courses): Near-instantaneous solving
- **Medium Problems** (10-50 courses): Seconds to minutes
- **Large Problems** (50+ courses): May take several minutes
- **Optimization**: Use appropriate optimizer flags to reduce solving time

## Development

### Setup

```bash
# Clone the repository
git clone https://github.com/mucsci/scheduler.git
cd scheduler

# Install dependencies (includes dev tools via uv default-groups; see pyproject.toml)
uv sync

# Run tests
uv run pytest

# Fast unit tests only
uv run pytest -m "not integration and not slow" --no-cov

# Integration and golden compatibility tests
uv run pytest -m "integration and not slow" --no-cov

# Long-running full-example tests
uv run pytest -m slow --no-cov

# Run linting
uv run ruff check .
```

Using **pip** without optional extras: dev dependencies are declared under `[dependency-groups]` in `pyproject.toml`. Either use **uv** as above, or add a matching `[project.optional-dependencies]` `dev` group if you need `pip install -e ".[dev]"`.

### Logging

The scheduler does not configure logging on import. The CLI (`scheduler`) and HTTP server (`scheduler-server`) call `configure_logging()` at startup. When embedding the scheduler as a library, configure logging in your application (e.g. `logging.basicConfig(...)`) before using the scheduler.

### Project Structure

```
tests/                     # Pytest suite
src/scheduler/
├── __init__.py              # Main package exports with all types
├── audit.py                 # Independent schedule validation and objective scoring
├── config.py                # Configuration models with strict validation and type definitions
├── configuration.py         # Raw and combined configuration helpers
├── contracts.py             # Z3-free public diagnostic result contracts
├── diagnostics.py           # Feasibility analysis, unsat cores, and repair sets
├── json_types.py            # Supplemental TypedDicts for serialized schedule rows
├── logging.py               # Logging setup
├── main.py                  # Command-line interface
├── problem.py               # Normalized, solver-independent scheduling problem
├── scheduler.py             # Stable public façade
├── server.py                # REST API server with session management
├── solver.py                # Z3 constraints, optimization, decoding, and enumeration
├── time_slot_generator.py   # Utility for generating valid time slots
├── models/                  # Enhanced data models
│   ├── __init__.py          # Model exports
│   ├── course.py            # Course and instance models with computed fields
│   ├── day.py               # Day enumeration (IntEnum)
│   └── time_slot.py         # Time-related models with comprehensive methods
└── writers/                 # Output formatters
    ├── __init__.py          # Writer exports
    ├── csv_writer.py        # CSV output with context manager support
    └── json_writer.py       # JSON output with context manager support
```

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Ensure all tests pass
6. Submit a pull request

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Support

For questions, issues, or feature requests:

- Check the documentation
- Review existing issues
- Create a new issue with detailed information
- Include configuration examples and error messages

## Current diagnostic capabilities

- Structured validation codes and JSON Pointer locations
- Per-course candidate domains and rejected-pattern explanations
- Faculty/resource capacity and mandatory-day feasibility analysis
- Subset-minimal primary and bounded alternative unsat cores
- Ranked relaxation suggestions and solver-verified repair sets
- Provenance edges, configuration fingerprints, completeness flags, and timeout reasons
- Independent schedule, workload, resource, preference, and objective audits

## Roadmap

- [ ] Web-based configuration interface
- [ ] Schedule visualization tools
