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

- **Faculty Constraints**: Availability, credit limits, course preferences
- **Room Constraints**: Room assignments, lab requirements, capacity limits
- **Time Constraints**: Time slot conflicts, meeting patterns, duration requirements
- **Course Constraints**: Prerequisites, conflicts, section limits
- **Optimization**: Multiple optimization strategies for better schedules

## Features

- **Z3 Integration**: Uses Microsoft's Z3 theorem prover for efficient constraint solving
- **Flexible Configuration**: JSON-based configuration with comprehensive validation
- **Multiple Output Formats**: JSON and CSV output support with type-safe serialization
- **REST API**: Full HTTP API for integration with web applications
- **Asynchronous Processing**: Background schedule generation for large problems
- **Session Management**: Persistent sessions for iterative schedule generation
- **Optimization Flags**: Configurable optimization strategies
- **Type Safety**: Comprehensive TypedDict definitions for all JSON structures
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
```

**Note on naming:** `scheduler.config` defines `Course` as a **course-id string** type alias (used in JSON config). `scheduler.models` defines a `Course` **class** representing a course with credits and meetings. Schedules from `get_models()` yield `CourseInstance` objects whose `.course` attribute is the models `Course`; use `.course.course_id` to get the config-style course id.

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
curl -X GET "http://localhost:8000/schedules/f9f2.../details"
curl -X GET "http://localhost:8000/schedules/f9f2.../index/0"
curl -X DELETE "http://localhost:8000/schedules/f9f2.../delete"
```

### Server deployment and security

The REST API is convenient for local use and trusted integrations. For production or internet-facing deployments:

- **No built-in authentication** — use a reverse proxy, API gateway, or private network; do not expose the process directly without controls you trust.
- **In-memory sessions** — active schedule sessions are lost on restart and are not shared across multiple server processes.
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

With [Node.js](https://nodejs.org/) and dev dependencies installed:

```console
npm install -g fern-api
uv run python scripts/export_openapi.py
uv run python scripts/export_config_schema.py
uv run python scripts/gen_python_api_mdx.py
fern docs dev
```

Generated artifacts used by Fern:

- `fern/openapi.json` (from FastAPI routes/models)
- `fern/docs/assets/combined-config.schema.json` (from `CombinedConfig`)
- `fern/docs/pages/python/reference.mdx` (from public docstrings)

Regenerate these with the scripts above after API/config/docstring changes.

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

Example configuration:

```json
{
  "config": {
    "rooms": ["Room A", "Room B"],
    "labs": ["Lab 1"],
    "courses": [
      {
        "course_id": "CS101",
        "credits": 3,
        "room": ["Room A"],
        "lab": ["Lab 1"],
        "conflicts": [],
        "faculty": ["Dr. Smith"]
      }
    ],
    "faculty": [
      {
        "name": "Dr. Smith",
        "maximum_credits": 12,
        "minimum_credits": 6,
        "unique_course_limit": 3,
        "times": {
          "MON": ["09:00-17:00"],
          "TUE": ["09:00-17:00"],
          "WED": ["09:00-17:00"],
          "THU": ["09:00-17:00"],
          "FRI": ["09:00-17:00"]
        }
      }
    ]
  },
  "time_slot_config": {
    "times": {
      "MON": [
        {
          "start": "09:00",
          "spacing": 60,
          "end": "17:00"
        }
      ]
    },
    "classes": [
      {
        "credits": 3,
        "meetings": [
          {
            "day": "MON",
            "duration": 150,
            "lab": false
          }
        ]
      }
    ]
  },
  "limit": 10,
  "optimizer_flags": ["faculty_course", "pack_rooms"]
}
```

## Architecture

The scheduler is built with a modular architecture:

- **Core Solver**: Z3-based constraint satisfaction engine
- **Configuration Management**: Pydantic-based configuration validation with comprehensive error handling
- **Model Classes**: Enhanced data structures for courses, faculty, and time slots with improved serialization
- **JSON Types**: Comprehensive TypedDict definitions for type-safe JSON handling
- **Output Writers**: JSON and CSV output formatters with context manager support
- **REST Server**: FastAPI-based HTTP API with asynchronous processing and session management
- **Session Management**: Persistent session handling for large problems with background task support

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
├── config.py                # Configuration models with strict validation and type definitions
├── json_types.py            # TypedDict definitions for JSON structures
├── logging.py               # Logging setup
├── main.py                  # Command-line interface
├── scheduler.py             # Core scheduling logic with Z3 integration
├── server.py                # REST API server with session management
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

## Recent Updates

### Enhanced Configuration Validation
- Comprehensive cross-reference validation ensures all IDs exist
- Business logic validation prevents impossible constraints
- Detailed error messages for easier debugging
- Support for preference scores (0-10) with improved validation

### Improved Type Safety
- New `json_types.py` module with comprehensive TypedDict definitions
- Type-safe JSON handling throughout the application
- Enhanced serialization with computed fields
- Better integration with modern Python type checking

### Enhanced REST API
- Improved session management with background task support
- Better error handling and status codes
- Enhanced command-line options for server configuration
- Comprehensive API documentation with examples

### Model Improvements
- Enhanced Course and TimeSlot models with better methods
- Improved serialization with computed fields
- Better time handling with IntEnum for days
- Context manager support for writers

## Roadmap

- [ ] Web-based configuration interface
- [ ] Schedule visualization tools
- [ ] Multi-objective optimization support
