# Course Constraint Scheduler

A powerful constraint satisfaction solver for generating academic course schedules using the Z3 theorem prover.

## Overview

The Course Constraint Scheduler is designed to solve complex academic scheduling problems by modeling them as constraint satisfaction problems. It can handle:

- **Faculty Constraints**: Availability, credit limits, course preferences
- **Room Constraints**: Room assignments, lab requirements, capacity limits
- **Time Constraints**: Time slot conflicts, meeting patterns, duration requirements
- **Course Constraints**: Prerequisites, conflicts, section limits
- **Optimization**: Multiple optimization strategies for better schedules

## Features

- **Z3 Integration**: Uses Microsoft's Z3 theorem prover for efficient constraint solving
- **Flexible Configuration**: JSON-based configuration for easy customization
- **Multiple Output Formats**: JSON and CSV output support
- **REST API**: Full HTTP API for integration with web applications
- **Asynchronous Processing**: Background schedule generation for large problems
- **Session Management**: Persistent sessions for iterative schedule generation
- **Optimization Flags**: Configurable optimization strategies

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
from scheduler import Scheduler, load_config_from_file, CombinedConfig

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


### REST API

```bash
# Start the server
scheduler-server --port 8000

# Submit a schedule request
curl -X POST "http://localhost:8000/submit" \
  -H "Content-Type: application/json" \
  -d @example.json
```

## Documentation

- **[Python API Documentation](docs/python_api.md)** - Complete Python API reference
- **[REST API Documentation](docs/rest_api.md)** - Full REST API specification
- **[Configuration Guide](docs/configuration.md)** - Configuration file format and examples

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
- **Configuration Management**: Pydantic-based configuration validation
- **Model Classes**: Data structures for courses, faculty, and time slots
- **Output Writers**: JSON and CSV output formatters
- **REST Server**: FastAPI-based HTTP API
- **Session Management**: Persistent session handling for large problems

## Performance

- **Small Problems** (< 10 courses): Near-instantaneous solving
- **Medium Problems** (10-50 courses): Seconds to minutes
- **Large Problems** (50+ courses): May take several minutes
- **Optimization**: Use appropriate optimizer flags to reduce solving time

## Development

### Setup

```bash
# Clone the repository
git clone <repository-url>
cd course-constraint-scheduler

# Install development dependencies
pip install -e ".[dev]"

# Run tests
pytest

# Run linting
ruff check src/
```

### Project Structure

```
src/scheduler/
├── __init__.py              # Main package exports
├── config.py                # Configuration models
├── logging.py               # Logging setup
├── main.py                  # Command-line interface
├── scheduler.py             # Core scheduling logic
├── server.py                # REST API server
├── time_slot_generator.py   # Utility for generating valid time slots
├── models/                  # Data models
│   ├── course.py            # Course and instance models
│   ├── day.py               # Day enumeration
│   ├── time_slot.py         # Time-related models
│   └── identifiable.py      # Base identifiable class
└── writers/                 # Output formatters
    ├── csv_writer.py        # CSV output
    └── json_writer.py       # JSON output
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

## Roadmap

- [ ] Web-based configuration interface
- [ ] Schedule visualization tools
- [ ] Multi-objective optimization support
