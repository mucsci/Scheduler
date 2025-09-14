# Contributing to Course Constraint Scheduler

Thank you for your interest in contributing to the Course Constraint Scheduler! This document provides guidelines and instructions for developers who want to contribute to the project.

## Table of Contents

- [Getting Started](#getting-started)
- [Development Setup](#development-setup)
- [Project Structure](#project-structure)
- [Development Workflow](#development-workflow)
- [Code Standards](#code-standards)
- [Testing](#testing)
- [Documentation](#documentation)
- [Submitting Changes](#submitting-changes)
- [Release Process](#release-process)

## Getting Started

### Prerequisites

- **Python 3.12+**: The project requires Python 3.12 or higher
- **Git**: For version control
- **uv**: Modern Python package manager (recommended)

### Installing uv

We strongly recommend using `uv` for dependency management and virtual environments. It's faster and more reliable than traditional tools.

**macOS and Linux:**
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

**Windows:**
```powershell
powershell -c "irm https://astral.sh/uv/install.ps1 | iex"
```

**Alternative (pip):**
```bash
pip install uv
```

## Development Setup


### 1. Clone the repository
```bash
git clone https://github.com/mucsci/scheduler.git
cd scheduler
```

### 2. Set Up Virtual Environment with uv

**Recommended approach using uv:**
```bash
# Create and activate virtual environment
uv venv
source .venv/bin/activate  # On macOS/Linux
# OR
.venv\Scripts\activate     # On Windows

# Install dependencies
uv sync

# Install package in editable mode
uv pip install -e .
```

**Alternative (if uv is not available):**
```bash
# Create virtual environment
python -m venv .venv
source .venv/bin/activate  # On macOS/Linux
# OR
.venv\Scripts\activate     # On Windows

# Install dependencies
pip install -r requirements.txt
pip install -e .
```

### 3. Install Development Dependencies

```bash
# Using uv (recommended)
uv sync --group dev

# Using pip
pip install -e ".[dev]"
```

### 4. Verify Installation

```bash
# Test the scheduler
python -m scheduler.main --help

# Test the server
python -m scheduler.server --help

# Run tests
pytest
```

## Project Structure

```
src/scheduler/
├── __init__.py             # Main package exports
├── config.py               # Configuration models and validation
├── json_types.py           # TypedDict definitions for JSON structures
├── main.py                 # Command-line interface
├── scheduler.py            # Core scheduling logic and Z3 integration
├── server.py               # FastAPI REST server
├── logging.py              # Logging configuration
├── models/                 # Data models
│   ├── __init__.py         # Model exports
│   ├── course.py           # Course and CourseInstance models
│   ├── day.py              # Day enumeration
│   └── time_slot.py        # Time-related models (TimeSlot, TimeInstance, etc.)
├── writers/                # Output formatters
│   ├── __init__.py         # Writer exports
│   ├── json_writer.py      # JSON output writer
│   └── csv_writer.py       # CSV output writer
└── time_slot_generator.py  # Time slot generation utilities

docs/                       # Documentation
├── configuration.md        # Configuration file format
├── python_api.md           # Python API
└── rest_api.md             # REST API
```

## Development Workflow

### 1. Create a Feature Branch

```bash
# Ensure you're on main and up to date
git checkout main
git pull origin main

# Create and checkout a feature branch
git checkout -b feature/your-feature-name
```

### 2. Make Your Changes

- Write your code following the [Code Standards](#code-standards)
- Update documentation as needed
- Ensure all tests pass

### 3. Test Your Changes

```bash
# Run linting
ruff check

# Run type checking
ty check
```

### 4. Commit Your Changes

```bash
# Stage your changes
git add .

# Commit with a descriptive message
git commit -m "feat: add new optimization algorithm for room packing

- Implemented improved room packing algorithm
- Added configuration option for packing strategy
- Updated tests and documentation
- Performance improvement of 15% for large schedules"
```

### 5. Push and Create Pull Request

```bash
git push origin feature/your-feature-name
```

Then create a Pull Request on GitHub with:
- Clear description of changes
- Reference to any related issues
- Screenshots for UI changes
- Performance impact analysis if applicable

## Code Standards

### Python Style Guide

We follow [PEP 8](https://pep8.org/) with some modifications enforced by our linting tools.

**Key Standards:**
- Use 4 spaces for indentation (no tabs)
- Maximum line length: 88 characters (enforced by Black)
- Use descriptive variable and function names
- Add type hints for all function parameters and return values
- Use f-strings for string formatting (Python 3.6+)

### Import Organization

```python
# Standard library imports
import json
import logging
from typing import List, Optional

# Third-party imports
import z3
from pydantic import BaseModel

# Local imports
from .models import Course, CourseInstance
from .config import SchedulerConfig
```

### Documentation Standards

**Docstrings:**
```python
def generate_schedule(config: SchedulerConfig) -> List[CourseInstance]:
    """Generate a course schedule based on configuration.
    
    **Args:**
    - config: The scheduler configuration containing courses, faculty, and constraints.
    
    **Returns:**
    A list of course instances representing the generated schedule.
    
    **Raises:**
    - ValueError: If the configuration is invalid.
    - RuntimeError: If no valid schedule can be generated.
    
    **Example:**
        >>> config = load_config_from_file("config.json")
        >>> schedule = generate_schedule(config, limit=5)
        >>> print(f"Generated {len(schedule)} courses")
    """
    pass
```

**Inline Comments:**
```python
# Use comments to explain WHY, not WHAT
# Avoid obvious comments like "increment counter"
# Good: "Skip Fridays for labs as they're not available for scheduling"
if day == Day.FRI:
    continue
```

### Error Handling

```python
# Use specific exception types
try:
    result = z3_solver.check()
except z3.Z3Exception as e:
    logger.error(f"Z3 solver failed: {e}")
    raise RuntimeError(f"Schedule generation failed: {e}") from e

# Provide meaningful error messages
if not faculty_available:
    raise ValueError(
        f"Faculty member '{faculty_name}' has no available time slots "
        f"that match the course requirements"
    )
```

## Documentation

### Code Documentation

- All public functions and classes must have docstrings
- Use Google-style docstrings for consistency
- Include examples for complex functions
- Document exceptions and error conditions

### API Documentation

- Update REST API documentation for new endpoints
- Include request/response examples
- Document error codes and messages
- Update OpenAPI schema if applicable

### User Documentation

- Update README.md for new features
- Add configuration examples
- Update troubleshooting guides
- Include performance considerations

## Submitting Changes

### Pull Request Checklist

Before submitting a pull request, ensure:

- [ ] Code passes linting (`ruff check`)
- [ ] Type checking passes (`ty check`)
- [ ] Documentation is updated
- [ ] Breaking changes are documented
- [ ] Commit messages follow conventional format

### Commit Message Format

We use [Conventional Commits](https://www.conventionalcommits.org/) format:

```
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

**Types:**
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `style`: Code style changes (formatting, etc.)
- `refactor`: Code refactoring
- `test`: Adding or updating tests
- `chore`: Maintenance tasks

**Examples:**
```
feat: add new optimization algorithm for room packing

fix(scheduler): resolve memory leak in large schedule generation

docs: update configuration guide with new options

test: add performance benchmarks for optimization algorithms
```

### Review Process

1. **Automated Checks**: CI/CD pipeline runs tests and linting
2. **Code Review**: At least one maintainer must approve
3. **Testing**: Changes are tested in staging environment
4. **Merge**: Changes are merged to main branch

## Release Process

### Version Management

We use [Semantic Versioning](https://semver.org/):

- **MAJOR**: Breaking changes
- **MINOR**: New features (backward compatible)
- **PATCH**: Bug fixes (backward compatible)

### Release Steps

1. **Update Version**: Update version in `pyproject.toml`
2. **Changelog**: Update `CHANGELOG.md` with new changes
3. **Tag Release**: Create git tag for the version
4. **Build Package**: Build and test the package
5. **Publish**: Publish to PyPI
6. **Documentation**: Update documentation for new version

### Release Commands

```bash
# Build package
uv run build

# Test package
uv run twine check dist/*

# Publish to PyPI
uv run twine upload dist/*
```

## Getting Help

### Communication Channels

- **GitHub Issues**: Bug reports and feature requests
- **GitHub Discussions**: General questions and discussions
- **Pull Requests**: Code review and collaboration

### Resources

- [Python Documentation](https://docs.python.org/)
- [FastAPI Documentation](https://fastapi.tiangolo.com/)
- [Z3 Documentation](https://github.com/Z3Prover/z3/wiki)
- [Pydantic Documentation](https://pydantic-docs.helpmanual.io/)

### Mentorship

New contributors are welcome! We're happy to:
- Help you get started
- Review your first pull request
- Pair program on complex features
- Provide guidance on best practices

## Code of Conduct

We are committed to providing a welcoming and inclusive environment for all contributors. Please read our [Code of Conduct](CODE_OF_CONDUCT.md) for details.

## License

By contributing to this project, you agree that your contributions will be licensed under the MIT License. See [LICENSE](LICENSE) for details.

---

Thank you for contributing to the Course Constraint Scheduler! Your contributions help make academic scheduling more efficient and accessible for everyone.
