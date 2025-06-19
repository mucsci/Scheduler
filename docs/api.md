# Scheduler API Documentation

## Overview

The Scheduler is a constraint-based scheduling system that generates valid course schedules while respecting various constraints and preferences. It uses the Z3 theorem prover for constraint satisfaction solving.

## Public API

The following types and functions are available directly from the top-level `scheduler` module:

### Scheduler

The main class for generating course schedules.

```python
from scheduler import Scheduler, load_config_from_file, SchedulerConfig, TimeSlotConfig

# Load configurations
config = load_config_from_file(SchedulerConfig, "config.json")
time_slot_config = load_config_from_file(TimeSlotConfig, "time_slots.json")

# Create scheduler instance
scheduler = Scheduler(config, time_slot_config)

# Generate schedules
for model in scheduler.get_models(limit=5, optimize=True):
    # See Internal Types section for how to interpret models
    ...
```

#### Methods
- `__init__(config: SchedulerConfig, time_slot_config: TimeSlotConfig)`: Initialize the scheduler with configuration and time slots configuration
- `get_models(limit: int = 10, optimize: bool = True)`: Generate schedule models (returns Z3 models)

### load_config_from_file

Utility function to load configuration objects from JSON files.

```python
from scheduler import load_config_from_file, SchedulerConfig, TimeSlotConfig

config = load_config_from_file(SchedulerConfig, "config.json")
time_slot_config = load_config_from_file(TimeSlotConfig, "time_slots.json")
```

### Output Writers

#### JSONWriter

```python
from scheduler import JSONWriter

with JSONWriter() as writer:
    for model in scheduler.get_models(limit=1):
        writer.add_schedule(scheduler.courses, model)

with JSONWriter("schedules.json") as writer:
    for model in scheduler.get_models(limit=1):
        writer.add_schedule(scheduler.courses, model)
```

#### CSVWriter

```python
from scheduler import CSVWriter

with CSVWriter() as writer:
    for model in scheduler.get_models(limit=1):
        writer.add_schedule(scheduler.courses, model)

with CSVWriter("schedules.csv") as writer:
    for model in scheduler.get_models(limit=1):
        writer.add_schedule(scheduler.courses, model)
```

### Configuration Types

#### SchedulerConfig

Configuration for the scheduler.

```python
from scheduler import SchedulerConfig, CourseConfig, FacultyConfig

config = SchedulerConfig(
    rooms=["Room1", "Room2"],
    labs=["Lab1"],
    courses=[
        CourseConfig(
            course_id="CS101",
            credits=3,
            room=["Room1"],
            lab=["Lab1"],
            conflicts=["CS102"],
            faculty=["Prof1"]
        )
    ],
    faculty=[
        FacultyConfig(
            name="Prof1",
            maximum_credits=12,
            minimum_credits=9,
            unique_course_limit=3,
            times={
                "MON": ["09:00-17:00"],
                "TUE": ["09:00-17:00"]
            },
            preferences={"CS101": 5}
        )
    ]
)
```

#### TimeSlotConfig

Configuration for time slots.

```python
from scheduler import TimeSlotConfig, TimeBlock, Meeting, ClassPattern

time_slot_config = TimeSlotConfig(
    times={
        "MON": [
            TimeBlock(start="09:00", spacing=60, end="17:00"),
            TimeBlock(start="18:00", spacing=60, end="21:00")
        ],
        "TUE": [
            TimeBlock(start="09:00", spacing=60, end="17:00")
        ]
    },
    classes=[
        ClassPattern(
            credits=3,
            meetings=[
                Meeting(day="MON", duration=60),
                Meeting(day="TUE", duration=60)
            ]
        ),
        ClassPattern(
            credits=4,
            meetings=[
                Meeting(day="MON", duration=60),
                Meeting(day="TUE", duration=60),
                Meeting(day="MON", duration=60, lab=True)
            ]
        )
    ]
)
```

#### CourseConfig

Configuration for a course.

```python
from scheduler import CourseConfig

course = CourseConfig(
    course_id="CS101",
    credits=3,
    room=["Room1"],
    lab=["Lab1"],
    conflicts=["CS102"],
    faculty=["Prof1"]
)
```

#### FacultyConfig

Configuration for a faculty member.

```python
from scheduler import FacultyConfig

faculty = FacultyConfig(
    name="Prof1",
    maximum_credits=12,
    minimum_credits=9,
    unique_course_limit=3,
    times={
        "MON": ["09:00-17:00"],
        "TUE": ["09:00-17:00"]
    },
    preferences={"CS101": 5}
)
```

#### TimeBlock, Meeting, ClassPattern

These are helper types for constructing `TimeSlotConfig`.

```python
from scheduler import TimeBlock, Meeting, ClassPattern

block = TimeBlock(start="09:00", spacing=60, end="17:00")
meeting = Meeting(day="MON", duration=60, lab=False)
pattern = ClassPattern(credits=3, meetings=[meeting])
```

## Error Handling

The scheduler uses standard Python exceptions for error handling:

```python
try:
    config = load_config_from_file(SchedulerConfig, "config.json")
    scheduler = Scheduler(config, time_slot_config)
except Exception as e:
    print(f"Error: {e}")
```

## Example Usage

```python
from scheduler import Scheduler, load_config_from_file, SchedulerConfig, TimeSlotConfig

config = load_config_from_file(SchedulerConfig, "config.json")
time_slot_config = load_config_from_file(TimeSlotConfig, "time_slots.json")
scheduler = Scheduler(config, time_slot_config)

for model in scheduler.get_models(limit=1, optimize=True):
    # See Internal Types section for how to interpret models
    ...
```

## Best Practices

1. Always use the configuration classes (`SchedulerConfig`, `CourseConfig`, `FacultyConfig`, `TimeSlotConfig`) to create valid configurations
2. Use the `load_config_from_file` function to load configurations from JSON files
3. Enable optimization only when needed, as it can significantly increase solving time
4. Use appropriate error handling for file operations and configuration loading
5. Use the provided writers (`JSONWriter`, `CSVWriter`) for consistent output formatting
6. When analyzing schedules, use the Z3 model output with the internal types (see below)

---

# Internal Types (Advanced)

The following types are used internally by the scheduler and are not part of the public API, but may be useful for advanced users or contributors. They are available via submodules (e.g., `scheduler.models`).

- `Course`
- `CourseInstance`
- `TimeSlot`, `TimeInstance`, `TimePoint`, `Duration`
- `Faculty`, `Room`, `Lab`, `Day`

### Example: Interpreting Z3 Models

To extract a human-readable schedule from a Z3 model:

```python
from scheduler.models import Course

for model in scheduler.get_models(limit=1):
    schedule = [course.instance(model).__json__() for course in scheduler.courses]
    print(schedule)
```

### Internal Type Summaries

- **Course**: Represents a course in the scheduling system. Use `course.instance(model)` to get a `CourseInstance` from a Z3 model.
- **CourseInstance**: Represents a scheduled course with assigned time, faculty, room, and lab. Has `.__json__()` and `.csv()` methods for output.
- **TimeSlot**: Represents a time slot in the schedule. Has methods for overlap and adjacency checks.
- **TimeInstance, TimePoint, Duration**: Used for time calculations and representation.
- **Faculty, Room, Lab, Day**: Represent faculty, rooms, labs, and days of the week.

---

For most users, only the types and functions in the Public API section are needed. Use the Internal Types section only if you need to work directly with Z3 models or extend the scheduler's functionality.
