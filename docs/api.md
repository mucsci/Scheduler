# Scheduler API Documentation

## Overview

The Scheduler is a constraint-based scheduling system that generates valid course schedules while respecting various constraints and preferences. It uses the Z3 theorem prover for constraint satisfaction solving.

## Public API

The following types and functions are available directly from the top-level `scheduler` module:

### Scheduler

The main class for generating course schedules.

```python
from scheduler import Scheduler, load_config_from_file, SchedulerConfig, TimeSlotConfig, OptimizerFlags

# Load configurations
config = load_config_from_file(SchedulerConfig, "config.json")
time_slot_config = load_config_from_file(TimeSlotConfig, "time_slots.json")

# Create scheduler instance
scheduler = Scheduler(config, time_slot_config)

# Generate schedules with specific optimizer options
optimizer_options = [
    OptimizerFlags.FACULTY_COURSE,
    OptimizerFlags.FACULTY_ROOM,
    OptimizerFlags.FACULTY_LAB,
    OptimizerFlags.SAME_ROOM,
    OptimizerFlags.SAME_LAB,
    OptimizerFlags.PACK_ROOMS,
    OptimizerFlags.PACK_LABS
]

for schedule in scheduler.get_models(limit=5, optimizer_options=optimizer_options):
    # schedule is a list of CourseInstance objects
    for course_instance in schedule:
        print(f"{course_instance.course.course_id}: {course_instance.faculty}")
```

#### Methods
- `__init__(config: SchedulerConfig, time_slot_config: TimeSlotConfig)`: Initialize the scheduler with configuration and time slots configuration
- `get_models(limit: int = 10, optimizer_options: list[OptimizerFlags] | None = None)`: Generate schedule models (returns lists of CourseInstance objects)

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
    for schedule in scheduler.get_models(limit=1):
        writer.add_schedule(schedule)

with JSONWriter("schedules.json") as writer:
    for schedule in scheduler.get_models(limit=1):
        writer.add_schedule(schedule)
```

#### CSVWriter

```python
from scheduler import CSVWriter

with CSVWriter() as writer:
    for schedule in scheduler.get_models(limit=1):
        writer.add_schedule(schedule)

with CSVWriter("schedules.csv") as writer:
    for schedule in scheduler.get_models(limit=1):
        writer.add_schedule(schedule)
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
            course_preferences={"CS101": 5},
            room_preferences={"Room1": 5},
            lab_preferences={"Lab1": 5}
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
    course_preferences={"CS101": 5},
    room_preferences={"Room1": 5},
    lab_preferences={"Lab1": 5}
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

### Example: Working with CourseInstance Objects

Each `CourseInstance` represents a scheduled course with all its assignments:

```python
for schedule in scheduler.get_models(limit=1):
    for course_instance in schedule:
        print(f"Course: {course_instance.course.course_id}")
        print(f"Faculty: {course_instance.faculty}")
        print(f"Room: {course_instance.room if course_instance.room else 'None'}")
        print(f"Lab: {course_instance.lab if course_instance.lab else 'None'}")
        print(f"Time: {course_instance.time}")
        print(f"JSON: {course_instance.as_json()}")
        print(f"CSV: {course_instance.as_csv()}")
```

## Optimizer Options

The scheduler supports various optimization strategies that can be enabled individually:

### OptimizerFlags

```python
from scheduler import OptimizerFlags

# Available optimizer options
OptimizerFlags.FACULTY_COURSE    # Optimize for faculty course preferences
OptimizerFlags.FACULTY_ROOM      # Optimize for faculty room preferences  
OptimizerFlags.FACULTY_LAB       # Optimize for faculty lab preferences
OptimizerFlags.SAME_ROOM         # Prefer same faculty to use same rooms
OptimizerFlags.SAME_LAB          # Prefer same faculty to use same labs
OptimizerFlags.PACK_ROOMS        # Pack courses into fewer rooms when possible
OptimizerFlags.PACK_LABS         # Pack courses into fewer labs when possible
```

### Faculty Preferences

Faculty can now specify preferences for courses, rooms, and labs separately:

- **`course_preferences`**: Map of course IDs to preference values (1-5, where 5 is strongly preferred)
- **`room_preferences`**: Map of room names to preference values (1-5, where 5 is strongly preferred)  
- **`lab_preferences`**: Map of lab names to preference values (1-5, where 5 is strongly preferred)

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
from scheduler import Scheduler, load_config_from_file, SchedulerConfig, TimeSlotConfig, OptimizerFlags

config = load_config_from_file(SchedulerConfig, "config.json")
time_slot_config = load_config_from_file(TimeSlotConfig, "time_slots.json")
scheduler = Scheduler(config, time_slot_config)

# Use all optimizer options
optimizer_options = [
    OptimizerFlags.FACULTY_COURSE,
    OptimizerFlags.FACULTY_ROOM,
    OptimizerFlags.FACULTY_LAB,
    OptimizerFlags.SAME_ROOM,
    OptimizerFlags.SAME_LAB,
    OptimizerFlags.PACK_ROOMS,
    OptimizerFlags.PACK_LABS
]

for schedule in scheduler.get_models(limit=1, optimizer_options=optimizer_options):
    # schedule is a list of CourseInstance objects
    for course_instance in schedule:
        print(f"{course_instance.course.course_id}: {course_instance.faculty}")
```

## Best Practices

1. Always use the configuration classes (`SchedulerConfig`, `CourseConfig`, `FacultyConfig`, `TimeSlotConfig`) to create valid configurations
2. Use the `load_config_from_file` function to load configurations from JSON files
3. Enable only the optimizer options you need, as each option can increase solving time
4. Use appropriate error handling for file operations and configuration loading
5. Use the provided writers (`JSONWriter`, `CSVWriter`) for consistent output formatting
6. Consider the trade-off between optimization quality and solving time when choosing optimizer options
