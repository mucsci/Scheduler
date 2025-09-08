# Python API Documentation

## Overview

The `course-constraint-scheduler` package provides a comprehensive constraint satisfaction solver for generating academic course schedules. It uses the Z3 theorem prover to find valid schedules that satisfy various constraints including faculty availability, room assignments, time conflicts, and optimization preferences.

## Installation

```bash
pip install course-constraint-scheduler
```

## Quick Start

```python
from scheduler import Scheduler, load_config_from_file, CombinedConfig

# Load configuration from JSON file
config = load_config_from_file(CombinedConfig, "config.json")

# Create scheduler
scheduler = Scheduler(config)

# Generate schedules
for schedule in scheduler.get_models():
    print(f"Generated schedule: {schedule}")
```

## Package Exports

The main package exports the following classes and functions:

```python
from scheduler import (
    # Core classes
    Scheduler,
    load_config_from_file,
    
    # Writers
    JSONWriter,
    CSVWriter,
    
    # Configuration types
    Time,
    TimeRange,
    Day,
    TimeBlock,
    Meeting,
    ClassPattern,
    TimeSlotConfig,
    CourseConfig,
    FacultyConfig,
    SchedulerConfig,
    CombinedConfig,
    OptimizerFlags,
)
```

## Core Classes

### Scheduler

The main scheduler class that handles constraint solving and schedule generation.

#### Constructor

```python
Scheduler(full_config: CombinedConfig)
```

**Parameters:**
- `full_config`: A `CombinedConfig` object containing all scheduler configuration

#### Methods

##### `get_models() -> Generator[list[CourseInstance], None, None]`

Generates valid schedules that satisfy all constraints.

**Returns:**
- A generator yielding lists of `CourseInstance` objects, each representing a complete schedule

**Example:**
```python
scheduler = Scheduler(config)
for schedule in scheduler.get_models():
    print(f"Schedule with {len(schedule)} courses")
    for course_instance in schedule:
        print(f"  {course_instance.course} at {course_instance.time}")
```

**Note:** The scheduler uses Z3 theorem prover for constraint solving. Each call to `get_models()` creates a new generator that can be used to iterate through valid schedules.

### Configuration Classes

#### Type Definitions

The configuration system uses several type aliases for validation and clarity:

```python
# Time-related types
TimeString = Annotated[str, Field(pattern=r"^([0-1][0-9]|2[0-3]):[0-5][0-9]$")]  # HH:MM format
TimeRangeString = Annotated[str, Field(pattern=r"^([0-1][0-9]|2[0-3]):[0-5][0-9]-([0-1][0-9]|2[0-3]):[0-5][0-9]$")]  # HH:MM-HH:MM format

# Preference scoring
Preference = Annotated[int, Field(ge=0, le=10)]  # 0-10 scale

# Entity types
Day = Annotated[Literal["MON", "TUE", "WED", "THU", "FRI"], Field(frozen=True)]
Room = Annotated[str, Field(frozen=True)]
Lab = Annotated[str, Field(frozen=True)]
Course = Annotated[str, Field(frozen=True)]
Faculty = Annotated[str, Field(frozen=True)]
```

#### CombinedConfig

Main configuration container that holds all scheduler settings.

```python
class CombinedConfig(BaseModel):
    config: SchedulerConfig
    time_slot_config: TimeSlotConfig
    limit: int = 10
    optimizer_flags: list[OptimizerFlags] = []
```

**Fields:**
- `config`: Main scheduler configuration (rooms, labs, courses, faculty)
- `time_slot_config`: Time slot and class pattern configuration
- `limit`: Maximum number of schedules to generate (default: 10)
- `optimizer_flags`: List of optimization preferences

#### SchedulerConfig

Core configuration for courses, faculty, rooms, and labs.

```python
class SchedulerConfig(BaseModel):
    rooms: list[str]
    labs: list[str]
    courses: list[CourseConfig]
    faculty: list[FacultyConfig]
```

**Fields:**
- `rooms`: List of available room names
- `labs`: List of available lab names
- `courses`: List of course configurations
- `faculty`: List of faculty configurations

#### CourseConfig

Configuration for individual courses.

```python
class CourseConfig(BaseModel):
    course_id: str
    credits: int
    room: list[str]
    lab: list[str]
    conflicts: list[str]
    faculty: list[str]
```

**Fields:**
- `course_id`: Unique identifier for the course
- `credits`: Number of credit hours
- `room`: List of acceptable room names
- `lab`: List of acceptable lab names
- `conflicts`: List of course IDs that cannot be scheduled simultaneously
- `faculty`: List of faculty names who can teach this course

#### FacultyConfig

Configuration for faculty members.

```python
class FacultyConfig(BaseModel):
    name: str
    maximum_credits: int
    minimum_credits: int
    unique_course_limit: int
    times: dict[str, list[str]]
    course_preferences: dict[str, int] = {}
    room_preferences: dict[str, int] = {}
    lab_preferences: dict[str, int] = {}
```

**Fields:**
- `name`: Faculty member's name
- `maximum_credits`: Maximum credit hours they can teach
- `minimum_credits`: Minimum credit hours they must teach
- `unique_course_limit`: Maximum number of different courses they can teach
- `times`: Dictionary mapping day names to time ranges (format: "HH:MM-HH:MM")
- `course_preferences`: Dictionary mapping course IDs to preference scores (higher = more preferred)
- `room_preferences`: Dictionary mapping room names to preference scores
- `lab_preferences`: Dictionary mapping lab names to preference scores

#### TimeSlotConfig

Configuration for time slots and class patterns.

```python
class TimeSlotConfig(BaseModel):
    times: dict[str, list[TimeBlock]]
    classes: list[ClassPattern]
```

**Fields:**
- `times`: Dictionary mapping day names to time blocks
- `classes`: List of class pattern configurations

#### TimeBlock

Represents a time block within a day.

```python
class TimeBlock(BaseModel):
    start: str
    spacing: int
    end: str
```

**Fields:**
- `start`: Start time in "HH:MM" format
- `spacing`: Time spacing between slots in minutes
- `end`: End time in "HH:MM" format

#### ClassPattern

Defines the structure of a class.

```python
class ClassPattern(BaseModel):
    credits: int
    meetings: list[Meeting]
    disabled: bool = False
    start_time: str | None = None
```

**Fields:**
- `credits`: Number of credit hours
- `meetings`: List of meeting configurations
- `disabled`: Whether this pattern is disabled
- `start_time`: Specific start time constraint (optional)

#### Meeting

Represents a single meeting instance.

```python
class Meeting(BaseModel):
    day: str
    duration: int
    lab: bool = False
```

**Fields:**
- `day`: Day of the week
- `duration`: Duration in minutes
- `lab`: Whether this meeting requires a lab

#### OptimizerFlags

Enumeration of available optimization options.

```python
class OptimizerFlags(StrEnum):
    FACULTY_COURSE = "faculty_course"      # Optimize faculty-course assignments
    FACULTY_ROOM = "faculty_room"          # Optimize faculty-room preferences
    FACULTY_LAB = "faculty_lab"            # Optimize faculty-lab preferences
    SAME_ROOM = "same_room"                # Prefer same room for course sections
    SAME_LAB = "same_lab"                  # Prefer same lab for course sections
    PACK_ROOMS = "pack_rooms"              # Pack courses into fewer rooms
    PACK_LABS = "pack_labs"                # Pack courses into fewer labs
```

### Model Classes

#### Course

Represents a course with its constraints and Z3 variables.

```python
class Course(Identifiable):
    credits: int
    course_id: str
    section: int | None
    labs: list[str]
    rooms: list[str]
    conflicts: list[str]
    faculties: list[str]
```

**Methods:**
- `uid() -> str`: Returns the course identifier
- `faculty() -> z3.ExprRef`: Returns the Z3 variable for faculty assignment
- `time() -> z3.ExprRef`: Returns the Z3 variable for time assignment
- `room() -> z3.ExprRef`: Returns the Z3 variable for room assignment
- `lab() -> z3.ExprRef`: Returns the Z3 variable for lab assignment

**Properties:**
- **`credits`**: Number of credit hours for this course
- **`course_id`**: Unique identifier for the course
- **`section`**: Section number (automatically assigned if not provided)
- **`labs`**: List of acceptable lab names
- **`rooms`**: List of acceptable room names
- **`conflicts`**: List of course IDs that cannot be scheduled simultaneously
- **`faculties`**: List of faculty names who can teach this course

**Note:** The `section` field is automatically assigned based on the course_id if not explicitly provided. Each course instance gets a unique section number.

#### CourseInstance

Represents a scheduled course instance.

```python
class CourseInstance(BaseModel):
    course: Course = Field(exclude=True)
    time: TimeSlot = Field(exclude=True)
    faculty: str
    room: str | None = Field(default=None)
    lab: str | None = Field(default=None)
```

**Methods:**
- `as_csv() -> str`: Converts to CSV representation

**Computed Fields:**
- **`course_str`** (alias: `course`): String representation of the course (e.g., "CS101.01")
- **`times`**: List of TimeInstance objects representing the scheduled times
- **`lab_index`**: Index of the lab time in the times list (if applicable, None if no lab)

**Properties:**
- **`course`**: The Course object (excluded from serialization)
- **`time`**: The TimeSlot object (excluded from serialization)
- **`faculty`**: Name of the assigned faculty member
- **`room`**: Name of the assigned room (None if not assigned)
- **`lab`**: Name of the assigned lab (None if not assigned)

**Serialization:**
The `CourseInstance` uses Pydantic's serialization features to provide clean JSON output with computed fields. The `course` and `time` fields are excluded from serialization and replaced with their string representations. When serialized with `model_dump(by_alias=True, exclude_none=True)`, the output matches the `CourseInstanceJSON` TypedDict structure.

#### TimeSlot

Represents a time slot assignment.

```python
class TimeSlot(Identifiable):
    times: list[TimeInstance]
    lab_index: int | None
```

**Methods:**
- `lab_time() -> TimeInstance | None`: Returns the lab time instance if applicable
- `has_lab() -> bool`: Returns True if this time slot has a lab component
- `lab_next_to(other: TimeSlot) -> bool`: Checks if lab times are adjacent
- `lecture_next_to(other: TimeSlot) -> bool`: Checks if lecture times are adjacent
- `overlaps(other: TimeSlot) -> bool`: Checks if time slots overlap
- `lab_overlaps(other: TimeSlot) -> bool`: Checks if lab times overlap
- `in_time_ranges(ranges: list[TimeInstance]) -> bool`: Checks if time slot fits in given ranges

**Properties:**
- **`times`**: List of TimeInstance objects representing all meeting times
- **`lab_index`**: Index of the lab time in the times list (None if no lab)

**Class Constants:**
- **`_MAX_TIME_DIFF_BETWEEN_SLOTS`**: Maximum time difference (30 minutes) for considering slots as adjacent

#### TimeInstance

Represents a specific time instance.

```python
class TimeInstance(BaseModel):
    day: Day
    start: TimePoint
    duration: Duration
```

**Properties:**
- **`day`**: Day of the week (Day enum)
- **`start`**: Start time as TimePoint
- **`duration`**: Duration as Duration object
- **`stop`**: Calculated end time as TimePoint (start + duration)

**Methods:**
- `__str__() -> str`: String representation in format "DAY HH:MM-HH:MM"

#### TimePoint

Represents a point in time.

```python
class TimePoint(BaseModel):
    timepoint: int
```

**Static Methods:**
- `make_from(hr: int, min: int) -> TimePoint`: Creates from hour and minute

**Properties:**
- **`hour`**: Hour component (0-23)
- **`minute`**: Minute component (0-59)
- **`value`**: Raw timepoint value in minutes from midnight

**Operators:**
- `+ Duration`: Add duration to time point
- `- TimePoint`: Calculate duration between time points
- `<`, `<=`, `>`, `>=`, `==`, `!=`: Standard comparison operators

**Methods:**
- `__str__() -> str`: String representation in "HH:MM" format
- `__repr__() -> str`: Detailed representation for debugging

#### Duration

Represents a time duration.

```python
class Duration(BaseModel):
    duration: int
```

**Properties:**
- **`value`**: Duration value in minutes

**Operators:**
- `+`, `-`, `<`, `<=`, `>`, `>=`, `==`, `!=`: Standard comparison operators
- `__abs__()`: Returns absolute value of duration

**Methods:**
- `__str__() -> str`: String representation of duration value
- `__repr__()`: Detailed representation for debugging

**Serialization:**
- Serializes to integer value (minutes)

#### Day

Enumeration of weekdays.

```python
class Day(IntEnum):
    MON = auto()
    TUE = auto()
    WED = auto()
    THU = auto()
    FRI = auto()
```

**Values:**
- `MON = 1`: Monday
- `TUE = 2`: Tuesday
- `WED = 3`: Wednesday
- `THU = 4`: Thursday
- `FRI = 5`: Friday

**Methods:**
- `__str__() -> str`: Returns the day name (e.g., "MON")
- `__repr__() -> str`: Returns the day name for debugging

### JSON Types Module

The `json_types` module provides comprehensive TypedDict definitions for all JSON structures used throughout the scheduler.

#### Key Types

- **`CourseInstanceJSON`**: JSON representation of a CourseInstance
- **`TimeInstanceJSON`**: JSON representation of a TimeInstance

#### CourseInstanceJSON

```python
class CourseInstanceJSON(TypedDict):
    course: str  # Course string representation (e.g., "CS101.01")
    faculty: str
    room: NotRequired[str | None]
    lab: NotRequired[str | None]
    times: list[TimeInstanceJSON]
    lab_index: NotRequired[int | None]
```

#### TimeInstanceJSON

```python
class TimeInstanceJSON(TypedDict):
    day: int  # Day enum value (1=MON, 2=TUE, etc.)
    start: int  # Timepoint in minutes from midnight
    duration: int  # Duration in minutes
```

#### Usage

```python
from scheduler.json_types import CourseInstanceJSON, TimeInstanceJSON

# Type hints for JSON data
def process_schedule_json(schedule: list[CourseInstanceJSON]) -> None:
    for course in schedule:
        print(f"Course: {course['course']}")
        for time in course['times']:
            print(f"  Time: Day {time['day']} at {time['start']} minutes for {time['duration']} minutes")
```

### Writer Classes

#### JSONWriter

Writes schedules in JSON format.

```python
class JSONWriter:
    def __init__(self, filename: str | None = None)
    def add_schedule(self, schedule: list[CourseInstance]) -> None
```

**Usage:**
```python
with JSONWriter("schedules.json") as writer:
    for schedule in scheduler.get_models():
        writer.add_schedule(schedule)
```

**Features:**
- Context manager support for automatic file handling
- Accumulates multiple schedules in memory
- Outputs compact JSON format
- Supports both file output and stdout

#### CSVWriter

Writes schedules in CSV format.

```python
class CSVWriter:
    def __init__(self, filename: str | None = None)
    def add_schedule(self, schedule: list[CourseInstance]) -> None
```

**Usage:**
```python
with CSVWriter("schedules.csv") as writer:
    for schedule in scheduler.get_models():
        writer.add_schedule(schedule)
```

## Utility Functions

### `load_config_from_file`

Loads configuration from a JSON file.

```python
def load_config_from_file(
    config_cls: type[T],
    filename: str,
) -> T
```

**Parameters:**
- `config_cls`: Configuration class type
- `filename`: Path to JSON configuration file

**Returns:**
- Configuration object of the specified type

**Example:**
```python
config = load_config_from_file(CombinedConfig, "config.json")
```

### `get_faculty_availability`

Parses faculty availability from configuration.

```python
def get_faculty_availability(
    faculty_config: FacultyConfig,
) -> list[TimeInstance]
```

**Parameters:**
- `faculty_config`: Faculty configuration object

**Returns:**
- List of available time instances

## Configuration File Format

The scheduler expects a JSON configuration file with the following structure:

```json
{
  "config": {
    "rooms": ["Room A", "Room B", "Room C"],
    "labs": ["Lab 1", "Lab 2"],
    "courses": [
      {
        "course_id": "CS101",
        "credits": 3,
        "room": ["Room A", "Room B"],
        "lab": ["Lab 1"],
        "conflicts": ["CS102"],
        "faculty": ["Dr. Smith", "Dr. Johnson"]
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
        },
        "course_preferences": {
          "CS101": 10,
          "CS102": 8
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

## Advanced Usage

### Custom Optimization

```python
from scheduler import OptimizerFlags

config = CombinedConfig(
    config=scheduler_config,
    time_slot_config=time_slot_config,
    limit=20,
    optimizer_flags=[
        OptimizerFlags.FACULTY_COURSE,
        OptimizerFlags.PACK_ROOMS,
        OptimizerFlags.SAME_ROOM
    ]
)
```

### Iterative Schedule Generation

```python
scheduler = Scheduler(config)
generator = scheduler.get_models()

# Get first schedule
try:
    first_schedule = next(generator)
    print(f"First schedule: {len(first_schedule)} courses")
except StopIteration:
    print("No valid schedules found")

# Get more schedules
for i, schedule in enumerate(generator):
    if i >= 5:  # Limit to 5 more schedules
        break
    print(f"Schedule {i+2}: {len(schedule)} courses")
```

### Error Handling

```python
try:
    scheduler = Scheduler(config)
    for schedule in scheduler.get_models():
        process_schedule(schedule)
except ValueError as e:
    print(f"Configuration error: {e}")
except Exception as e:
    print(f"Unexpected error: {e}")
```

## Performance Considerations

- The Z3 solver can be computationally intensive for large problems
- Use the `limit` parameter to control the number of generated schedules
- Consider using optimization flags to reduce search space
- Large faculty availability windows may increase solving time
- Complex conflict constraints can significantly impact performance

## Troubleshooting

### Common Issues

1. **No schedules generated**: Check constraint conflicts and faculty availability
2. **Slow performance**: Reduce the number of courses or faculty members
3. **Memory issues**: Lower the `limit` parameter
4. **Invalid configuration**: Verify JSON format and required fields

### Debug Mode

Enable debug logging to see detailed constraint solving information:

```python
import logging
logging.basicConfig(level=logging.DEBUG)
```
