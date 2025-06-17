# Scheduler API Documentation

## Overview

The Scheduler is a constraint-based scheduling system that generates valid course schedules while respecting various constraints and preferences. It uses the Z3 theorem prover for constraint satisfaction solving.

## Core Classes

### Scheduler

The main class for generating course schedules.

```python
from scheduler import Scheduler, load_from_file

# Create scheduler instance
scheduler = Scheduler(config, time_slots_config_file)

# Generate schedules
for model in scheduler.get_models(limit=5, optimize=True):
    schedule = [course.instance(model).__json__() for course in scheduler.courses]
```

#### Methods

- `__init__(config: SchedulerConfig, time_slots_config_file: str)`: Initialize the scheduler with configuration and time slots file
- `get_models(limit: int = 10, optimize: bool = True)`: Generate schedule models

### Course

Represents a course in the scheduling system.

```python
class Course:
    def __init__(self, credits: int, course_id: str, labs: List[str],
                 rooms: List[str], conflicts: List[str], faculties: List[str],
                 ctx: z3.Context):
        """
        Initialize a course.
        
        Args:
            credits: Number of credits for the course
            course_id: Unique identifier for the course
            labs: List of lab names that can be used
            rooms: List of room names that can be used
            conflicts: List of course IDs that cannot be scheduled at the same time
            faculties: List of faculty names who can teach this course
            ctx: Z3 context for constraint solving
        """
        
    def instance(self, m: z3.ModelRef) -> CourseInstance:
        """
        Create a course instance from a model.
        
        Args:
            m: Z3 model containing assignments
            
        Returns:
            CourseInstance with assigned time, faculty, room, and lab
        """
```

### TimeSlot

Represents a time slot in the schedule.

```python
class TimeSlot:
    def __init__(self, times: List[TimeInstance], lab_index: Optional[int] = None):
        """
        Initialize a time slot.
        
        Args:
            times: List of time instances for this slot
            lab_index: Index of the lab time in the times list, if any
        """
        
    def overlaps(self, other: TimeSlot) -> bool:
        """
        Check if this slot overlaps with another.
        
        Args:
            other: Another time slot to check against
            
        Returns:
            True if the slots overlap, False otherwise
        """
        
    def next_to(self, other: TimeSlot) -> bool:
        """
        Check if slots are logically adjacent.
        
        Args:
            other: Another time slot to check against
            
        Returns:
            True if the slots are adjacent, False otherwise
        """
```

## Output Writers

The scheduler provides two output writers for different formats:

### JSONWriter

```python
from scheduler import JSONWriter

with JSONWriter() as writer:
    for model in scheduler.get_models(limit=1):
        writer.add_schedule(scheduler.courses, model)
```

### CSVWriter

```python
from scheduler import CSVWriter

with CSVWriter() as writer:
    for model in scheduler.get_models(limit=1):
        writer.add_schedule(scheduler.courses, model)
```

## Configuration

### SchedulerConfig

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

### CourseConfig

Configuration for a course.

```python
course = CourseConfig(
    course_id="CS101",
    credits=3,
    room=["Room1"],
    lab=["Lab1"],
    conflicts=["CS102"],
    faculty=["Prof1"]
)
```

### FacultyConfig

Configuration for a faculty member.

```python
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

## Error Handling

The scheduler uses custom exceptions for error handling:

```python
from scheduler import SchedulerError

try:
    scheduler = Scheduler(config, time_slots_config_file)
except SchedulerError as e:
    print(f"Error: {e}")
```

## Example Usage

### Basic Usage

```python
from scheduler import Scheduler, load_from_file

# Load configuration
config = load_from_file("config.json")

# Create scheduler
scheduler = Scheduler(config, "time_slots.json")

# Generate schedules
for model in scheduler.get_models(limit=1, optimize=True):
    schedule = [course.instance(model).__json__() for course in scheduler.courses]
    print(json.dumps(schedule, indent=2))
```

### Advanced Usage

```python
from scheduler import Scheduler, load_from_file, JSONWriter, CSVWriter

# Load configuration
config = load_from_file("config.json")

# Create scheduler
scheduler = Scheduler(config, "time_slots.json")

# Generate multiple schedules with different output formats
print("\nJSON Output:")
with JSONWriter() as writer:
    for model in scheduler.get_models(limit=2, optimize=True):
        writer.add_schedule(scheduler.courses, model)

print("\nCSV Output:")
with CSVWriter() as writer:
    for model in scheduler.get_models(limit=2, optimize=True):
        writer.add_schedule(scheduler.courses, model)

# Analyze schedules
for model in scheduler.get_models(limit=1, optimize=True):
    schedule = [course.instance(model) for course in scheduler.courses]
    
    # Analyze faculty workload
    faculty_workload = {}
    for course in schedule:
        faculty = course.faculty.name
        if faculty not in faculty_workload:
            faculty_workload[faculty] = []
        faculty_workload[faculty].append(course.course.course_id)
    
    print("\nFaculty Workload:")
    for faculty, courses in faculty_workload.items():
        print(f"{faculty}: {', '.join(courses)}")
```

## Best Practices

1. Always use the configuration classes (`SchedulerConfig`, `CourseConfig`, `FacultyConfig`) to create valid configurations
2. Use the `load_from_file` function to load configurations from JSON files
3. Enable optimization only when needed, as it can significantly increase solving time
4. Use appropriate error handling with `SchedulerError`
5. Use the provided writers (`JSONWriter`, `CSVWriter`) for consistent output formatting
6. When analyzing schedules, use the `CourseInstance` objects for detailed information about assignments
