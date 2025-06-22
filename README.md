# Course Scheduler

A constraint satisfaction solver for generating course schedules using Z3 theorem prover.

## Features

- **Constraint Satisfaction**: Uses Z3 theorem prover for optimal schedule generation
- **Faculty Preferences**: Supports faculty course, room, and lab preferences with granular optimization
- **Room & Lab Assignment**: Intelligent assignment of rooms and labs with packing optimization
- **Conflict Resolution**: Handles course conflicts and scheduling constraints
- **HTTP API**: RESTful API for schedule generation with session management
- **Concurrent Processing**: Thread pool for handling multiple Z3 operations simultaneously
- **Performance Optimized**: Aggressive Z3 settings for faster solving

## Installation

1. Clone the repository:
```bash
git clone <repository-url>
cd Sched
```

2. Install dependencies:
```bash
pip install -e .
```

## Usage

### Command Line Interface

Generate schedules using the CLI:

```bash
# Using the installed script
scheduler --config config.json --time-slots time_slots.json --limit 10

# Or directly with Python
python -m scheduler.main --config config.json --time-slots time_slots.json --limit 10
```

### Python API

```python
from scheduler import Scheduler, load_config_from_file, SchedulerConfig, TimeSlotConfig, OptimizerFlags

# Load configurations
config = load_config_from_file(SchedulerConfig, "config.json")
time_slot_config = load_config_from_file(TimeSlotConfig, "time_slots.json")

# Create scheduler and generate schedules
scheduler = Scheduler(config, time_slot_config)

# Use specific optimizer options
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
        print(f"  Room: {course_instance.room if course_instance.room else 'None'}")
        print(f"  Lab: {course_instance.lab if course_instance.lab else 'None'}")
        print(f"  Time: {course_instance.time}")
```

### HTTP API Server

Start the HTTP API server:

```bash
# Using the installed script with default settings
scheduler-server

# With custom configuration
scheduler-server --port 8000 --host 0.0.0.0 --log-level info --workers 6

# Or directly with Python
python -m scheduler.server --port 8000 --workers 6
```

#### Server Options

- `--port, -p`: Port to run the server on (default: 8000)
- `--host, -h`: Host to bind the server to (default: 0.0.0.0)
- `--log-level, -l`: Log level (debug, info, warning, error, critical) (default: info)
- `--workers, -w`: Number of Z3 worker threads for concurrent processing (default: 4)

#### Performance Tuning

The server uses a thread pool to handle Z3 operations concurrently. For optimal performance:

- **CPU-bound workloads**: Set workers to number of CPU cores
- **I/O-bound workloads**: Set workers to 2-4x number of CPU cores
- **Memory-constrained**: Reduce workers to avoid memory pressure

Example for high-performance server:
```bash
scheduler-server --workers 8 --log-level warning
```

### API Endpoints

#### Submit Schedule Request
```http
POST /submit
Content-Type: application/json

{
  "config": {
    "courses": [...],
    "faculty": [...],
    "rooms": [...],
    "labs": [...]
  },
  "time_slot_config": {
    "start_time": "08:00",
    "end_time": "18:00",
    "slot_duration": 60,
    "break_duration": 15
  },
  "limit": 10,
  "optimizer_options": [
    "faculty_course",
    "faculty_room",
    "faculty_lab",
    "same_room",
    "same_lab",
    "pack_rooms",
    "pack_labs"
  ]
}
```

#### Generate Next Schedule
```http
POST /schedules/{schedule_id}/next
```

#### Get Schedule by Index
```http
GET /schedules/{schedule_id}/index/{index}
```

#### Get Schedule Details
```http
GET /schedules/{schedule_id}/details
```

#### Delete Schedule Session
```http
DELETE /schedules/{schedule_id}/delete
```

#### Health Check
```http
GET /health
```

## Configuration

### Course Configuration (`config.json`)

```json
{
  "courses": [
    {
      "course_id": "CS101",
      "credits": 3,
      "faculty": ["Dr. Smith"],
      "room": ["Room A", "Room B"],
      "lab": ["Lab 1"],
      "conflicts": []
    }
  ],
  "faculty": [
    {
      "name": "Dr. Smith",
      "maximum_credits": 12,
      "minimum_credits": 6,
      "unique_course_limit": 2,
      "course_preferences": {"CS101": 5},
      "room_preferences": {"Room A": 5},
      "lab_preferences": {"Lab 1": 5},
      "times": {
        "MON": ["09:00-12:00", "14:00-17:00"],
        "TUE": ["09:00-12:00", "14:00-17:00"]
      }
    }
  ],
  "rooms": ["Room A", "Room B"],
  "labs": ["Lab 1", "Lab 2"]
}
```

### Time Slot Configuration (`time_slots.json`)

```json
{
  "start_time": "08:00",
  "end_time": "18:00",
  "slot_duration": 60,
  "break_duration": 15
}
```

## Testing

### Basic API Test
```bash
python examples/rest_api.py
```

### Concurrent Client Test
```bash
python examples/concurrent_clients.py
```

### Stress Test
```bash
python examples/stress_test.py
```

The stress test creates multiple concurrent sessions and generates schedules to test server performance under load.

## Performance Optimizations

### Z3 Configuration
The scheduler uses aggressive Z3 settings for faster solving:

- **Parallel solving**: Enabled with configurable thread count
- **Timeouts**: 30-second timeout per solve operation
- **Resource limits**: Optimized memory and CPU usage
- **Caching**: Extensive caching of slot relationships and simplifications

### Thread Pool
- **Concurrent Z3 operations**: Multiple schedule generations can run simultaneously
- **Configurable workers**: Adjust based on system resources
- **Non-blocking API**: Async endpoints with thread pool execution

### Memory Management
- **Session cleanup**: Automatic cleanup of completed sessions
- **Resource limits**: Z3 resource limits prevent memory exhaustion
- **Garbage collection**: Aggressive GC settings for faster memory cleanup

## Architecture

```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   HTTP Client   │───▶│  FastAPI Server │───▶│  Thread Pool    │
└─────────────────┘    └─────────────────┘    └─────────────────┘
                                │                       │
                                ▼                       ▼
                       ┌─────────────────┐    ┌─────────────────┐
                       │ Session Manager │    │   Z3 Solver     │
                       └─────────────────┘    └─────────────────┘
```

## Development

### Project Structure
```
src/scheduler/
├── __init__.py
├── main.py              # CLI entry point
├── server.py            # HTTP API server
├── scheduler.py         # Core scheduler logic
├── config.py            # Configuration models
├── time_slot_generator.py
├── logging.py
├── models/              # Data models
└── writers/             # Output writers
```

## Optimizer Options

The scheduler supports various optimization strategies that can be enabled individually:

- **`faculty_course`**: Optimize for faculty course preferences (1-5 scale)
- **`faculty_room`**: Optimize for faculty room preferences (1-5 scale)
- **`faculty_lab`**: Optimize for faculty lab preferences (1-5 scale)
- **`same_room`**: Prefer same faculty to use same rooms
- **`same_lab`**: Prefer same faculty to use same labs
- **`pack_rooms`**: Pack courses into fewer rooms when possible
- **`pack_labs`**: Pack courses into fewer labs when possible

### Faculty Preferences

Faculty can now specify preferences for courses, rooms, and labs separately:

- **`course_preferences`**: Map of course IDs to preference values (1-5, where 5 is strongly preferred)
- **`room_preferences`**: Map of room names to preference values (1-5, where 5 is strongly preferred)
- **`lab_preferences`**: Map of lab names to preference values (1-5, where 5 is strongly preferred)
