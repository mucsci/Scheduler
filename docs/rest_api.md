# REST API Documentation

## Overview

The Course Constraint Scheduler provides a comprehensive REST API for generating academic course schedules. The API is built with FastAPI and supports asynchronous schedule generation, session management, and multiple output formats.

## Base URL

```
http://localhost:8000
```

## Authentication

Currently, the API does not require authentication. All endpoints are publicly accessible.

## API Endpoints

### 1. Submit Schedule Request

**Endpoint:** `POST /submit`

**Description:** Submit a new schedule generation request and create a session.

**Request Body:**
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

**Response:**
```json
{
  "schedule_id": "550e8400-e29b-41d4-a716-446655440000",
  "endpoint": "/schedules/550e8400-e29b-41d4-a716-446655440000"
}
```

**Status Codes:**
- `200`: Successfully created schedule session
- `400`: Invalid configuration
- `500`: Internal server error

**Notes:**
- The `schedule_id` is a UUID that identifies the session
- Use the returned `endpoint` to interact with the session
- The scheduler is initialized asynchronously in the background

### 2. Get Schedule Details

**Endpoint:** `GET /schedules/{schedule_id}/details`

**Description:** Get detailed information about a schedule session.

**Path Parameters:**
- `schedule_id`: UUID of the schedule session

**Response:**
```json
{
  "schedule_id": "550e8400-e29b-41d4-a716-446655440000",
  "config": { /* Original configuration */ },
  "time_slot_config": { /* Original time slot configuration */ },
  "limit": 10,
  "optimizer_flags": ["faculty_course", "pack_rooms"],
  "total_generated": 3
}
```

**Status Codes:**
- `200`: Successfully retrieved session details
- `404`: Schedule session not found
- `500`: Internal server error

**Notes:**
- Returns the original configuration used to create the session
- `total_generated` shows how many schedules have been generated so far

### 3. Get Next Schedule

**Endpoint:** `POST /schedules/{schedule_id}/next`

**Description:** Generate and return the next schedule in the session.

**Path Parameters:**
- `schedule_id`: UUID of the schedule session

**Response:**
```json
{
  "schedule_id": "550e8400-e29b-41d4-a716-446655440000",
  "schedule": [
    {
      "course": "CS101.01",
      "faculty": "Dr. Smith",
      "room": "Room A",
      "lab": null,
      "times": [
        {
          "day": "MON",
          "start": "09:00",
          "duration": 150
        }
      ]
    },
    {
      "course": "CS102.01",
      "faculty": "Dr. Johnson",
      "room": "Room B",
      "lab": null,
      "times": [
        {
          "day": "MON",
          "start": "14:00",
          "duration": 150
        }
      ]
    }
  ],
  "index": 3,
  "total_generated": 4
}
```

**Status Codes:**
- `200`: Successfully generated next schedule
- `400`: All schedules generated or no more available
- `404`: Schedule session not found
- `408`: Request timeout
- `500`: Internal server error

**Notes:**
- Each call generates one new schedule
- `index` is the 0-based index of the returned schedule
- `total_generated` is the total count of schedules generated so far
- The scheduler may take time to generate complex schedules

### 4. Generate All Schedules

**Endpoint:** `POST /schedules/{schedule_id}/generate_all`

**Description:** Start background generation of all remaining schedules.

**Path Parameters:**
- `schedule_id`: UUID of the schedule session

**Response:**
```json
{
  "message": "Started generating all remaining schedules for session 550e8400-e29b-41d4-a716-446655440000",
  "current_count": 3,
  "target_count": 10
}
```

**Status Codes:**
- `200`: Successfully started background generation
- `400`: All schedules already generated
- `404`: Schedule session not found
- `500`: Internal server error

**Notes:**
- This is an asynchronous operation that runs in the background
- Use the count endpoint to monitor progress
- Individual schedules can still be retrieved using the next endpoint
- Background generation can be cancelled by deleting the session

### 5. Get Schedule Count

**Endpoint:** `GET /schedules/{schedule_id}/count`

**Description:** Get the current count of generated schedules and completion status.

**Path Parameters:**
- `schedule_id`: UUID of the schedule session

**Response:**
```json
{
  "schedule_id": "550e8400-e29b-41d4-a716-446655440000",
  "current_count": 7,
  "limit": 10,
  "is_complete": false
}
```

**Status Codes:**
- `200`: Successfully retrieved count
- `404`: Schedule session not found

**Notes:**
- Use this endpoint to monitor progress during background generation
- `is_complete` indicates whether all schedules have been generated

### 6. Get Schedule by Index

**Endpoint:** `GET /schedules/{schedule_id}/index/{index}`

**Description:** Retrieve a previously generated schedule by its index.

**Path Parameters:**
- `schedule_id`: UUID of the schedule session
- `index`: 0-based index of the schedule to retrieve

**Response:**
```json
{
  "schedule_id": "550e8400-e29b-41d4-a716-446655440000",
  "schedule": [ /* Schedule data */ ],
  "index": 2,
  "total_generated": 7
}
```

**Status Codes:**
- `200`: Successfully retrieved schedule
- `404`: Schedule session not found or index out of range
- `500`: Internal server error

**Notes:**
- Index must be between 0 and `total_generated - 1`
- This endpoint is useful for reviewing previously generated schedules

### 7. Delete Schedule Session

**Endpoint:** `DELETE /schedules/{schedule_id}/delete`

**Description:** Mark a schedule session for deletion and cleanup.

**Path Parameters:**
- `schedule_id`: UUID of the schedule session

**Response:**
```json
{
  "message": "Schedule session 550e8400-e29b-41d4-a716-446655440000 marked for deletion"
}
```

**Status Codes:**
- `200`: Successfully marked for deletion
- `404`: Schedule session not found

**Notes:**
- Cleanup is performed asynchronously in the background
- The session will be removed from memory
- Any ongoing background generation will be cancelled

### 8. Immediate Cleanup

**Endpoint:** `POST /schedules/{schedule_id}/cleanup`

**Description:** Immediately clean up a schedule session.

**Path Parameters:**
- `schedule_id`: UUID of the schedule session

**Response:**
```json
{
  "message": "Schedule session 550e8400-e29b-41d4-a716-446655440000 cleaned up"
}
```

**Status Codes:**
- `200`: Successfully cleaned up
- `404`: Schedule session not found

**Notes:**
- This performs immediate cleanup instead of background deletion
- Useful when you need to free resources immediately

### 9. Health Check

**Endpoint:** `GET /health`

**Description:** Check the health status of the API server.

**Response:**
```json
{
  "status": "healthy",
  "active_sessions": 5
}
```

**Status Codes:**
- `200`: Server is healthy

**Notes:**
- `active_sessions` shows the current number of active schedule sessions
- Useful for monitoring and load balancing

## Data Models

### SubmitRequest

```json
{
  "config": "SchedulerConfig",
  "time_slot_config": "TimeSlotConfig",
  "limit": 10,
  "optimizer_flags": ["faculty_course", "pack_rooms"]
}
```

### ScheduleResponse

```json
{
  "schedule_id": "string",
  "schedule": "array of CourseInstance",
  "index": 0,
  "total_generated": 1
}
```

### ScheduleDetails

```json
{
  "schedule_id": "string",
  "config": "SchedulerConfig",
  "time_slot_config": "TimeSlotConfig",
  "limit": 10,
  "optimizer_flags": ["faculty_course"],
  "total_generated": 5
}
```

### ErrorResponse

```json
{
  "error": "error_type",
  "message": "Detailed error message"
}
```

## Configuration Schema

### SchedulerConfig

```json
{
  "rooms": ["string"],
  "labs": ["string"],
  "courses": [
    {
      "course_id": "string",
      "credits": 0,
      "room": ["string"],
      "lab": ["string"],
      "conflicts": ["string"],
      "faculty": ["string"]
    }
  ],
  "faculty": [
    {
      "name": "string",
      "maximum_credits": 0,
      "minimum_credits": 0,
      "unique_course_limit": 0,
      "times": {
        "MON": ["string"],
        "TUE": ["string"],
        "WED": ["string"],
        "THU": ["string"],
        "FRI": ["string"]
      },
      "course_preferences": {
        "course_id": 0
      },
      "room_preferences": {
        "room_name": 0
      },
      "lab_preferences": {
        "lab_name": 0
      }
    }
  ]
}
```

### TimeSlotConfig

```json
{
  "times": {
    "MON": [
      {
        "start": "string",
        "spacing": 0,
        "end": "string"
      }
    ]
  },
  "classes": [
    {
      "credits": 0,
      "meetings": [
        {
          "day": "string",
          "duration": 0,
          "lab": false
        }
      ],
      "disabled": false,
      "start_time": "string"
    }
  ]
}
```

### OptimizerFlags

Available optimization options:
- `"faculty_course"`: Optimize faculty-course assignments
- `"faculty_room"`: Optimize faculty-room preferences
- `"faculty_lab"`: Optimize faculty-lab preferences
- `"same_room"`: Prefer same room for course sections
- `"same_lab"`: Prefer same lab for course sections
- `"pack_rooms"`: Pack courses into fewer rooms
- `"pack_labs"`: Pack courses into fewer labs

## Usage Examples

### Python Client

```python
import requests
import json

# Base URL
base_url = "http://localhost:8000"

# Configuration
config = {
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
                        "lab": False
                    }
                ]
            }
        ]
    },
    "limit": 5,
    "optimizer_flags": ["faculty_course"]
}

# Submit request
response = requests.post(f"{base_url}/submit", json=config)
if response.status_code == 200:
    data = response.json()
    schedule_id = data["schedule_id"]
    print(f"Created session: {schedule_id}")
    
    # Generate schedules
    for i in range(5):
        try:
            schedule_response = requests.post(f"{base_url}/schedules/{schedule_id}/next")
            if schedule_response.status_code == 200:
                schedule_data = schedule_response.json()
                print(f"Generated schedule {i+1}: {len(schedule_data['schedule'])} courses")
            else:
                print(f"Failed to generate schedule: {schedule_response.status_code}")
                break
        except Exception as e:
            print(f"Error: {e}")
            break
    
    # Clean up
    requests.delete(f"{base_url}/schedules/{schedule_id}/delete")
else:
    print(f"Failed to create session: {response.status_code}")
```

### JavaScript/Node.js Client

```javascript
const axios = require('axios');

const baseUrl = 'http://localhost:8000';

async function generateSchedules() {
    try {
        // Configuration
        const config = {
            config: {
                rooms: ["Room A", "Room B"],
                labs: ["Lab 1"],
                courses: [
                    {
                        course_id: "CS101",
                        credits: 3,
                        room: ["Room A"],
                        lab: ["Lab 1"],
                        conflicts: [],
                        faculty: ["Dr. Smith"]
                    }
                ],
                faculty: [
                    {
                        name: "Dr. Smith",
                        maximum_credits: 12,
                        minimum_credits: 6,
                        unique_course_limit: 3,
                        times: {
                            MON: ["09:00-17:00"],
                            TUE: ["09:00-17:00"],
                            WED: ["09:00-17:00"],
                            THU: ["09:00-17:00"],
                            FRI: ["09:00-17:00"]
                        }
                    }
                ]
            },
            time_slot_config: {
                times: {
                    MON: [
                        {
                            start: "09:00",
                            spacing: 60,
                            end: "17:00"
                        }
                    ]
                },
                classes: [
                    {
                        credits: 3,
                        meetings: [
                            {
                                day: "MON",
                                duration: 150,
                                lab: false
                            }
                        ]
                    }
                ]
            },
            limit: 5,
            optimizer_flags: ["faculty_course"]
        };

        // Submit request
        const submitResponse = await axios.post(`${baseUrl}/submit`, config);
        const scheduleId = submitResponse.data.schedule_id;
        console.log(`Created session: ${scheduleId}`);

        // Generate schedules
        for (let i = 0; i < 5; i++) {
            try {
                const scheduleResponse = await axios.post(`${baseUrl}/schedules/${scheduleId}/next`);
                const scheduleData = scheduleResponse.data;
                console.log(`Generated schedule ${i+1}: ${scheduleData.schedule.length} courses`);
            } catch (error) {
                console.log(`Failed to generate schedule: ${error.response?.status}`);
                break;
            }
        }

        // Clean up
        await axios.delete(`${baseUrl}/schedules/${scheduleId}/delete`);
        console.log('Session cleaned up');

    } catch (error) {
        console.error('Error:', error.message);
    }
}

generateSchedules();
```

### cURL Examples

#### Submit Schedule Request
```bash
curl -X POST "http://localhost:8000/submit" \
  -H "Content-Type: application/json" \
  -d '{
    "config": {
      "rooms": ["Room A"],
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
            "MON": ["09:00-17:00"]
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
    "limit": 3,
    "optimizer_flags": ["faculty_course"]
  }'
```

#### Get Next Schedule
```bash
curl -X POST "http://localhost:8000/schedules/{schedule_id}/next"
```

#### Get Schedule Count
```bash
curl -X GET "http://localhost:8000/schedules/{schedule_id}/count"
```

#### Delete Session
```bash
curl -X DELETE "http://localhost:8000/schedules/{schedule_id}/delete"
```

## Error Handling

### Common Error Responses

#### 400 Bad Request
```json
{
  "detail": "Invalid configuration: Faculty 'Dr. Smith' has no available time slots"
}
```

#### 404 Not Found
```json
{
  "detail": "Schedule session not found"
}
```

#### 408 Request Timeout
```json
{
  "detail": "Request timeout"
}
```

#### 500 Internal Server Error
```json
{
  "detail": "Schedule generation failed: Z3 solver error"
}
```

### Error Types

1. **Configuration Errors**: Invalid JSON, missing required fields, constraint violations
2. **Session Errors**: Session not found, session expired
3. **Generation Errors**: Z3 solver failures, constraint conflicts
4. **System Errors**: Memory issues, thread pool exhaustion

## Performance Considerations

### Asynchronous Processing
- Schedule generation is asynchronous and may take time
- Use the count endpoint to monitor progress
- Consider using background generation for large numbers of schedules

### Resource Management
- Sessions consume memory and should be cleaned up
- The server limits concurrent sessions
- Background tasks are automatically cancelled on session deletion

### Optimization
- Use appropriate optimizer flags to reduce solving time
- Limit the number of courses and faculty for better performance
- Consider breaking large problems into smaller sub-problems

## Rate Limiting

Currently, the API does not implement rate limiting. However, consider:
- Limiting concurrent requests per client
- Implementing request throttling for large configurations
- Monitoring server resources during peak usage

## Monitoring and Logging

### Health Monitoring
- Use the `/health` endpoint for basic health checks
- Monitor active session count
- Check server logs for error patterns

### Logging
The server provides detailed logging for:
- Session creation and deletion
- Schedule generation progress
- Error conditions and stack traces
- Performance metrics

## Security Considerations

### Current State
- No authentication required
- All endpoints publicly accessible
- No input validation beyond Pydantic models

### Recommendations
- Implement API key authentication
- Add rate limiting per client
- Validate and sanitize all inputs
- Use HTTPS in production
- Implement request logging and monitoring

## Deployment

### Running the Server
```bash
# Using the installed package
scheduler-server --port 8000

# Or directly with Python
python -m scheduler.server --port 8000
```

### Environment Variables
- `PORT`: Server port (default: 8000)
- `HOST`: Server host (default: 127.0.0.1)
- `LOG_LEVEL`: Logging level (default: INFO)

### Production Considerations
- Use a reverse proxy (nginx, Apache)
- Implement load balancing for multiple instances
- Use process managers (systemd, supervisor)
- Monitor memory usage and implement limits
- Set up proper logging and monitoring

## API Versioning

The current API is version 1.0. Future versions will maintain backward compatibility where possible and provide migration guides for breaking changes.

## Support and Feedback

For issues, questions, or feature requests:
- Check the project documentation
- Review server logs for error details
- Consider the constraint complexity and configuration validity
- Monitor system resources during operation
