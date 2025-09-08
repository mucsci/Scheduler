# Configuration Guide

## Overview

The Course Constraint Scheduler uses a JSON-based configuration system that defines all aspects of the scheduling problem. This guide covers the complete configuration format, provides examples, and offers best practices for creating effective configurations.

## Configuration Structure

The configuration consists of four main sections:

1. **`config`**: Core scheduling configuration (rooms, labs, courses, faculty)
2. **`time_slot_config`**: Time slot definitions and class patterns
3. **`limit`**: Maximum number of schedules to generate (default: 10)
4. **`optimizer_flags`**: Optimization preferences (optional)

**Validation Features:**
- All configurations are validated using Pydantic models with strict validation
- Cross-reference validation ensures all IDs exist and are unique
- Business logic validation prevents impossible constraints
- Comprehensive error messages for debugging
- Type-safe field validation with custom type definitions

**Type Definitions:**
The configuration system uses several type aliases for validation:
- **`TimeString`**: Time in HH:MM format (00:00-23:59)
- **`TimeRangeString`**: Time range in HH:MM-HH:MM format
- **`Preference`**: Preference score between 0 and 10
- **`Day`**: Day of the week (MON, TUE, WED, THU, FRI)
- **`Room`**, **`Lab`**, **`Course`**, **`Faculty`**: Frozen string types for entity names

## Complete Configuration Example

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
      },
      {
        "course_id": "CS102",
        "credits": 4,
        "room": ["Room B", "Room C"],
        "lab": ["Lab 2"],
        "conflicts": ["CS101"],
        "faculty": ["Dr. Johnson", "Dr. Brown"]
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
          "CS102": 5
        },
        "room_preferences": {
          "Room A": 10,
          "Room B": 7,
          "Room C": 3
        },
        "lab_preferences": {
          "Lab 1": 8,
          "Lab 2": 5
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
      ],
      "TUE": [
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
      },
      {
        "credits": 4,
        "meetings": [
          {
            "day": "TUE",
            "duration": 150,
            "lab": true
          },
          {
            "day": "THU",
            "duration": 150,
            "lab": false
          }
        ]
      }
    ]
  },
  "limit": 10,
  "optimizer_flags": ["faculty_course", "pack_rooms", "same_room"]
}
```

## Configuration Sections

### 1. Core Configuration (`config`)

#### Rooms and Labs

```json
{
  "rooms": ["Room A", "Room B", "Room C"],
  "labs": ["Lab 1", "Lab 2"]
}
```

**Best Practices:**
- Use descriptive names for rooms and labs
- Consider room capacity and equipment requirements
- Group similar facilities together

#### Courses

```json
{
  "course_id": "CS101",
  "credits": 3,
  "room": ["Room A", "Room B"],
  "lab": ["Lab 1"],
  "conflicts": ["CS102"],
  "faculty": ["Dr. Smith", "Dr. Johnson"]
}
```

**Fields:**
- **`course_id`**: Unique identifier (required, string)
- **`credits`**: Credit hours (required, positive integer)
- **`room`**: List of acceptable rooms (required, non-empty list)
- **`lab`**: List of acceptable labs (optional, can be empty)
- **`conflicts`**: Course IDs that cannot be scheduled simultaneously (optional, can be empty)
- **`faculty`**: List of faculty who can teach this course (required, non-empty list)

**Validation Rules:**
- All room names must exist in the `rooms` list
- All lab names must exist in the `labs` list
- All faculty names must exist in the `faculty` list
- All conflict course IDs must exist in the courses list
- Course cannot conflict with itself

**Best Practices:**
- Use consistent course ID naming conventions
- Specify multiple room options for flexibility
- Include all course conflicts to prevent scheduling issues
- Ensure faculty lists are accurate and up-to-date

#### Faculty

```json
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
    "CS102": 5
  },
  "room_preferences": {
    "Room A": 10,
    "Room B": 7
  },
  "lab_preferences": {
    "Lab 1": 8
  }
}
```

**Fields:**
- **`name`**: Faculty member's name (required, unique string)
- **`maximum_credits`**: Maximum credit hours they can teach (required, non-negative integer)
- **`minimum_credits`**: Minimum credit hours they must teach (required, non-negative integer)
- **`unique_course_limit`**: Maximum number of different courses they can teach (required, positive integer)
- **`times`**: Available time slots by day (required, non-empty dict)
- **`course_preferences`**: Course preference scores (0-10, higher = more preferred, optional)
- **`room_preferences`**: Room preference scores (0-10, higher = more preferred, optional)
- **`lab_preferences`**: Lab preference scores (0-10, higher = more preferred, optional)

**Validation Rules:**
- `minimum_credits` cannot be greater than `maximum_credits`
- All course IDs in preferences must exist in the courses list
- All room names in preferences must exist in the rooms list
- All lab names in preferences must exist in the labs list
- Faculty names must be unique across all faculty members

**Time Format:**
- Use 24-hour format: "HH:MM-HH:MM"
- Multiple time ranges can be specified per day
- Example: `["09:00-12:00", "14:00-17:00"]`

**Preference Scoring:**
- **0**: No preference (default)
- **1-3**: Low preference
- **4-6**: Medium preference
- **7-8**: High preference
- **9-10**: Very high preference

**Best Practices:**
- Set realistic credit limits based on faculty workload
- Use preference scores to guide optimization
- Ensure availability times are accurate and comprehensive
- Consider faculty expertise when assigning course preferences

### 2. Time Slot Configuration (`time_slot_config`)

#### Time Blocks

```json
{
  "times": {
    "MON": [
      {
        "start": "09:00",
        "spacing": 60,
        "end": "17:00"
      }
    ],
    "TUE": [
      {
        "start": "08:00",
        "spacing": 60,
        "end": "16:00"
      }
    ]
  }
}
```

**Fields:**
- **`start`**: Start time in "HH:MM" format (required, 24-hour format)
- **`spacing`**: Time slot spacing in minutes (required, positive integer)
- **`end`**: End time in "HH:MM" format (required, must be after start time)

**Validation Rules:**
- End time must be after start time
- Spacing must be a positive integer
- Time format must be valid "HH:MM" (00:00-23:59)

**Best Practices:**
- Use consistent time formats across all days
- Consider standard class durations (50, 75, 150 minutes)
- Account for breaks between classes
- Ensure end time is after start time

#### Class Patterns

```json
{
  "credits": 3,
  "meetings": [
    {
      "day": "MON",
      "duration": 150,
      "lab": false
    }
  ],
  "disabled": false,
}
```

**Fields:**
- **`credits`**: Credit hours for this pattern (required, integer)
- **`meetings`**: List of meeting configurations (required, non-empty list)
- **`disabled`**: Whether this pattern is disabled (optional, default: false)
- **`start_time`**: Specific start time constraint (optional, "HH:MM" format)

**Validation Rules:**
- At least one meeting is required
- No duplicate days in meetings list
- Duration must be positive integer
- Day must be valid weekday (MON, TUE, WED, THU, FRI)
- Start time must be valid "HH:MM" format if provided

**Meeting Configuration:**
- **`day`**: Day of the week (MON, TUE, WED, THU, FRI)
- **`duration`**: Duration in minutes (required)
- **`lab`**: Whether this meeting requires a lab (optional, default: false)

**Best Practices:**
- Match credit hours to actual class time
- Use realistic durations based on course content
- Consider lab requirements for practical courses
- Disable patterns that don't apply to your institution

### 3. Optimization Flags

```json
{
  "optimizer_flags": [
    "faculty_course",
    "faculty_room",
    "pack_rooms",
    "same_room"
  ]
}
```

**Available Flags:**
- **`faculty_course`**: Optimize faculty-course assignments
- **`faculty_room`**: Optimize faculty-room preferences
- **`faculty_lab`**: Optimize faculty-lab preferences
- **`same_room`**: Prefer same room for course sections
- **`same_lab`**: Prefer same lab for course sections
- **`pack_rooms`**: Pack courses into fewer rooms
- **`pack_labs`**: Pack courses into fewer labs

**Best Practices:**
- Start with basic flags like `faculty_course`
- Add room/lab optimization for better resource utilization
- Use packing flags to reduce facility requirements
- Consider the trade-off between optimization and solving time

## Advanced Configuration Examples

### Multi-Day Course Pattern

```json
{
  "credits": 4,
  "meetings": [
    {
      "day": "MON",
      "duration": 75,
      "lab": false
    },
    {
      "day": "WED",
      "duration": 75,
      "lab": false
    },
    {
      "day": "FRI",
      "duration": 150,
      "lab": true
    }
  ]
}
```

### Complex Faculty Availability

```json
{
  "times": {
    "MON": ["09:00-12:00", "14:00-17:00"],
    "TUE": ["08:00-11:00", "13:00-16:00"],
    "WED": ["10:00-17:00"],
    "THU": ["09:00-15:00"],
    "FRI": ["09:00-12:00"]
  }
}
```

### Course with Multiple Room Options

```json
{
  "course_id": "CS201",
  "credits": 4,
  "room": ["Room A", "Room B", "Room C"],
  "lab": ["Lab 1", "Lab 2"],
  "conflicts": ["CS202", "CS203"],
  "faculty": ["Dr. Smith", "Dr. Johnson", "Dr. Brown"]
}
```

## Configuration Validation

### Required Fields

The following fields are required and must be present:

- `config.rooms` (non-empty list)
- `config.courses` (non-empty list)
- `config.faculty` (non-empty list)
- `time_slot_config.times` (non-empty dict)
- `time_slot_config.classes` (non-empty list)

### Field Validation

**Basic Field Validation:**
- **Course IDs**: Must be unique strings
- **Faculty Names**: Must be unique strings
- **Room/Lab Names**: Must exist in the respective lists
- **Time Formats**: Must be valid "HH:MM" format (00:00-23:59)
- **Credit Hours**: Must be positive integers
- **Durations**: Must be positive integers
- **Preference Scores**: Must be integers 0-10
- **Time Ranges**: End time must be after start time
- **Cross-References**: All referenced IDs must exist in their respective lists

**Advanced Validation Rules:**
- **Strict Model Validation**: All models use `extra="forbid"` and `strict=True`
- **Time Block Validation**: End time must be after start time in TimeBlock objects
- **Faculty Credit Validation**: Minimum credits cannot exceed maximum credits
- **Meeting Validation**: No duplicate days allowed in class pattern meetings
- **Business Logic Validation**: All courses must have at least one faculty assignment
- **Uniqueness Validation**: Room names, lab names, and faculty names must be unique
- **Self-Conflict Prevention**: Courses cannot conflict with themselves

### Common Validation Errors

1. **Missing Required Fields**
   ```
   ValidationError: 1 validation error for SchedulerConfig
   rooms: field required
   ```

2. **Invalid Time Format**
   ```
   ValidationError: 1 validation error for FacultyConfig
   times -> MON -> 0: invalid time format; expected HH:MM-HH:MM
   ```

3. **Invalid Reference**
   ```
   ValidationError: 1 validation error for CourseConfig
   faculty -> 0: "Dr. Unknown" is not in faculty list
   ```

4. **Business Logic Violation**
   ```
   ValidationError: Configuration validation errors:
     - Faculty "Dr. Smith" has minimum credits (8) greater than maximum credits (6)
     - Course "CS101" cannot conflict with itself
     - Courses without faculty assignments: ["CS102"]
   ```

5. **Time Validation Error**
   ```
   ValidationError: 1 validation error for TimeBlock
   end: End time must be after start time
   ```

## Performance Considerations

### Configuration Size Impact

- **Small** (< 10 courses, < 5 faculty): Near-instantaneous solving
- **Medium** (10-50 courses, 5-15 faculty): Seconds to minutes
- **Large** (50+ courses, 15+ faculty): May take several minutes

### Optimization Strategies

1. **Reduce Search Space**
   - Limit faculty availability windows
   - Use specific room/lab assignments
   - Minimize course conflicts

2. **Efficient Patterns**
   - Use consistent time slot spacing
   - Group similar course patterns
   - Avoid overly complex meeting schedules

3. **Resource Constraints**
   - Balance room/lab availability
   - Set realistic credit limits
   - Use appropriate optimizer flags

## Troubleshooting

### Common Issues

1. **No Schedules Generated**
   - Check faculty availability overlaps with time slots
   - Verify room/lab assignments are valid
   - Ensure course conflicts don't create impossible constraints

2. **Slow Performance**
   - Reduce the number of courses or faculty
   - Simplify time slot configurations
   - Use fewer optimization flags

3. **Memory Issues**
   - Lower the `limit` parameter
   - Reduce faculty availability windows
   - Simplify course patterns

### Debug Mode

Enable detailed logging to identify configuration issues:

```python
import logging
logging.basicConfig(level=logging.DEBUG)
```

### Configuration Testing

Test configurations incrementally:

1. Start with minimal configuration
2. Add courses one by one
3. Test faculty assignments
4. Verify time slot constraints
5. Add optimization flags gradually

## Best Practices Summary

1. **Start Simple**: Begin with basic configurations and add complexity gradually
2. **Validate Early**: Use the configuration validation to catch errors early
3. **Test Incrementally**: Test small changes before making large modifications
4. **Document Constraints**: Clearly document any special requirements or constraints
5. **Monitor Performance**: Watch solving times and adjust configuration accordingly
6. **Use Preferences**: Leverage preference scoring for better optimization
7. **Plan Resources**: Ensure adequate room/lab availability for all courses
8. **Consider Conflicts**: Carefully plan course conflicts to avoid impossible schedules

## Configuration Templates

### Basic Template

```json
{
  "config": {
    "rooms": ["Room 1", "Room 2"],
    "labs": ["Lab 1"],
    "courses": [
      {
        "course_id": "COURSE101",
        "credits": 3,
        "room": ["Room 1", "Room 2"],
        "lab": ["Lab 1"],
        "conflicts": [],
        "faculty": ["Faculty1"]
      }
    ],
    "faculty": [
      {
        "name": "Faculty1",
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
      "MON": [{"start": "09:00", "spacing": 60, "end": "17:00"}],
      "TUE": [{"start": "09:00", "spacing": 60, "end": "17:00"}],
      "WED": [{"start": "09:00", "spacing": 60, "end": "17:00"}],
      "THU": [{"start": "09:00", "spacing": 60, "end": "17:00"}],
      "FRI": [{"start": "09:00", "spacing": 60, "end": "17:00"}]
    },
    "classes": [
      {
        "credits": 3,
        "meetings": [
          {"day": "MON", "duration": 150, "lab": false}
        ]
      }
    ]
  },
  "limit": 10,
  "optimizer_flags": ["faculty_course"]
}
```

Use this template as a starting point and customize it for your specific needs.
