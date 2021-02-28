# Constraint-Sastisfaction Scheduler

### Dependencies

- `python` (version >= 3.7) -- only tested with 3.8 and 3.9
- `z3` (can be installed via pip `pip3 install z3-solver`)

### File Architecture

- `scheduler.py` - the entrypoint program
- Other files:
  - `config.py` - basic configuration for generating all possible times
  - `course.py` - Course class definition
  - `room.py`   - Room class definition
  - `time_slot.py` - TimeSlot class definition along with other time resources
  - `lab.py`    - Lab class definition

### Constraints Modeled

- **Faculty** are assigned to teach specific **Courses**
  - **Faculty** have *time-of-day* and *day-of-week* preferences, of which they will not be assigned to any time block outside of their specified window
  - **Faculty** teaching two sections of the same course will have both sections assigned "next to" the other
- **Courses** may have specific **Lab** assignments or **Room** assignments
- **Rooms** may only be occupied by a single **Course** at any given time
- **Labs** may only be occupied by a single **Course** at any given time

### Using the tool

```
[user@hostname] $ python3 scheduler.py <json_file> [limit=10]
```

- `json_file` - a JSON file that adheres to a specific schema
- `limit` - an optional integral value that limits how many schedules are generated

A sample provided json is included. Feel free to edit as necessary.

### Output

Output will be listed in the same order as courses are in the JSON file and will include
- Assigned Room
- Assigned Lab (if any needed)
- Comma-delimited list of times

```
CSCI140.01,Cain,Roddy 140,None,TUE 10:00-11:50,MON 10:00-10:50,FRI 10:00-10:50
CSCI140.02,Cain,Roddy 140,None,WED 09:00-10:50,MON 09:00-09:50,FRI 09:00-09:50
...
...
CSCI375.01,Zoppetti,Roddy 147,Linux,THU 15:00-16:50,MON 15:00-15:50,FRI 15:00-15:50
```

### Contact / Bug Reporting / Feature Requests

Any bugs or feature requests should be filed as issues on this repository.
