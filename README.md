# Constraint-Sastisfaction Scheduler

### Dependencies

- `python` (version >= 3.12)
- `uv`

### Build / Install

```
$ uv venv
$ source .venv/bin/activate
$ uv sync
```

### Usage

A `scheduler` executable should be in the virtual environment's path

```
Usage: scheduler [OPTIONS] CONFIG

  Generate course schedules using constraint satisfaction solving.

Options:
  -t, --timeslot-config PATH  Path to the time slot configuration file
  -l, --limit INTEGER         Maximum number of models to generate
  -f, --format [csv|json]     Output format
  -o, --output TEXT           Output basename (extension added automatically)
  --optimize                  Enable optimization of preferences (slower)
  --help                      Show this message and exit.
```

### Constraints Modeled

- **Faculty** are assigned to teach specific **Courses**, of which they may have preferences
  - **Faculty** have credit minimums and maximums
  - **Faculty** have unique course maximums
  - **Faculty** have *time-of-day* and *day-of-week* preferences, of which they will not be assigned to any time block outside of their specified window
  - **Faculty** teaching two sections of the same course will have both sections assigned "next to" the other. These courses will also be in the same rooms
- **Courses** may have specific **Lab** assignments or **Room** assignments
- **Rooms** may only be occupied by a single **Course** at any given time
- **Labs** may only be occupied by a single **Course** at any given time

### Output

Output will be listed in the same order as courses are in the JSON file and will include
- Assigned Room
- Assigned Lab (if any needed)
- Comma-delimited list of times

```
CSCI 140.01,Cain,Roddy 140,None,MON 10:00-10:50,TUE 10:00-11:50^,FRI 10:00-10:50
CSCI 140.02,Cain,Roddy 140,None,MON 09:00-09:50,WED 09:00-10:50^,FRI 09:00-09:50
...
...
CSCI 375.01,Hogg,Roddy 147,Linux,MON 11:00-11:50,THU 11:00-12:50^,FRI 11:00-11:50
```

### Contact / Bug Reporting / Feature Requests

Any bugs or feature requests should be filed as issues on this repository.
