from typing import Iterable, List, Dict, Tuple, Optional
import json
import itertools
from datetime import datetime, timedelta
from pydantic import BaseModel, Field
from day import Day
from time_slot import Duration, TimeInstance, TimePoint, TimeSlot


class TimeBlock(BaseModel):
    start: str
    spacing: int
    end: str


class Meeting(BaseModel):
    day: str
    duration: int
    lab: Optional[bool] = Field(default=False)


class ClassPattern(BaseModel):
    credits: int
    meetings: List[Meeting]
    disabled: Optional[bool] = Field(default=False)
    start_time: Optional[str] = Field(default=None)


class TimeSlotConfig(BaseModel):
    times: Dict[str, List[TimeBlock]]
    classes: List[ClassPattern]


def parse_time(time_str: str) -> Tuple[int, int]:
    """Parse time string like '08:00' into (hour, minute) tuple"""
    parts = time_str.split(':')
    return int(parts[0]), int(parts[1])


def time_to_minutes(hour: int, minute: int) -> int:
    """Convert time to minutes since midnight"""
    return hour * 60 + minute


def minutes_to_time(minutes: int) -> Tuple[int, int]:
    """Convert minutes since midnight to (hour, minute)"""
    return minutes // 60, minutes % 60


def generate_valid_start_times(day_time_blocks: List[TimeBlock], meeting_duration: int, start_time: Optional[str] = None) -> List[str]:
    """Generate all valid start times for a day based on time blocks and meeting duration"""
    start_times = []
    min_start_minutes = None
    
    if start_time:
        min_start_hour, min_start_minute = parse_time(start_time)
        min_start_minutes = time_to_minutes(min_start_hour, min_start_minute)
        
    for time_block in day_time_blocks:
        start_hour, start_minute = parse_time(time_block.start)
        end_hour, end_minute = parse_time(time_block.end)
        spacing = time_block.spacing
        
        start_minutes = time_to_minutes(start_hour, start_minute)
        end_minutes = time_to_minutes(end_hour, end_minute)
        
        # Start from the later of block start time or minimum start time
        current_minutes = start_minutes
        if min_start_minutes is not None:
            current_minutes = max(start_minutes, min_start_minutes)
            # Align to the next valid spacing interval if needed
            if current_minutes > start_minutes:
                spacing_offset = (current_minutes - start_minutes) % spacing
                if spacing_offset != 0:
                    current_minutes += spacing - spacing_offset

        while current_minutes + meeting_duration <= end_minutes:  # Ensure full meeting duration fits
            hour, minute = minutes_to_time(current_minutes)
            start_times.append(f"{hour:02d}:{minute:02d}")
            current_minutes += spacing
    
    return sorted(list(set(start_times)))


def times_overlap(time1: str, duration1: int, time2: str, duration2: int) -> bool:
    """Check if two time periods have any overlap"""
    h1, m1 = parse_time(time1)
    h2, m2 = parse_time(time2)
    
    start1 = time_to_minutes(h1, m1)
    end1 = start1 + duration1
    
    start2 = time_to_minutes(h2, m2)
    end2 = start2 + duration2
    
    # Two periods overlap if start1 < end2 AND start2 < end1
    return start1 < end2 and start2 < end1


def check_110_minute_alignment(combination: List[Tuple], config: TimeSlotConfig, start_time: Optional[str] = None, max_diff: int = 10) -> bool:
    """Check if 110-minute meetings are properly aligned with other meetings"""
    # Early exit if no 110-minute meetings
    has_110_minute = any(meeting.duration == 110 for idx, meeting, meeting_start_time in combination)
    if not has_110_minute:
        return True
    
    # Cache meeting times computation for efficiency
    if not hasattr(check_110_minute_alignment, '_cached_meeting_times'):
        check_110_minute_alignment._cached_meeting_times = {}
    
    cache_key = (tuple(sorted(config.times.keys())), tuple(sorted(
        meeting.duration for class_pattern in config.classes 
        if not class_pattern.disabled 
        for meeting in class_pattern.meetings
    )), start_time)
    
    if cache_key not in check_110_minute_alignment._cached_meeting_times:
        # Get all possible meeting start and end times from all days
        all_meeting_times = set()
        all_meeting_end_times = set()
        
        # Collect all unique meeting durations from the configuration
        all_durations = set()
        for class_pattern in config.classes:
            if not class_pattern.disabled:
                for meeting in class_pattern.meetings:
                    all_durations.add(meeting.duration)
        
        for day, time_blocks in config.times.items():
            for duration in all_durations:
                day_start_times = generate_valid_start_times(time_blocks, duration, start_time)
                for start_time_str in day_start_times:
                    start_minutes = time_to_minutes(*parse_time(start_time_str))
                    end_minutes = start_minutes + duration
                    end_hour, end_minute = minutes_to_time(end_minutes)
                    
                    all_meeting_times.add(start_time_str)
                    all_meeting_end_times.add(f"{end_hour:02d}:{end_minute:02d}")
        
        check_110_minute_alignment._cached_meeting_times[cache_key] = (all_meeting_times, all_meeting_end_times)
    
    all_meeting_times, all_meeting_end_times = check_110_minute_alignment._cached_meeting_times[cache_key]
    
    # Check each 110-minute meeting for alignment
    for idx, meeting, meeting_start_time in combination:
        if meeting.duration == 110:
            # Calculate end time for this 110-minute meeting
            start_minutes = time_to_minutes(*parse_time(meeting_start_time))
            end_minutes = start_minutes + 110
            end_hour, end_minute = minutes_to_time(end_minutes)
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            
            # Check if start/end times are within max_diff minutes of any meeting start/end times
            start_aligned = any(abs(start_minutes - time_to_minutes(*parse_time(t))) <= max_diff 
                              for t in all_meeting_times)
            end_aligned = any(abs(end_minutes - time_to_minutes(*parse_time(t))) <= max_diff
                            for t in all_meeting_end_times)
            
            if not (start_aligned or end_aligned):
                return False
    
    return True


def generate_time_combinations(meetings: List[Meeting], config: TimeSlotConfig, start_time: Optional[str] = None) -> List[List[Dict]]:
    """Generate all valid time combinations for a class pattern with optimizations"""
    # Early exit for empty meetings
    if not meetings:
        return []
    
    # Group meetings by duration to handle constraints
    duration_groups = {}
    for i, meeting in enumerate(meetings):
        duration = meeting.duration
        if duration not in duration_groups:
            duration_groups[duration] = []
        duration_groups[duration].append((i, meeting))
    
    # Generate possible start times for each meeting with early filtering
    meeting_times = []
    for i, meeting in enumerate(meetings):
        day = meeting.day
        if day in config.times:
            valid_times = generate_valid_start_times(config.times[day], meeting.duration, start_time)
            if not valid_times:  # Early exit if no valid times
                return []
            meeting_times.append([(i, meeting, time) for time in valid_times])
        else:
            return []  # Early exit if day not found
    
    # Early exit if any meeting has no valid times
    if any(not times for times in meeting_times):
        return []
    
    # Calculate total combinations and apply heuristic filtering
    total_combinations = 1
    for times in meeting_times:
        total_combinations *= len(times)
    
    # If too many combinations, apply pre-filtering heuristics
    if total_combinations > 10000:  # Threshold for expensive computation
        # Reduce search space by limiting start times for non-critical meetings
        for i, times in enumerate(meeting_times):
            if len(times) > 20:  # Limit to reasonable number
                # Keep every nth element to maintain diversity
                step = max(1, len(times) // 15)
                meeting_times[i] = times[::step]
    
    # Generate all combinations
    all_combinations = list(itertools.product(*meeting_times))
    
    # Filter combinations based on constraints with optimized checking
    valid_combinations = []
    for combination in all_combinations:
        # Quick validation checks first
        
        # Check constraints efficiently
        # First, check that all meetings with the same duration start at the same time
        duration_start_times = {}
        valid = True
        for idx, meeting, combination_start_time in combination:
            duration = meeting.duration
            if duration not in duration_start_times:
                duration_start_times[duration] = combination_start_time
            elif duration_start_times[duration] != combination_start_time:
                # Same duration meetings must start at the same time
                valid = False
                break
        
        if not valid:
            continue
        
        if len(duration_groups) > 1:
            # Mixed durations - check overlap constraints
            for i in range(len(combination)):
                for j in range(i + 1, len(combination)):
                    meeting1 = combination[i]
                    meeting2 = combination[j]
                    
                    if meeting1[1].duration != meeting2[1].duration:
                        # Different durations must overlap
                        if not times_overlap(meeting1[2], meeting1[1].duration, 
                                           meeting2[2], meeting2[1].duration):
                            valid = False
                            break
                
                if not valid:
                    break
        
        if not valid:
            continue
        
        # Check 110-minute alignment constraint (most expensive check last)
        if not check_110_minute_alignment(combination, config, start_time):
            continue
        
        # Convert to the format we need
        time_instances = []
        for idx, meeting, combination_start_time in combination:
            time_instances.append({
                'day': meeting.day,
                'time': combination_start_time,
                'duration': meeting.duration,
                'lab': meeting.lab or False
            })
        valid_combinations.append(time_instances)
    
    return valid_combinations


def time_slots(credits: int) -> Iterable[TimeSlot]:
    """
    returns all possible time slots generated from JSON configuration with caching
    """
    # Add function-level cache to avoid recomputing
    if not hasattr(time_slots, '_cache'):
        time_slots._cache = {}
    
    if credits in time_slots._cache:
        yield from time_slots._cache[credits]
        return
    
    with open('time_slots.json', 'r') as f:
        raw_config = json.load(f)
    
    # Parse with Pydantic for validation and type safety
    config = TimeSlotConfig(**raw_config)
    
    generated_slots = []
    
    # Find all class patterns for the requested credits
    for class_pattern in config.classes:
        if class_pattern.disabled:
            continue
        if class_pattern.credits == credits:
            meetings = class_pattern.meetings
            
            # Generate all valid time combinations for this pattern
            time_combinations = generate_time_combinations(meetings, config, class_pattern.start_time)
            
            for time_combination in time_combinations:
                time_instances = []
                lab_index = None
                
                for i, time_config in enumerate(time_combination):
                    day = Day[time_config['day']]
                    hour, minute = parse_time(time_config['time'])
                    time_point = TimePoint.make_from(hour, minute)
                    duration = Duration(time_config['duration'])
                    
                    time_instance = TimeInstance(day, time_point, duration)
                    time_instances.append(time_instance)
                    
                    # Track lab index if this is a lab session
                    if time_config.get('lab', False):
                        lab_index = i
                
                if lab_index is not None:
                    slot = TimeSlot(time_instances, lab_index=lab_index)
                else:
                    slot = TimeSlot(time_instances)
                
                generated_slots.append(slot)
                yield slot
    
    # Cache the results for future calls
    time_slots._cache[credits] = generated_slots
