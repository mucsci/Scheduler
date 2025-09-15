from collections import Counter
from functools import cache
from itertools import product

from .config import TimeBlock, TimeSlotConfig
from .models import Day, Duration, TimeInstance, TimePoint, TimeSlot


class TimeSlotGenerator:
    """
    Generator for time slots based on configuration.

    This class generates all possible time slot combinations for courses
    based on the provided TimeSlotConfig, ensuring valid scheduling patterns
    and constraints are met.
    """

    def __init__(self, config: TimeSlotConfig):
        """
        Initialize the TimeSlotGenerator.

        **Args:**
        - config: The TimeSlotConfig containing time blocks and class patterns
        """
        self.config = config

    def _parse_time(self, time_str: str) -> int:
        """Convert time string (HH:MM) to minutes since midnight."""
        hour, minute = map(int, time_str.split(":"))
        return hour * 60 + minute

    def _generate_day_slots(
        self,
        day: str,
        duration: int,
        time_blocks: list[TimeBlock],
        start_time: str | None = None,
    ) -> list[TimeInstance]:
        """Generate all possible time slots for a given day and duration."""
        day_slots = []
        for block in time_blocks:
            block_start = self._parse_time(block.start)
            block_end = self._parse_time(block.end)

            if start_time:
                pattern_start = self._parse_time(start_time)
                if pattern_start < block_start or pattern_start + duration > block_end:
                    continue
                block_start = pattern_start

            current_start = block_start
            while current_start + duration <= block_end:
                time_instance = TimeInstance(
                    day=Day[day],
                    start=TimePoint.make_from(current_start // 60, current_start % 60),
                    duration=Duration(duration=duration),
                )
                day_slots.append(time_instance)
                current_start += block.spacing

        return day_slots

    def _validate_time_combination(self, time_combination: list[TimeInstance]) -> bool:
        """
        Validate a time combination by checking:
        1. No overlapping meetings on the same day
        2. Sufficient overlap between different days
        Returns True if the combination is valid.
        """
        for i, t1 in enumerate(time_combination):
            for j, t2 in enumerate(time_combination):
                if i != j:
                    # Check for same-day overlaps
                    if t1.day == t2.day:
                        if t1.start < t2.start + t2.duration and t2.start < t1.start + t1.duration:
                            return False
                    # Check for sufficient overlap between different days
                    else:
                        t1_start = t1.start
                        t1_end = t1_start + t1.duration
                        t2_start = t2.start
                        t2_end = t2_start + t2.duration

                        overlap_start = max(t1_start, t2_start)
                        overlap_end = min(t1_end, t2_end)
                        overlap_minutes = overlap_end - overlap_start

                        if overlap_minutes < Duration(duration=self.config.min_time_overlap):
                            return False
        return True

    def _has_matching_start_times(self, time_combination: list[TimeInstance]) -> bool:
        """Check if at least two meetings start at the same time."""
        if len(time_combination) < 2:
            return True
        start_times = Counter(t.start.timepoint for t in time_combination)
        return max(start_times.values()) >= 2

    @cache
    def time_slots(self, credits: int) -> list[TimeSlot]:
        """
        Generate all possible time slots for a given credit level.

        **Args:**
        - credits: The course credit count to generate time slots for

        **Returns:**
        A list of TimeSlot objects
        """
        # Find matching class patterns for the requested credits
        matching_patterns = [p for p in self.config.classes if p.credits == credits and not p.disabled]
        if not matching_patterns:
            return []

        result = []
        for pattern in matching_patterns:
            # Generate all possible time slots for each meeting in the pattern
            meeting_slots: list[list[TimeInstance]] = []
            for meeting in pattern.meetings:
                day_slots = self._generate_day_slots(
                    day=meeting.day,
                    duration=meeting.duration,
                    time_blocks=self.config.times.get(meeting.day, []),
                    start_time=pattern.start_time,
                )
                meeting_slots.append(day_slots)

            # Generate and validate all possible combinations
            for time_combination_tuple in product(*meeting_slots):
                time_combination = list(time_combination_tuple)
                # Skip if there are same-day overlaps or insufficient overlap between days
                if not self._validate_time_combination(time_combination):
                    continue

                # Skip if there aren't at least two meetings starting at the same time
                if not self._has_matching_start_times(time_combination):
                    continue

                # Find lab index if any
                lab_index = None
                for i, meeting in enumerate(pattern.meetings):
                    if meeting.lab:
                        lab_index = i
                        break

                # Create TimeSlot with this combination
                slot = TimeSlot(
                    times=list(time_combination),
                    lab_index=lab_index,
                    max_time_gap=Duration(duration=self.config.max_time_gap),
                )
                if slot not in result:
                    result.append(slot)

        return result
