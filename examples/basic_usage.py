"""
Basic usage example for the scheduler library.

This example demonstrates how to:
1. Load configuration from JSON files
2. Create a scheduler instance
3. Generate and display a schedule
"""

import json
from scheduler import Scheduler, load_config_from_file, SchedulerConfig, TimeSlotConfig


def main():
    # Load configurations from files
    config = load_config_from_file(SchedulerConfig, "sample.json")
    time_slot_config = load_config_from_file(TimeSlotConfig, "time_slots.json")

    # Create scheduler instance
    scheduler = Scheduler(config, time_slot_config)

    # Generate a single schedule
    print("\nGenerating schedule...")
    for model in scheduler.get_models(limit=1, optimize=True):
        schedule = [course_instance.as_json() for course_instance in model]

        # Print schedule
        print("\nGenerated Schedule:")
        print(json.dumps(schedule, indent=2))


if __name__ == "__main__":
    main()
