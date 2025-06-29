"""
Advanced usage example for the scheduler library.

This example demonstrates how to:
1. Load and use multiple configuration files
2. Generate and display multiple schedules
3. Use different output formats
4. Analyze generated schedules
5. Use different optimizer options
"""

import json
import click
from scheduler import (
    Scheduler,
    load_config_from_file,
    SchedulerConfig,
    TimeSlotConfig,
    JSONWriter,
    CSVWriter,
    OptimizerFlags,
)


def main():
    # Load configurations from files
    config = load_config_from_file(SchedulerConfig, "sample.json")
    time_slot_config = load_config_from_file(TimeSlotConfig, "time_slots.json")

    # Create scheduler instance
    scheduler = Scheduler(config, time_slot_config)

    # Define optimizer options
    optimizer_options = [
        OptimizerFlags.FACULTY_COURSE,
        OptimizerFlags.FACULTY_ROOM,
        OptimizerFlags.FACULTY_LAB,
        OptimizerFlags.SAME_ROOM,
        OptimizerFlags.SAME_LAB,
        OptimizerFlags.PACK_ROOMS,
        OptimizerFlags.PACK_LABS,
    ]

    # Generate multiple schedules with different output formats
    print("\nGenerating schedules...")

    # First, generate JSON output
    print("\nJSON Output:")
    with JSONWriter() as writer:
        for i, model in enumerate(
            scheduler.get_models(limit=2, optimizer_options=optimizer_options)
        ):
            print(f"\nGenerated Schedule {i+1}:")
            writer.add_schedule(model)

    # Then, generate CSV output
    print("\nCSV Output:")
    with CSVWriter() as writer:
        for i, model in enumerate(
            scheduler.get_models(limit=2, optimizer_options=optimizer_options)
        ):
            print(f"\nGenerated Schedule {i+1}:")
            writer.add_schedule(model)

    # Finally, demonstrate how to analyze the schedules
    print("\nSchedule Analysis:")
    for i, model in enumerate(
        scheduler.get_models(limit=1, optimizer_options=optimizer_options)
    ):
        # Analyze faculty workload
        faculty_workload = {}
        for course in model:
            faculty = course.faculty
            if faculty not in faculty_workload:
                faculty_workload[faculty] = []
            faculty_workload[faculty].append(course.course.course_id)

        print("\nFaculty Workload:")
        for faculty, courses in faculty_workload.items():
            print(f"{faculty}: {', '.join(courses)}")

        # Analyze room usage
        room_usage = {}
        for course in model:
            if course.room:
                room = course.room
                if room not in room_usage:
                    room_usage[room] = []
                room_usage[room].append(f"{course.course.course_id} ({course.time})")

        print("\nRoom Usage:")
        for room, courses in room_usage.items():
            print(f"{room}: {', '.join(courses)}")


if __name__ == "__main__":
    main()
