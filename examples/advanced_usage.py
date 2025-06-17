"""
Advanced usage example for the scheduler library.

This example demonstrates how to:
1. Load and use multiple configuration files
2. Generate and display multiple schedules
3. Use different output formats
4. Analyze generated schedules
"""

import json
import click
from scheduler import Scheduler, load_from_file, JSONWriter, CSVWriter

def main():
    # Load configuration from file
    config = load_from_file("sample.json")
    
    # Create scheduler instance
    scheduler = Scheduler(config, "time_slots.json")
    
    # Generate multiple schedules with different output formats
    print("\nGenerating schedules...")
    
    # First, generate JSON output
    print("\nJSON Output:")
    with JSONWriter() as writer:
        for i, model in enumerate(scheduler.get_models(limit=2, optimize=True)):
            print(f"\nGenerated Schedule {i+1}:")
            writer.add_schedule(scheduler.courses, model)
    
    # Then, generate CSV output
    print("\nCSV Output:")
    with CSVWriter() as writer:
        for i, model in enumerate(scheduler.get_models(limit=2, optimize=True)):
            print(f"\nGenerated Schedule {i+1}:")
            writer.add_schedule(scheduler.courses, model)
    
    # Finally, demonstrate how to analyze the schedules
    print("\nSchedule Analysis:")
    for i, model in enumerate(scheduler.get_models(limit=1, optimize=True)):
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
        
        # Analyze room usage
        room_usage = {}
        for course in schedule:
            if course.room:
                room = course.room.name
                if room not in room_usage:
                    room_usage[room] = []
                room_usage[room].append(f"{course.course.course_id} ({course.time})")
        
        print("\nRoom Usage:")
        for room, courses in room_usage.items():
            print(f"{room}: {', '.join(courses)}")

if __name__ == "__main__":
    main() 