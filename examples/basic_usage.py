"""
Basic usage example for the scheduler library.

This example demonstrates how to:
1. Load configuration from a JSON file
2. Create a scheduler instance
3. Generate and display a schedule
"""

import json
from scheduler import Scheduler, load_from_file

def main():
    # Load configuration from file
    config = load_from_file("sample.json")
    
    # Create scheduler instance
    scheduler = Scheduler(config, "time_slots.json")
    
    # Generate a single schedule
    print("\nGenerating schedule...")
    for model in scheduler.get_models(limit=1, optimize=True):
        # Convert model to schedule using Course.instance()
        schedule = [course.instance(model).__json__() for course in scheduler.courses]
        
        # Print schedule
        print("\nGenerated Schedule:")
        print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()
