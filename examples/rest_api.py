#!/usr/bin/env python3
"""
Test the API using the example configuration file.
"""

import json
import requests
import time

BASE_URL = "http://localhost:8000"


def load_example_config():
    """Load the example configuration."""
    with open("example_rest_config.json", "r") as f:
        return json.load(f)


def main():
    """Test the API with the example configuration."""
    print("Testing Course Scheduler API with example configuration...")
    print("=" * 60)

    # Load example configuration
    try:
        config_data = load_example_config()
        print("✓ Loaded example configuration")
    except FileNotFoundError:
        print(
            "✗ Example configuration file not found. Please run this from the project root."
        )
        return
    except json.JSONDecodeError as e:
        print(f"✗ Invalid JSON in example configuration: {e}")
        return

    # Test health check
    print("\n1. Testing health check...")
    try:
        response = requests.get(f"{BASE_URL}/health", timeout=5)
        if response.status_code == 200:
            print(
                f"✓ Server is healthy. Active sessions: {response.json()['active_sessions']}"
            )
        else:
            print(f"✗ Health check failed: {response.status_code}")
            return
    except requests.exceptions.ConnectionError:
        print(
            "✗ Cannot connect to server. Make sure the server is running on localhost:8000"
        )
        return

    # Submit schedule request
    print("\n2. Submitting schedule request...")
    try:
        response = requests.post(f"{BASE_URL}/submit", json=config_data, timeout=30)
        if response.status_code == 200:
            result = response.json()
            schedule_id = result["schedule_id"]
            print(f"✓ Schedule session created: {schedule_id}")
        else:
            print(f"✗ Failed to create schedule session: {response.status_code}")
            print(f"Error: {response.text}")
            return
    except requests.exceptions.Timeout:
        print("✗ Request timed out. The solver might be taking too long.")
        return

    # Get schedule details
    print("\n3. Getting schedule details...")
    try:
        response = requests.get(
            f"{BASE_URL}/schedules/{schedule_id}/details", timeout=5
        )
        if response.status_code == 200:
            details = response.json()
            print(f"✓ Schedule details retrieved:")
            print(f"  - Limit: {details['limit']}")
            print(f"  - Optimizer options: {details['optimizer_options']}")
            print(f"  - Total generated: {details['total_generated']}")
        else:
            print(f"✗ Failed to get details: {response.status_code}")
    except requests.exceptions.Timeout:
        print("✗ Request timed out")

    # Generate schedules
    print("\n4. Generating schedules...")
    for i in range(min(3, config_data["limit"])):
        print(f"\n   Generating schedule {i + 1}...")
        try:
            response = requests.post(
                f"{BASE_URL}/schedules/{schedule_id}/next", timeout=60
            )
            if response.status_code == 200:
                result = response.json()
                print(f"✓ Generated schedule {result['index'] + 1}:")
                for course in result["schedule"]:
                    print(
                        f"    - {course['course']}: {course['faculty']} in {course.get('room', 'N/A')}"
                    )
            elif response.status_code == 400:
                print(f"✓ {response.json()['detail']}")
                break
            else:
                print(f"✗ Failed to generate schedule: {response.status_code}")
                print(f"Error: {response.text}")
                break
        except requests.exceptions.Timeout:
            print("✗ Request timed out. The solver might be taking too long.")
            break

        time.sleep(1)  # Small delay between requests

    # Test retrieving a specific schedule
    print("\n5. Testing schedule retrieval by index...")
    try:
        response = requests.get(
            f"{BASE_URL}/schedules/{schedule_id}/index/0", timeout=5
        )
        if response.status_code == 200:
            print("✓ Successfully retrieved schedule by index")
        else:
            print(f"✗ Failed to retrieve schedule by index: {response.status_code}")
    except requests.exceptions.Timeout:
        print("✗ Request timed out")

    # Clean up
    print("\n6. Cleaning up...")
    try:
        response = requests.delete(
            f"{BASE_URL}/schedules/{schedule_id}/delete", timeout=5
        )
        if response.status_code == 200:
            print("✓ Schedule session marked for deletion")
        else:
            print(f"✗ Failed to delete session: {response.status_code}")
    except requests.exceptions.Timeout:
        print("✗ Request timed out")

    print("\n" + "=" * 60)
    print("Test completed!")


if __name__ == "__main__":
    main()
