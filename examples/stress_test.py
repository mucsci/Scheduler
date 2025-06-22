#!/usr/bin/env python3
"""
Stress test for the Course Scheduler HTTP API.

This script creates multiple concurrent sessions and generates schedules
to test the server's performance under load.
"""

import asyncio
import time
import json
import requests
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any
import threading
import os

# Configuration
BASE_URL = "http://localhost:8000"
TIMEOUT = 30  # Increased timeout for Z3 operations
MAX_WORKERS = 8  # Increased worker count
SCHEDULES_PER_OPERATION = 10
OPERATIONS_PER_WORKER = 5
TOTAL_OPERATIONS = MAX_WORKERS * OPERATIONS_PER_WORKER


# Load configuration from example_rest_config.json
def load_example_config() -> Dict[str, Any]:
    """Load the example configuration from example_rest_config.json."""
    config_path = os.path.join(
        os.path.dirname(__file__), "..", "example_rest_config.json"
    )
    try:
        with open(config_path, "r") as f:
            full_config = json.load(f)

        # Extract the parts we need for the API
        config = {
            "config": full_config["config"],
            "time_slot_config": full_config["time_slot_config"],
            "limit": full_config.get("limit", 5),
        }
        return config
    except FileNotFoundError:
        raise FileNotFoundError(f"Configuration file not found: {config_path}")
    except json.JSONDecodeError as e:
        raise ValueError(f"Invalid JSON in configuration file: {e}")
    except KeyError as e:
        raise ValueError(f"Missing required key in configuration: {e}")


def health_check() -> Dict[str, Any]:
    """Check server health."""
    try:
        response = requests.get(f"{BASE_URL}/health", timeout=5)
        return response.json()
    except Exception as e:
        return {"error": str(e)}


def create_session(config: Dict[str, Any]) -> str:
    """Create a new schedule session."""
    try:
        response = requests.post(f"{BASE_URL}/submit", json=config, timeout=TIMEOUT)
        response.raise_for_status()
        return response.json()["schedule_id"]
    except Exception as e:
        raise Exception(f"Failed to create session: {e}")


def generate_schedule(session_id: str) -> Dict[str, Any]:
    """Generate a schedule for a session."""
    try:
        response = requests.post(
            f"{BASE_URL}/schedules/{session_id}/next", timeout=TIMEOUT
        )
        response.raise_for_status()
        return response.json()
    except Exception as e:
        raise Exception(f"Failed to generate schedule: {e}")


def delete_session(session_id: str):
    """Delete a session."""
    try:
        response = requests.delete(
            f"{BASE_URL}/schedules/{session_id}/delete", timeout=5
        )
        response.raise_for_status()
    except Exception as e:
        print(f"Warning: Failed to delete session {session_id}: {e}")


def worker_operation(worker_id: int, config: Dict[str, Any]) -> Dict[str, Any]:
    """Single worker operation: create session, generate schedules, delete session."""
    start_time = time.time()
    session_id = None

    try:
        # Create session
        session_id = create_session(config)

        # Generate multiple schedules
        schedules = []
        schedule_times = []
        start = time.time()
        for i in range(SCHEDULES_PER_OPERATION):  # Generate 3 schedules per session
            schedule = generate_schedule(session_id)
            end = time.time()
            schedule_times.append(end - start)
            start = end
            schedules.append(schedule)

        operation_time = time.time() - start_time

        return {
            "worker_id": worker_id,
            "success": True,
            "session_id": session_id,
            "schedules_generated": len(schedules),
            "time": operation_time,
            "schedule_times": schedule_times,
        }

    except Exception as e:
        operation_time = time.time() - start_time
        return {
            "worker_id": worker_id,
            "success": False,
            "error": str(e),
            "session_id": session_id,
            "time": operation_time,
            "schedule_times": [],
        }
    finally:
        # Clean up session
        if session_id:
            delete_session(session_id)


def main():
    """Run the stress test."""
    print("Course Scheduler API Stress Test")
    print("=" * 50)

    # Load example configuration
    try:
        config = load_example_config()
        print("✓ Loaded example configuration from example_rest_config.json")
    except Exception as e:
        print(f"✗ Failed to load configuration: {e}")
        return
    print()

    # 1. Initial health check
    print("1. Initial health check...")
    health = health_check()
    if "error" in health:
        print(f"✗ Server health check failed: {health['error']}")
        return
    print(f"✓ Server is healthy. Active sessions: {health.get('active_sessions', 0)}")
    print()

    # 2. Start stress test
    print("2. Starting stress test...")
    print(f"   - {MAX_WORKERS} threads")
    print(f"   - {OPERATIONS_PER_WORKER} operations per thread")
    print(f"   - Total operations: {TOTAL_OPERATIONS}")
    print(f"   - Schedules per operation: {SCHEDULES_PER_OPERATION}")
    print(f"   - Total schedules: {TOTAL_OPERATIONS * SCHEDULES_PER_OPERATION}")

    start_time = time.time()
    successful_operations = 0
    failed_operations = 0
    operation_times = []
    schedule_times = []
    # Health check counter
    health_check_counter = 0

    # Use ThreadPoolExecutor for concurrent operations
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        # Submit all operations
        future_to_worker = {
            executor.submit(worker_operation, i, config): i
            for i in range(TOTAL_OPERATIONS)
        }

        # Process completed operations
        for future in as_completed(future_to_worker):
            worker_id = future_to_worker[future]

            try:
                result = future.result()
                operation_times.append(result["time"])
                schedule_times.extend(result["schedule_times"])
                if result["success"]:
                    successful_operations += 1
                else:
                    failed_operations += 1
                    print(f"✗ Worker {worker_id} failed: {result['error']}")

                # Progress update
                completed = successful_operations + failed_operations
                if completed % 10 == 0:
                    print(f"Completed {completed}/{TOTAL_OPERATIONS} operations...")

                # Periodic health checks
                health_check_counter += 1
                if health_check_counter % 5 == 0:
                    health = health_check()
                    if "error" in health:
                        print(
                            f"Health check {health_check_counter} error: {health['error']}"
                        )
                    else:
                        print(
                            f"Health check {health_check_counter}: {health.get('active_sessions', 0)} active sessions"
                        )

            except Exception as e:
                failed_operations += 1
                print(f"✗ Worker {worker_id} exception: {e}")

    total_time = time.time() - start_time

    # 3. Results
    print()
    print("3. Stress test completed in {:.2f} seconds".format(total_time))
    print("=" * 50)
    print("Results Summary:")
    print(f"  - Total operations: {TOTAL_OPERATIONS}")
    print(f"  - Successful: {successful_operations}")
    print(f"  - Failed: {failed_operations}")
    print(f"  - Success rate: {(successful_operations / TOTAL_OPERATIONS) * 100:.1f}%")
    print(f"  - Operations per second: {TOTAL_OPERATIONS / total_time:.1f}")
    print(
        f"  - Schedules per second: {TOTAL_OPERATIONS * SCHEDULES_PER_OPERATION / total_time:.1f}"
    )

    if operation_times:
        avg_time = sum(operation_times) / len(operation_times)
        print(f"  - Average time per operation: {avg_time * 1000:.1f}ms")
        print(f"  - Min time per operation: {min(operation_times) * 1000:.1f}ms")
        print(f"  - Max time per operation: {max(operation_times) * 1000:.1f}ms")

    if schedule_times:
        avg_time = sum(schedule_times) / len(schedule_times)
        print(f"  - Average time per schedule: {avg_time * 1000:.1f}ms")
        print(f"  - Min time per schedule: {min(schedule_times) * 1000:.1f}ms")
        print(f"  - Max time per schedule: {max(schedule_times) * 1000:.1f}ms")

    print()

    # 4. Final health check
    print("4. Final health check...")
    health = health_check()
    if "error" in health:
        print(f"✗ Server health check failed: {health['error']}")
    else:
        print(
            f"✓ Server is healthy. Active sessions: {health.get('active_sessions', 0)}"
        )

    print()
    print("=" * 50)
    print("Stress test completed!")


if __name__ == "__main__":
    main()
