#!/usr/bin/env python3
"""
Example demonstrating multiple concurrent client connections to the Course Scheduler API.
This example creates multiple schedule sessions simultaneously and tests concurrent operations.
"""

import json
import requests
import time
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, Any, List
import random

BASE_URL = "http://localhost:8000"
NUM_CLIENTS = 5
SCHEDULES_PER_CLIENT = 3


def load_example_config() -> Dict[str, Any]:
    """Load the example configuration."""
    with open("example_rest_config.json", "r") as f:
        return json.load(f)


class ConcurrentClient:
    """Represents a client that creates and manages a schedule session."""
    
    def __init__(self, client_id: int, config: Dict[str, Any]):
        self.client_id = client_id
        self.config = config
        self.schedule_id = None
        self.session = requests.Session()
        self.session.headers.update({"Content-Type": "application/json"})
    
    def create_session(self) -> bool:
        """Create a new schedule session."""
        try:
            # Modify config slightly for each client to create variety
            modified_config = self.config.copy()
            modified_config["limit"] = SCHEDULES_PER_CLIENT
            modified_config["optimize"] = random.choice([True, False])
            
            response = self.session.post(
                f"{BASE_URL}/submit", 
                json=modified_config, 
                timeout=30
            )
            
            if response.status_code == 200:
                result = response.json()
                self.schedule_id = result["schedule_id"]
                print(f"Client {self.client_id}: Created session {self.schedule_id}")
                return True
            else:
                print(f"Client {self.client_id}: Failed to create session: {response.status_code}")
                return False
                
        except Exception as e:
            print(f"Client {self.client_id}: Error creating session: {e}")
            return False
    
    def get_session_details(self) -> Dict[str, Any]:
        """Get details about the current session."""
        try:
            response = self.session.get(
                f"{BASE_URL}/schedules/{self.schedule_id}/details",
                timeout=5
            )
            if response.status_code == 200:
                return response.json()
            else:
                print(f"Client {self.client_id}: Failed to get details: {response.status_code}")
                return {}
        except Exception as e:
            print(f"Client {self.client_id}: Error getting details: {e}")
            return {}
    
    def generate_schedule(self) -> Dict[str, Any]:
        """Generate the next schedule for this client."""
        try:
            response = self.session.post(
                f"{BASE_URL}/schedules/{self.schedule_id}/next",
                timeout=60
            )
            
            if response.status_code == 200:
                result = response.json()
                print(f"Client {self.client_id}: Generated schedule {result['index'] + 1}")
                return result
            elif response.status_code == 400:
                print(f"Client {self.client_id}: {response.json()['detail']}")
                return {}
            else:
                print(f"Client {self.client_id}: Failed to generate schedule: {response.status_code}")
                return {}
                
        except Exception as e:
            print(f"Client {self.client_id}: Error generating schedule: {e}")
            return {}
    
    def get_schedule_by_index(self, index: int) -> Dict[str, Any]:
        """Get a specific schedule by index."""
        try:
            response = self.session.get(
                f"{BASE_URL}/schedules/{self.schedule_id}/index/{index}",
                timeout=5
            )
            if response.status_code == 200:
                return response.json()
            else:
                print(f"Client {self.client_id}: Failed to get schedule {index}: {response.status_code}")
                return {}
        except Exception as e:
            print(f"Client {self.client_id}: Error getting schedule {index}: {e}")
            return {}
    
    def cleanup(self) -> bool:
        """Clean up the session."""
        try:
            response = self.session.delete(
                f"{BASE_URL}/schedules/{self.schedule_id}/delete",
                timeout=5
            )
            if response.status_code == 200:
                print(f"Client {self.client_id}: Session marked for deletion")
                return True
            else:
                print(f"Client {self.client_id}: Failed to delete session: {response.status_code}")
                return False
        except Exception as e:
            print(f"Client {self.client_id}: Error deleting session: {e}")
            return False


def client_workflow(client_id: int, config: Dict[str, Any]) -> Dict[str, Any]:
    """Complete workflow for a single client."""
    client = ConcurrentClient(client_id, config)
    results = {
        "client_id": client_id,
        "success": False,
        "schedules_generated": 0,
        "schedules_retrieved": 0,
        "errors": []
    }
    
    try:
        # Step 1: Create session
        if not client.create_session():
            results["errors"].append("Failed to create session")
            return results
        
        # Step 2: Get session details
        details = client.get_session_details()
        if details:
            print(f"Client {client_id}: Session limit={details.get('limit')}, optimize={details.get('optimize')}")
        
        # Step 3: Generate schedules
        generated_schedules = []
        for i in range(SCHEDULES_PER_CLIENT):
            schedule = client.generate_schedule()
            if schedule:
                generated_schedules.append(schedule)
                results["schedules_generated"] += 1
                
                # Add some randomness to simulate real-world usage
                time.sleep(random.uniform(0.1, 0.5))
            else:
                break
        
        # Step 4: Retrieve some schedules by index
        for i in range(min(2, len(generated_schedules))):
            retrieved = client.get_schedule_by_index(i)
            if retrieved:
                results["schedules_retrieved"] += 1
        
        # Step 5: Cleanup
        client.cleanup()
        
        results["success"] = True
        print(f"Client {client_id}: Completed successfully - {results['schedules_generated']} schedules generated")
        
    except Exception as e:
        results["errors"].append(str(e))
        print(f"Client {client_id}: Workflow failed: {e}")
    
    return results


def test_health_check() -> bool:
    """Test if the server is healthy."""
    try:
        response = requests.get(f"{BASE_URL}/health", timeout=5)
        if response.status_code == 200:
            health_data = response.json()
            print(f"✓ Server is healthy. Active sessions: {health_data['active_sessions']}")
            return True
        else:
            print(f"✗ Health check failed: {response.status_code}")
            return False
    except requests.exceptions.ConnectionError:
        print("✗ Cannot connect to server. Make sure the server is running on localhost:8000")
        return False
    except Exception as e:
        print(f"✗ Health check error: {e}")
        return False


def main():
    """Run the concurrent client test."""
    print("Testing Course Scheduler API with Multiple Concurrent Clients")
    print("=" * 70)
    
    # Load configuration
    try:
        config = load_example_config()
        print("✓ Loaded example configuration")
    except FileNotFoundError:
        print("✗ Example configuration file not found. Please run this from the project root.")
        return
    except json.JSONDecodeError as e:
        print(f"✗ Invalid JSON in example configuration: {e}")
        return
    
    # Test server health
    print(f"\n1. Testing server health...")
    if not test_health_check():
        return
    
    print(f"\n2. Starting {NUM_CLIENTS} concurrent clients...")
    print(f"   Each client will generate up to {SCHEDULES_PER_CLIENT} schedules")
    
    # Run concurrent clients
    start_time = time.time()
    
    with ThreadPoolExecutor(max_workers=NUM_CLIENTS) as executor:
        # Submit all client workflows
        future_to_client = {
            executor.submit(client_workflow, i, config): i 
            for i in range(NUM_CLIENTS)
        }
        
        # Collect results as they complete
        results = []
        for future in as_completed(future_to_client):
            client_id = future_to_client[future]
            try:
                result = future.result()
                results.append(result)
            except Exception as e:
                print(f"Client {client_id}: Exception occurred: {e}")
                results.append({
                    "client_id": client_id,
                    "success": False,
                    "schedules_generated": 0,
                    "schedules_retrieved": 0,
                    "errors": [str(e)]
                })
    
    end_time = time.time()
    total_time = end_time - start_time
    
    # Print summary
    print(f"\n3. Concurrent test completed in {total_time:.2f} seconds")
    print("=" * 70)
    
    successful_clients = sum(1 for r in results if r["success"])
    total_schedules = sum(r["schedules_generated"] for r in results)
    total_retrieved = sum(r["schedules_retrieved"] for r in results)
    total_errors = sum(len(r["errors"]) for r in results)
    
    print(f"Results Summary:")
    print(f"  - Successful clients: {successful_clients}/{NUM_CLIENTS}")
    print(f"  - Total schedules generated: {total_schedules}")
    print(f"  - Total schedules retrieved: {total_retrieved}")
    print(f"  - Total errors: {total_errors}")
    print(f"  - Average time per client: {total_time/NUM_CLIENTS:.2f} seconds")
    
    # Print individual client results
    print(f"\nIndividual Client Results:")
    for result in results:
        status = "✓" if result["success"] else "✗"
        print(f"  {status} Client {result['client_id']}: "
              f"{result['schedules_generated']} generated, "
              f"{result['schedules_retrieved']} retrieved")
        if result["errors"]:
            for error in result["errors"]:
                print(f"    Error: {error}")
    
    # Final health check
    print(f"\n4. Final health check...")
    test_health_check()
    
    print(f"\n" + "=" * 70)
    print("Concurrent test completed!")


if __name__ == "__main__":
    main() 