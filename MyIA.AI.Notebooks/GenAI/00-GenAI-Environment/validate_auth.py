
import sys
import os
from pathlib import Path
import requests

# Add shared helpers to path
shared_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../shared'))
if shared_path not in sys.path:
    sys.path.insert(0, shared_path)

from helpers.comfyui_client import create_client, ComfyUIConfig, load_from_env

# Configuration
BASE_URL = "http://localhost:8188"

print(f"Validating ComfyUI Auth at {BASE_URL}")

def test_token(token_name, token_value):
    print(f"\n--- Testing with {token_name} ---")
    print(f"Token: {token_value[:10]}...")
    
    headers = {"Authorization": f"Bearer {token_value}"}
    try:
        response = requests.get(f"{BASE_URL}/system_stats", headers=headers, timeout=5)
        print(f"Status Code: {response.status_code}")
        if response.status_code == 200:
            print("✅ Success!")
            return True
        else:
            print(f"❌ Failed: {response.text}")
            return False
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

# Test 1: Client Auto-Discovery (should use .env or .secrets)
print("\n--- Testing Client Auto-Discovery ---")
try:
    client = create_client()
    print(f"Client loaded token: {client.api_token[:10] if client.api_token else 'None'}...")
    stats = client.get_system_stats()
    print("✅ Success with Auto-Discovery!")
except Exception as e:
    print(f"❌ Failed with Auto-Discovery: {e}")

# Test 2: Explicit check with known hash (sanity check)
# This hash is what we expect the server to use
EXPECTED_HASH = "$2b$12$6707ngR1uLGnTOFpgBRZDunYJ9PrnE7J86byQKxSZ1EQAQwbz/1Zy"
success_hash = test_token("EXPECTED HASH TOKEN", EXPECTED_HASH)

if success_hash:
    print("\n✅ VALIDATION SUCCESSFUL: Authentication is working correctly.")
else:
    print("\n❌ VALIDATION FAILED: Authentication is NOT working.")
