import requests
import os

print("Environment variables:")
for k, v in os.environ.items():
    if "PROXY" in k.upper():
        print(f"{k}: {v}")

login_url = "http://localhost:1111/login"
api_url = "http://localhost:17861/sdapi/v1/options"

print(f"\nTesting Authentication Flow...")
print(f"1. Login to Service Portal at {login_url}")

session = requests.Session()
credentials_list = [
    ("admin", "changeme"),
    ("admin", "goldman")
]

for user, password in credentials_list:
    print(f"\nTrying credentials: {user} / {password}")
    try:
        response = session.post(login_url, data={"user": user, "password": password}, timeout=5)
        print(f"Login Status: {response.status_code}")
        print(f"Cookies: {session.cookies.get_dict()}")
        
        if response.status_code == 200 and "login" not in response.url and "Log In" not in response.text:
             print("✅ Login successful!")
             
             # Test API on port 17861
             # print(f"\n2a. Accessing API at {api_url} with session cookies...")
             # response = session.get(api_url, timeout=5)
             # print(f"API Status (17861): {response.status_code}")
             
             # Test API on port 1111 (Service Portal) - POST
             api_url_portal = "http://localhost:1111/sdapi/v1/txt2img"
             print(f"\n2b. Accessing API (POST) at {api_url_portal} with session cookies...")
             
             payload = {"prompt": "test", "steps": 1}
             response = session.post(api_url_portal, json=payload, timeout=5)
             print(f"API Status (1111 POST): {response.status_code}")
             
             if response.status_code == 200:
                 print("✅ API POST Access Successful via Portal!")
                 print(f"Response snippet: {response.text[:100]}...")
                 break
             else:
                 print("❌ API POST Access Failed via Portal")
                 print(f"Response snippet: {response.text[:100]}...")
        else:
             print("❌ Login failed")
    except Exception as e:
        print(f"Error: {e}")