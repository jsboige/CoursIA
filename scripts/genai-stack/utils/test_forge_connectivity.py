#!/usr/bin/env python3
"""
test_forge_connectivity.py - Script de test de connectivité pour Forge SDXL Turbo (Basic Auth)
"""

import os
import sys
import requests
from pathlib import Path

def test_forge_auth(url="http://localhost:17861", user="admin", password="changeme"):
    """Teste l'authentification Basic Auth sur Forge"""
    print(f"Testing Forge connectivity at {url} with user={user}")
    
    # Support IPv6 pour localhost si nécessaire
    if "localhost" in url:
        # Essayer d'abord IPv6 [::1] car Docker Windows mappe souvent dessus
        try:
            print("Trying IPv6 [::1]...")
            ipv6_url = url.replace("localhost", "[::1]")
            requests.get(ipv6_url, timeout=2)
            url = ipv6_url
            print(f"Using IPv6 URL: {url}")
        except:
            print("IPv6 failed, falling back to provided URL")

    try:
        # Test sans auth (devrait échouer ou rediriger vers login si auth activée)
        print("\n1. Testing without auth...")
        resp_no_auth = requests.get(url, timeout=5, allow_redirects=True)
        print(f"Status: {resp_no_auth.status_code}")
        print(f"Final URL: {resp_no_auth.url}")
        
        if resp_no_auth.status_code == 401:
            print("✅ Protected (401 Unauthorized)")
        elif "login" in resp_no_auth.text.lower() or "service portal" in resp_no_auth.text.lower():
             print("✅ Protected (Login page/Service Portal detected)")
             # Si c'est le Service Portal, on ne peut pas tester l'auth Gradio directement facilement
             # sans bypasser le portail.
             if "1111" in resp_no_auth.url:
                 print("⚠️ Redirected to Service Portal (port 1111). Gradio Auth might be behind it.")
                 return True # On considère que c'est protégé par le portail
        else:
            print("⚠️ Potentially Unprotected (Access allowed)")

        # Test avec auth (si pas redirigé vers portail)
        if "1111" not in resp_no_auth.url:
            print("\n2. Testing with Basic Auth...")
            resp_auth = requests.get(url, auth=(user, password), timeout=5)
            print(f"Status: {resp_auth.status_code}")
            
            if resp_auth.status_code == 200:
                print("✅ Authentication Successful")
                return True
            else:
                print(f"❌ Authentication Failed: {resp_auth.status_code}")
                return False
        
        return True

    except requests.exceptions.ConnectionError:
        print(f"❌ Connection Refused to {url}. Is the service running?")
        return False
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

if __name__ == "__main__":
    # Charger les variables d'env si possible (simulation simple ici)
    # Dans un vrai scénario, on lirait le .env de Forge
    
    # Valeurs par défaut basées sur l'audit
    FORGE_URL = "http://localhost:17861"
    FORGE_USER = "admin"
    FORGE_PASSWORD = "changeme"
    
    success = test_forge_auth(FORGE_URL, FORGE_USER, FORGE_PASSWORD)
    sys.exit(0 if success else 1)