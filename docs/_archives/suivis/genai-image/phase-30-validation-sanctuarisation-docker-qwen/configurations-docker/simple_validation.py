#!/usr/bin/env python3
"""
Script simple de validation du système ComfyUI Qwen
"""

import requests
import json
import time
from datetime import datetime

# Configuration
COMFYUI_URL = "http://localhost:8188"
USERNAME = "admin"
PASSWORD = "rZDS3XQa/8!v9L"
BEARER_TOKEN = "$2b$12$NErya5UooY9bJnscVc/ec.hpVDX.nYM86/88bXIkF/hh2VeKRvU5ka"

def test_web_access():
    """Test accès web"""
    print("TEST 1: ACCÈS WEB")
    try:
        response = requests.get(COMFYUI_URL, timeout=10)
        if response.status_code == 200:
            print("✅ Accès web: SUCCÈS")
            return True
        else:
            print(f"❌ Accès web: ÉCHEC (code {response.status_code})")
            return False
    except Exception as e:
        print(f"❌ Accès web: ÉCHEC ({str(e)})")
        return False

def test_web_login():
    """Test login web"""
    print("\nTEST 2: LOGIN WEB")
    session = requests.Session()
    try:
        login_data = {'username': USERNAME, 'password': PASSWORD}
        response = session.post(
            COMFYUI_URL + "/login",
            data=login_data,
            headers={'Content-Type': 'application/x-www-form-urlencoded'},
            timeout=10,
            allow_redirects=False
        )
        
        if response.status_code in [302, 303]:
            print("✅ Login web: SUCCÈS")
            return session
        else:
            print(f"❌ Login web: ÉCHEC (code {response.status_code})")
            return None
    except Exception as e:
        print(f"❌ Login web: ÉCHEC ({str(e)})")
        return None

def test_api_auth():
    """Test API authentification"""
    print("\nTEST 3: API AUTHENTIFICATION")
    headers = {'Authorization': f'Bearer {BEARER_TOKEN}'}
    try:
        response = requests.get(COMFYUI_URL + "/system_stats", headers=headers, timeout=10)
        if response.status_code == 200:
            print("✅ API authentification: SUCCÈS")
            return True
        else:
            print(f"❌ API authentification: ÉCHEC (code {response.status_code})")
            return False
    except Exception as e:
        print(f"❌ API authentification: ÉCHEC ({str(e)})")
        return False

def test_gpu():
    """Test GPU"""
    print("\nTEST 4: VALIDATION GPU")
    headers = {'Authorization': f'Bearer {BEARER_TOKEN}'}
    try:
        response = requests.get(COMFYUI_URL + "/system_stats", headers=headers, timeout=10)
        if response.status_code == 200:
            data = response.json()
            if 'devices' in data and data['devices']:
                device = data['devices'][0]
                if 'RTX' in device.get('name', ''):
                    print("✅ GPU RTX détecté: SUCCÈS")
                    return True
                else:
                    print("⚠️ GPU détecté mais pas RTX")
                    return False
            else:
                print("❌ GPU non détecté")
                return False
        else:
            print(f"❌ GPU validation: ÉCHEC (code {response.status_code})")
            return False
    except Exception as e:
        print(f"❌ GPU validation: ÉCHEC ({str(e)})")
        return False

def test_comfyui_nodes():
    """Test nodes ComfyUI"""
    print("\nTEST 5: FONCTIONNALITÉS COMFYUI")
    headers = {'Authorization': f'Bearer {BEARER_TOKEN}'}
    try:
        response = requests.get(COMFYUI_URL + "/object_info", headers=headers, timeout=10)
        if response.status_code == 200:
            object_info = response.json()
            qwen_nodes = [key for key in object_info.keys() if 'qwen' in key.lower()]
            if qwen_nodes:
                print(f"✅ Nodes Qwen détectés: SUCCÈS ({len(qwen_nodes)} nodes)")
            else:
                print("⚠️ Aucun node Qwen détecté")
            
            models = [key for key in object_info.keys() if 'model' in key.lower()]
            if models:
                print(f"✅ Modèles détectés: SUCCÈS ({len(models)} modèles)")
            else:
                print("⚠️ Aucun modèle détecté")
            
            return True
        else:
            print(f"❌ Fonctionnalités ComfyUI: ÉCHEC (code {response.status_code})")
            return False
    except Exception as e:
        print(f"❌ Fonctionnalités ComfyUI: ÉCHEC ({str(e)})")
        return False

def main():
    print("=" * 60)
    print("VALIDATION SYSTÈME COMFYUI QWEN")
    print("=" * 60)
    print(f"Début: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    
    # Tests
    results = []
    results.append(test_web_access())
    results.append(test_web_login() is not None)
    results.append(test_api_auth())
    results.append(test_gpu())
    results.append(test_comfyui_nodes())
    
    # Résultats
    print("\n" + "=" * 60)
    print("RÉSULTATS FINAUX")
    print("=" * 60)
    
    success_count = sum(results)
    total_count = len(results)
    success_rate = (success_count / total_count) * 100
    
    print(f"Tests réussis: {success_count}/{total_count} ({success_rate:.1f}%)")
    
    if success_rate >= 80:
        print("\n🎯 SYSTÈME PRÊT POUR LA PRODUCTION")
        print("Le système ComfyUI Qwen est fonctionnel.")
    elif success_rate >= 60:
        print("\n⚠️ SYSTÈME PARTIELLEMENT FONCTIONNEL")
        print("Des ajustements sont nécessaires.")
    else:
        print("\n❌ SYSTÈME NON FONCTIONNEL")
        print("Des corrections critiques sont requises.")
    
    return success_rate >= 80

if __name__ == "__main__":
    main()