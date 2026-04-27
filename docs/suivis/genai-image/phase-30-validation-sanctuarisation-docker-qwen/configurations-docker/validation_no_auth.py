#!/usr/bin/env python3
"""
Script de validation du système ComfyUI Qwen SANS authentification
"""

import requests
import json
import time
from datetime import datetime

# Configuration
COMFYUI_URL = "http://localhost:8188"

def test_web_access():
    """Test accès web sans authentification"""
    print("TEST 1: ACCÈS WEB (SANS AUTH)")
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

def test_api_no_auth():
    """Test API sans authentification"""
    print("\nTEST 2: API (SANS AUTH)")
    try:
        response = requests.get(COMFYUI_URL + "/system_stats", timeout=10)
        if response.status_code == 200:
            print("✅ API sans authentification: SUCCÈS")
            data = response.json()
            print(f"📊 Infos système: {len(data)} champs")
            return True
        else:
            print(f"❌ API sans authentification: ÉCHEC (code {response.status_code})")
            return False
    except Exception as e:
        print(f"❌ API sans authentification: ÉCHEC ({str(e)})")
        return False

def test_gpu():
    """Test GPU"""
    print("\nTEST 3: VALIDATION GPU")
    try:
        response = requests.get(COMFYUI_URL + "/system_stats", timeout=10)
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
    print("\nTEST 4: FONCTIONNALITÉS COMFYUI")
    try:
        response = requests.get(COMFYUI_URL + "/object_info", timeout=10)
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
    print("VALIDATION SYSTÈME COMFYUI QWEN (SANS AUTHENTIFICATION)")
    print("=" * 60)
    print(f"Début: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    
    # Tests
    results = []
    results.append(test_web_access())
    results.append(test_api_no_auth())
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