#!/usr/bin/env python3
"""
Script Simple - Test Authentification ComfyUI avec Hash Bcrypt

Ce script teste l'authentification ComfyUI-Login en utilisant
le hash bcrypt comme Bearer token (comportement documenté).

Auteur: Consolidation Phase 29
Date: 2025-11-01
Version: 1.0.0
"""

import sys
import requests
from pathlib import Path

# Configuration
COMFYUI_URL = "http://localhost:8188"
BCRYPT_HASH = "$2b$12$2jPJrb7dmsM7fw0..PoEqu8nmGarw0vnYYdGw5BFmcZ52bGfwf5M2"

def test_authentication():
    """Test l'authentification avec le hash bcrypt comme token"""
    
    print("=" * 60)
    print("Test d'Authentification ComfyUI-Login")
    print("=" * 60)
    
    headers = {
        "Authorization": f"Bearer {BCRYPT_HASH}",
        "Content-Type": "application/json"
    }
    
    print(f"\n1️⃣ Test de connectivité...")
    print(f"   URL: {COMFYUI_URL}/system_stats")
    print(f"   Token: {BCRYPT_HASH[:20]}...")
    
    try:
        response = requests.get(
            f"{COMFYUI_URL}/system_stats",
            headers=headers,
            timeout=10
        )
        
        if response.status_code == 200:
            print("\n✅ SUCCÈS - Authentification réussie!")
            
            data = response.json()
            system = data.get("system", {})
            devices = data.get("devices", [])
            
            print("\n📊 Informations Système:")
            print(f"   • OS: {system.get('os', 'N/A')}")
            print(f"   • RAM Totale: {system.get('ram_total', 0) / (1024**3):.2f} GB")
            print(f"   • RAM Libre: {system.get('ram_free', 0) / (1024**3):.2f} GB")
            print(f"   • ComfyUI Version: {system.get('comfyui_version', 'N/A')}")
            print(f"   • Python Version: {system.get('python_version', 'N/A')}")
            
            if devices:
                print("\n🖥️ Périphériques GPU:")
                for device in devices:
                    print(f"   • {device.get('name', 'Unknown')}")
                    print(f"     - VRAM Totale: {device.get('vram_total', 0) / (1024**3):.2f} GB")
                    print(f"     - VRAM Libre: {device.get('vram_free', 0) / (1024**3):.2f} GB")
            
            return True
            
        elif response.status_code == 401:
            print(f"\n❌ ÉCHEC - Authentification refusée (HTTP 401)")
            print(f"   Réponse: {response.text}")
            return False
        else:
            print(f"\n❌ ÉCHEC - Code HTTP {response.status_code}")
            print(f"   Réponse: {response.text}")
            return False
            
    except requests.exceptions.ConnectionError:
        print("\n❌ ÉCHEC - Impossible de se connecter au serveur ComfyUI")
        print(f"   Vérifiez que le container est démarré: docker ps | grep comfyui-qwen")
        return False
    except Exception as e:
        print(f"\n❌ ERREUR - {type(e).__name__}: {e}")
        return False

def main():
    """Point d'entrée principal"""
    success = test_authentication()
    
    print("\n" + "=" * 60)
    if success:
        print("✅ Test réussi - Authentification fonctionnelle")
        print("\n💡 Prochaine étape: Test de génération d'image")
        return 0
    else:
        print("❌ Test échoué - Vérifiez la configuration")
        return 1

if __name__ == "__main__":
    sys.exit(main())