#!/usr/bin/env python3
"""
Test d'authentification ComfyUI avec credentials dynamiques.

Architecture alignée avec setup_complete_qwen.py :
- Credentials chargés depuis .secrets/qwen-api-user.token
- Gestion d'erreurs robuste
- Logging structuré

Auteur : Phase 29 - Rapport 38
Date : 2025-11-02
Version: 2.0.0 (Credentials Dynamiques)
"""

import sys
import requests
from pathlib import Path

# Configuration
COMFYUI_URL = "http://localhost:8188"


def load_auth_token():
    """Charge le token d'authentification depuis .secrets/qwen-api-user.token"""
    # Remonter à la racine du projet (3 niveaux: utils -> genai-auth -> scripts -> racine)
    project_root = Path(__file__).parent.parent.parent.parent
    secrets_file = project_root / ".secrets" / "qwen-api-user.token"
    
    if not secrets_file.exists():
        raise FileNotFoundError(
            f"Fichier secrets non trouvé : {secrets_file}\n"
            f"Exécutez install_comfyui_login.py pour générer le token"
        )
    
    bcrypt_hash = secrets_file.read_text().strip()
    
    if not bcrypt_hash.startswith("$2b$"):
        raise ValueError(
            f"Hash bcrypt invalide dans {secrets_file}\n"
            f"Le hash doit commencer par '$2b$'"
        )
    
    return bcrypt_hash


# Charger le hash bcrypt dynamiquement
BCRYPT_HASH = load_auth_token()

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