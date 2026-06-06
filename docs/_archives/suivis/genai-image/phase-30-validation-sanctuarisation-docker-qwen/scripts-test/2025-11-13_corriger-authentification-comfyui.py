#!/usr/bin/env python3
"""
Script pour corriger l'authentification ComfyUI en utilisant les scripts existants
Basé sur l'analyse des scripts genai-auth/core et genai-auth/utils
"""

import sys
import os
from pathlib import Path

# Ajout du chemin des scripts d'authentification
sys.path.append(str(Path(__file__).parent.parent.parent / "genai-auth" / "core"))
sys.path.append(str(Path(__file__).parent.parent.parent / "genai-auth" / "utils"))

try:
    from token_manager import TokenManager
    from genai_auth_manager import GenAIAuthManager
    print("✅ Scripts d'authentification importés avec succès")
except ImportError as e:
    print(f"❌ Erreur d'import des scripts: {e}")
    sys.exit(1)

def corriger_authentification_comfyui():
    """Corrige l'authentification ComfyUI avec le hash bcrypt correct"""
    
    print("🔧 Correction de l'authentification ComfyUI...")
    
    # Initialisation des gestionnaires
    token_manager = TokenManager()
    auth_manager = GenAIAuthManager()
    
    # Récupération du hash bcrypt depuis les secrets
    try:
        hash_value = token_manager.get_bcrypt_hash()
        print(f"📋 Hash bcrypt récupéré: {hash_value[:20]}...")
    except Exception as e:
        print(f"❌ Erreur récupération hash: {e}")
        return False
    
    # Application du hash dans le container ComfyUI
    try:
        # Le hash doit être placé dans /workspace/ComfyUI/custom_nodes/ComfyUI-Login/password/password.txt
        container_password_file = "/workspace/ComfyUI/custom_nodes/ComfyUI-Login/password/password.txt"
        
        # Utilisation de docker exec pour écrire le fichier
        import subprocess
        
        cmd = [
            "docker", "exec", "comfyui-qwen", "sh", "-c",
            f'echo "{hash_value}" > {container_password_file}'
        ]
        
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        
        if result.returncode == 0:
            print("✅ Hash bcrypt écrit avec succès dans le container")
            
            # Redémarrage du container pour appliquer les changements
            print("🔄 Redémarrage du container ComfyUI...")
            restart_cmd = ["docker", "restart", "comfyui-qwen"]
            subprocess.run(restart_cmd, check=True)
            print("✅ Container redémarré")
            
            return True
        else:
            print(f"❌ Erreur écriture hash: {result.stderr}")
            return False
            
    except Exception as e:
        print(f"❌ Erreur lors de l'application du hash: {e}")
        return False

def main():
    """Fonction principale"""
    print("🚀 Script de correction d'authentification ComfyUI")
    print("=" * 50)
    
    if corriger_authentification_comfyui():
        print("✅ Authentification ComfyUI corrigée avec succès")
        
        # Test de connexion
        print("\n🧪 Test de connexion à ComfyUI...")
        test_result = tester_connexion_comfyui()
        
        if test_result:
            print("✅ Connexion ComfyUI réussie !")
            return 0
        else:
            print("❌ Échec de la connexion ComfyUI")
            return 1
    else:
        print("❌ Échec de la correction d'authentification")
        return 1

def tester_connexion_comfyui():
    """Test la connexion à l'API ComfyUI"""
    try:
        import requests
        
        # Récupération du hash pour l'authentification
        token_manager = TokenManager()
        auth_token = token_manager.get_bcrypt_hash()
        
        # Test de connexion à l'API
        api_url = "http://localhost:8188/system_stats"
        headers = {
            "Authorization": f"Bearer {auth_token}",
            "Content-Type": "application/json"
        }
        
        response = requests.get(api_url, headers=headers, timeout=10)
        
        if response.status_code == 200:
            print("✅ API ComfyUI accessible")
            return True
        else:
            print(f"❌ Erreur API: {response.status_code} - {response.text}")
            return False
            
    except Exception as e:
        print(f"❌ Erreur de connexion: {e}")
        return False

if __name__ == "__main__":
    sys.exit(main())