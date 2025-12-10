#!/usr/bin/env python3
"""
Script d'installation ComfyUI avec authentification intégrée
Lit le .env et configure ComfyUI-Login automatiquement
"""

import os
import sys
import subprocess
import time
from pathlib import Path

def load_env_file(env_path):
    """Charge les variables du fichier .env"""
    env_vars = {}
    try:
        with open(env_path, 'r') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#') and '=' in line:
                    key, value = line.split('=', 1)
                    env_vars[key.strip()] = value.strip()
        return env_vars
    except Exception as e:
        print(f"❌ Erreur lecture .env: {e}")
        return None

def check_docker_compose():
    """Vérifie si docker-compose.yml existe"""
    compose_path = "docker-configurations/services/comfyui-qwen/docker-compose.yml"
    if not os.path.exists(compose_path):
        print(f"❌ Fichier {compose_path} non trouvé")
        return False
    return True

def update_docker_compose_with_env():
    """Met à jour docker-compose.yml pour inclure les variables d'environnement d'authentification"""
    compose_path = "docker-configurations/services/comfyui-qwen/docker-compose.yml"
    
    try:
        with open(compose_path, 'r') as f:
            content = f.read()
        
        # Vérification si les variables d'authentification sont déjà présentes
        if 'COMFYUI_USERNAME' in content and 'COMFYUI_PASSWORD' in content:
            print("✅ Variables d'authentification déjà présentes dans docker-compose.yml")
            return True
        
        # Ajout des variables d'environnement d'authentification
        env_section = """
    environment:
      - CUDA_VISIBLE_DEVICES=${CUDA_VISIBLE_DEVICES:-0}
      - NVIDIA_VISIBLE_DEVICES=${NVIDIA_VISIBLE_DEVICES:-0}
      - PYTHONUNBUFFERED=1
      - PYTHONDONTWRITEBYTECODE=1
      - TZ=${TZ:-Europe/Paris}
      - COMFYUI_PORT=8188
      - COMFYUI_LISTEN=0.0.0.0
      - COMFYUI_LOGIN_ENABLED=true
      - COMFYUI_USERNAME=${COMFYUI_USERNAME:-admin}
      - COMFYUI_PASSWORD=${COMFYUI_PASSWORD}
      - GUEST_MODE_ENABLED=${GUEST_MODE_ENABLED:-false}"""
        
        # Remplacement de la section environment
        import re
        pattern = r'(\s+environment:\s*\n(?:\s+-[^\n]*\n)*)'
        replacement = env_section
        
        new_content = re.sub(pattern, replacement, content, flags=re.MULTILINE)
        
        with open(compose_path, 'w') as f:
            f.write(new_content)
        
        print("✅ docker-compose.yml mis à jour avec les variables d'authentification")
        return True
        
    except Exception as e:
        print(f"❌ Erreur mise à jour docker-compose.yml: {e}")
        return False

def install_comfyui_login():
    """Installe ComfyUI-Login si nécessaire"""
    try:
        # Vérification si ComfyUI-Login est déjà installé
        result = subprocess.run(
            ["docker", "exec", "comfyui-qwen", "test", "-d", "/workspace/ComfyUI/custom_nodes/ComfyUI-Login"],
            capture_output=True
        )
        
        if result.returncode == 0:
            print("✅ ComfyUI-Login déjà installé")
            return True
        
        print("📦 Installation de ComfyUI-Login...")
        
        # Installation de ComfyUI-Login
        cmd = [
            "docker", "exec", "comfyui-qwen",
            "sh", "-c",
            """
            cd /workspace/ComfyUI/custom_nodes &&
            git clone https://github.com/ComfyUI-Login/ComfyUI-Login.git &&
            cd ComfyUI-Login &&
            pip install -r requirements.txt
            """
        ]
        
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        if result.returncode == 0:
            print("✅ ComfyUI-Login installé avec succès")
            return True
        else:
            print(f"❌ Erreur installation ComfyUI-Login: {result.stderr}")
            return False
            
    except Exception as e:
        print(f"❌ Exception installation ComfyUI-Login: {e}")
        return False

def start_comfyui_container():
    """Démarre le conteneur ComfyUI"""
    try:
        print("🚀 Démarrage du conteneur ComfyUI...")
        
        result = subprocess.run(
            ["docker-compose", "-f", "docker-configurations/services/comfyui-qwen/docker-compose.yml", "up", "-d"],
            capture_output=True, text=True
        )
        
        if result.returncode == 0:
            print("✅ Conteneur démarré avec succès")
            return True
        else:
            print(f"❌ Erreur démarrage conteneur: {result.stderr}")
            return False
            
    except Exception as e:
        print(f"❌ Exception démarrage conteneur: {e}")
        return False

def wait_for_comfyui_ready(max_wait=300):
    """Attend que ComfyUI soit prêt"""
    print(f"⏳ Attente du démarrage de ComfyUI (max {max_wait}s)...")
    
    for i in range(max_wait):
        try:
            import requests
            response = requests.get("http://localhost:8188/system_stats", timeout=5)
            if response.status_code in [200, 401, 403]:
                print(f"✅ ComfyUI est prêt! (Status: {response.status_code})")
                return True
        except:
            pass
        
        if i % 30 == 0 and i > 0:
            print(f"⏳ Attente en cours... ({i}/{max_wait}s)")
        
        time.sleep(1)
    
    print("❌ Timeout: ComfyUI n'a pas démarré dans le temps imparti")
    return False

def main():
    """Fonction principale"""
    print("🚀 INSTALLATION COMFYUI AVEC AUTHENTIFICATION INTÉGRÉE")
    print("=" * 60)
    
    # Vérifications préliminaires
    if not check_docker_compose():
        sys.exit(1)
    
    # Chargement du .env
    env_path = "docker-configurations/services/comfyui-qwen/.env"
    env_vars = load_env_file(env_path)
    
    if not env_vars:
        print("❌ Impossible de charger le fichier .env")
        sys.exit(1)
    
    # Vérification des credentials
    username = env_vars.get('COMFYUI_USERNAME', 'admin')
    password = env_vars.get('COMFYUI_PASSWORD', '')
    
    if not password:
        print("❌ COMFYUI_PASSWORD non trouvé dans le .env")
        sys.exit(1)
    
    print(f"📝 Configuration trouvée:")
    print(f"   • Username: {username}")
    print(f"   • Password: {'*' * len(password)}")
    
    # Mise à jour de docker-compose.yml
    if not update_docker_compose_with_env():
        print("❌ Échec de la mise à jour de docker-compose.yml")
        sys.exit(1)
    
    # Démarrage du conteneur
    if not start_comfyui_container():
        print("❌ Échec du démarrage du conteneur")
        sys.exit(1)
    
    # Attente du démarrage
    if not wait_for_comfyui_ready():
        print("❌ ComfyUI n'a pas démarré correctement")
        sys.exit(1)
    
    # Installation de ComfyUI-Login
    if not install_comfyui_login():
        print("❌ Échec de l'installation de ComfyUI-Login")
        sys.exit(1)
    
    # Configuration des credentials
    print("🔐 Configuration des credentials...")
    sync_cmd = ["python", "scripts/genai-auth/sync_comfyui_credentials.py"]
    result = subprocess.run(sync_cmd, capture_output=True, text=True)
    
    if result.returncode != 0:
        print(f"❌ Échec de la synchronisation des credentials: {result.stderr}")
        sys.exit(1)
    
    print("\n" + "=" * 60)
    print("🎉 INSTALLATION TERMINÉE AVEC SUCCÈS")
    print("=" * 60)
    print(f"📱 URL d'accès: http://localhost:8188/")
    print(f"👤 Username: {username}")
    print(f"🔑 Password: {password}")
    
    print("\n📋 PROCHAINES ÉTAPES:")
    print("1. Accédez à http://localhost:8188/")
    print("2. Utilisez les identifiants ci-dessus pour vous connecter")
    print("3. L'authentification est maintenant configurée et fonctionnelle")
    
    print("\n✨ ComfyUI avec authentification est prêt!")

if __name__ == "__main__":
    main()