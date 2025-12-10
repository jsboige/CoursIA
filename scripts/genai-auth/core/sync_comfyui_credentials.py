#!/usr/bin/env python3
"""
Script de synchronisation des credentials ComfyUI depuis le fichier .env
Lit les identifiants du .env et les configure dans ComfyUI-Login
"""

import os
import sys
import bcrypt
import subprocess
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

def check_container_running():
    """Vérifie si le conteneur ComfyUI est en cours d'exécution"""
    try:
        result = subprocess.run(
            ["docker", "ps", "--filter", "name=comfyui-qwen", "--format", "{{.Names}}"],
            capture_output=True, text=True
        )
        return "comfyui-qwen" in result.stdout
    except Exception as e:
        print(f"❌ Erreur vérification conteneur: {e}")
        return False

def create_password_hash(password, username):
    """Crée un hash bcrypt pour le mot de passe"""
    try:
        # Génération du sel et hash
        salt = bcrypt.gensalt()
        hashed_password = bcrypt.hashpw(password.encode('utf-8'), salt)
        return hashed_password
    except Exception as e:
        print(f"❌ Erreur hashage mot de passe: {e}")
        return None

def update_comfyui_password(hashed_password, username):
    """Met à jour le fichier PASSWORD dans le conteneur ComfyUI"""
    try:
        # Écriture du hash et du username dans le fichier PASSWORD
        password_content = hashed_password + b'\n' + username.encode('utf-8')
        
        # Utilisation de docker exec pour écrire dans le conteneur
        cmd = [
            "docker", "exec", "comfyui-qwen", 
            "sh", "-c", 
            f"echo '{password_content.decode('utf-8')}' > /workspace/ComfyUI/login/PASSWORD"
        ]
        
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        if result.returncode == 0:
            print("✅ Fichier PASSWORD mis à jour dans le conteneur")
            return True
        else:
            print(f"❌ Erreur mise à jour PASSWORD: {result.stderr}")
            return False
            
    except Exception as e:
        print(f"❌ Exception mise à jour PASSWORD: {e}")
        return False

def configure_guest_mode(guest_mode_enabled):
    """Configure le mode invité"""
    try:
        if guest_mode_enabled.lower() == 'true':
            # Créer le fichier GUEST_MODE
            cmd = [
                "docker", "exec", "comfyui-qwen", 
                "touch", "/workspace/ComfyUI/login/GUEST_MODE"
            ]
            print("✅ Mode invité activé")
        else:
            # Supprimer le fichier GUEST_MODE s'il existe
            cmd = [
                "docker", "exec", "comfyui-qwen", 
                "sh", "-c", 
                "rm -f /workspace/ComfyUI/login/GUEST_MODE"
            ]
            print("✅ Mode invité désactivé")
            
        result = subprocess.run(cmd, capture_output=True, text=True)
        return result.returncode == 0
        
    except Exception as e:
        print(f"❌ Erreur configuration mode invité: {e}")
        return False

def restart_comfyui_container():
    """Redémarre le conteneur ComfyUI pour appliquer les changements"""
    try:
        print("🔄 Redémarrage du conteneur ComfyUI...")
        result = subprocess.run(
            ["docker-compose", "-f", "docker-configurations/services/comfyui-qwen/docker-compose.yml", "restart"],
            capture_output=True, text=True
        )
        
        if result.returncode == 0:
            print("✅ Conteneur redémarré avec succès")
            return True
        else:
            print(f"❌ Erreur redémarrage conteneur: {result.stderr}")
            return False
            
    except Exception as e:
        print(f"❌ Exception redémarrage conteneur: {e}")
        return False

def main():
    """Fonction principale"""
    print("🔐 SYNCHRONISATION DES CREDENTIALS COMFYUI")
    print("=" * 50)
    
    # Vérification du conteneur
    if not check_container_running():
        print("❌ Le conteneur comfyui-qwen n'est pas en cours d'exécution")
        print("🚀 Démarrage du conteneur...")
        
        # Démarrage du conteneur
        try:
            subprocess.run(
                ["docker-compose", "-f", "docker-configurations/services/comfyui-qwen/docker-compose.yml", "up", "-d"],
                check=True
            )
            print("✅ Conteneur démarré")
            print("⏳ Attente de 60s pour l'initialisation...")
            import time
            time.sleep(60)
        except Exception as e:
            print(f"❌ Erreur démarrage conteneur: {e}")
            sys.exit(1)
    
    # Chargement du .env
    env_path = "docker-configurations/services/comfyui-qwen/.env"
    env_vars = load_env_file(env_path)
    
    if not env_vars:
        print("❌ Impossible de charger le fichier .env")
        sys.exit(1)
    
    # Récupération des credentials
    username = env_vars.get('COMFYUI_USERNAME', 'admin')
    password = env_vars.get('COMFYUI_PASSWORD', '')
    guest_mode = env_vars.get('GUEST_MODE_ENABLED', 'false')
    
    if not password:
        print("❌ COMFYUI_PASSWORD non trouvé dans le .env")
        sys.exit(1)
    
    print(f"📝 Configuration trouvée:")
    print(f"   • Username: {username}")
    print(f"   • Password: {'*' * len(password)}")
    print(f"   • Mode invité: {guest_mode}")
    
    # Création du hash
    print("\n🔐 Hashage du mot de passe...")
    hashed_password = create_password_hash(password, username)
    
    if not hashed_password:
        print("❌ Échec du hashage du mot de passe")
        sys.exit(1)
    
    # Mise à jour du fichier PASSWORD
    print("💾 Mise à jour du fichier PASSWORD...")
    if not update_comfyui_password(hashed_password, username):
        print("❌ Échec de la mise à jour du mot de passe")
        sys.exit(1)

    # Mise à jour du fichier local .secrets/qwen-api-user.token
    try:
        secrets_file = Path(".secrets/qwen-api-user.token")
        secrets_file.parent.mkdir(exist_ok=True)
        secrets_file.write_text(hashed_password.decode('utf-8'))
        print(f"✅ Fichier local mis à jour: {secrets_file}")
    except Exception as e:
        print(f"❌ Erreur mise à jour fichier local: {e}")
    
    # Configuration du mode invité
    print("👥 Configuration du mode invité...")
    if not configure_guest_mode(guest_mode):
        print("❌ Échec de la configuration du mode invité")
        sys.exit(1)
    
    # Redémarrage du conteneur
    if not restart_comfyui_container():
        print("❌ Échec du redémarrage du conteneur")
        sys.exit(1)
    
    # Attente pour le démarrage
    print("⏳ Attente de 30s pour le démarrage complet...")
    import time
    time.sleep(30)
    
    # Affichage des credentials
    print("\n" + "=" * 50)
    print("🎉 SYNCHRONISATION TERMINÉE AVEC SUCCÈS")
    print("=" * 50)
    print(f"📱 URL d'accès: http://localhost:8188/")
    print(f"👤 Username: {username}")
    print(f"🔑 Password: {password}")
    print(f"👥 Mode invité: {guest_mode}")
    
    print("\n📋 INSTRUCTIONS:")
    print("1. Accédez à http://localhost:8188/")
    print("2. Utilisez les identifiants ci-dessus pour vous connecter")
    print("3. Le mode invité est " + ("activé" if guest_mode.lower() == 'true' else "désactivé"))
    
    # Test de connexion
    print("\n🔍 Test de l'authentification...")
    try:
        import requests
        response = requests.get("http://localhost:8188/", timeout=10)
        
        if response.status_code == 200:
            if "login" in response.text.lower() or "auth" in response.text.lower():
                print("✅ Interface web protégée - Authentification requise")
            else:
                print("⚠️ Interface web accessible - Vérifiez la configuration")
        else:
            print(f"⚠️ Réponse inattendue: {response.status_code}")
            
    except Exception as e:
        print(f"❌ Erreur test connexion: {e}")
    
    print("\n✨ Les credentials ComfyUI sont maintenant synchronisés!")

if __name__ == "__main__":
    main()