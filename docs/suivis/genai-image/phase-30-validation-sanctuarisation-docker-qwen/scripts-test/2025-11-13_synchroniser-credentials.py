#!/usr/bin/env python3
"""
Script de synchronisation des credentials ComfyUI Qwen - Phase 29
Adapté à la structure de répertoires actuelle

Date: 2025-11-13
Objectif: Synchroniser les credentials entre Windows et WSL pour ComfyUI-Login
"""

import os
import sys
import json
import tempfile
import subprocess
from pathlib import Path
from datetime import datetime

# Configuration des chemins
WINDOWS_ROOT = Path("d:/Dev/CoursIA")
WINDOWS_SECRETS = WINDOWS_ROOT / ".secrets"
WINDOWS_ENV_FILE = WINDOWS_SECRETS / ".env.generated"
WINDOWS_HASH_FILE = WINDOWS_SECRETS / "qwen-api-user.token"

# Chemins WSL (selon scripts existants)
WSL_COMFYUI_PATH = "/home/jesse/SD/workspace/comfyui-qwen"
WSL_SECRETS = f"{WSL_COMFYUI_PATH}/ComfyUI/.secrets"

def log(message: str) -> None:
    """Affiche un message avec timestamp"""
    timestamp = datetime.now().strftime("%H:%M:%S")
    print(f"[{timestamp}] {message}")

def execute_wsl(cmd: str, check: bool = True) -> dict:
    """Exécute une commande WSL et retourne le résultat"""
    log(f"WSL: {cmd[:100]}...")
    
    try:
        result = subprocess.run(
            ["wsl", "bash", "-c", cmd],
            capture_output=True,
            shell=False,
            timeout=60,
            encoding='utf-8',
            errors='replace'
        )
        
        if check and result.returncode != 0:
            log(f"❌ Erreur WSL (code {result.returncode})")
            log(f"STDERR: {result.stderr}")
            raise RuntimeError(f"Erreur WSL: {result.stderr}")
            
        return {
            'returncode': result.returncode,
            'stdout': result.stdout.strip(),
            'stderr': result.stderr.strip()
        }
    except subprocess.TimeoutExpired:
        log("❌ Timeout WSL")
        raise
    except Exception as e:
        log(f"❌ Exception WSL: {e}")
        raise

def execute_docker_windows(cmd: str, cwd: str = None, check: bool = True) -> dict:
    """Exécute commande Docker depuis Windows"""
    if cwd:
        if cwd.startswith('/'):
            cwd_windows = f"\\\\wsl$\\Ubuntu{cwd}"
        else:
            cwd_windows = cwd
    else:
        cwd_windows = None
    
    docker_cmd = ["docker"] + cmd.split()
    log(f"Docker: {' '.join(docker_cmd[:5])}...")
    
    try:
        result = subprocess.run(
            docker_cmd,
            capture_output=True,
            text=True,
            shell=False,
            cwd=cwd_windows,
            timeout=60,
            encoding='utf-8',
            errors='replace'
        )
        
        if check and result.returncode != 0:
            log(f"❌ Erreur Docker (code {result.returncode})")
            log(f"STDERR: {result.stderr}")
            raise RuntimeError(f"Erreur Docker: {result.stderr}")
        
        return {
            'returncode': result.returncode,
            'stdout': result.stdout.strip(),
            'stderr': result.stderr.strip()
        }
    except Exception as e:
        log(f"❌ Exception Docker: {e}")
        raise

def extract_token_from_env(env_content: str) -> str:
    """Extrait QWEN_API_USER_TOKEN du contenu .env"""
    for line in env_content.split('\n'):
        if line.startswith('QWEN_API_USER_TOKEN='):
            return line.split('=', 1)[1].strip().strip('"').strip("'")
    raise ValueError("QWEN_API_USER_TOKEN non trouvé dans .env.generated")

def generate_bcrypt_hash(password: str) -> str:
    """Génère un hash bcrypt du mot de passe"""
    import bcrypt
    salt = bcrypt.gensalt(rounds=12)
    hashed = bcrypt.hashpw(password.encode('utf-8'), salt)
    return hashed.decode('utf-8')

def synchronize_credentials():
    """Synchronise les credentials entre Windows et WSL"""
    log("🔐 DÉBUT SYNCHRONISATION CREDENTIALS")
    
    try:
        # 1. Vérifier les fichiers Windows
        log("📋 Vérification fichiers Windows...")
        if not WINDOWS_ENV_FILE.exists():
            log(f"❌ Fichier .env.generated manquant: {WINDOWS_ENV_FILE}")
            return False
        
        if not WINDOWS_HASH_FILE.exists():
            log(f"❌ Fichier token manquant: {WINDOWS_HASH_FILE}")
            # Générer le hash depuis le token brut
            log("🔑 Génération du hash bcrypt...")
            env_content = WINDOWS_ENV_FILE.read_text(encoding='utf-8').strip()
            token_value = extract_token_from_env(env_content)
            hash_value = generate_bcrypt_hash(token_value)
            WINDOWS_HASH_FILE.write_text(hash_value, encoding='utf-8')
            log(f"✅ Hash bcrypt généré: {hash_value[:30]}...")
        
        # 2. Lire les credentials Windows
        log("📖 Lecture credentials Windows...")
        env_content = WINDOWS_ENV_FILE.read_text(encoding='utf-8').strip()
        token_value = extract_token_from_env(env_content)
        hash_value = WINDOWS_HASH_FILE.read_text(encoding='utf-8').strip()
        
        log(f"✅ Token brut: {token_value[:15]}...")
        log(f"✅ Hash bcrypt: {hash_value[:30]}...")
        
        # 3. Créer le répertoire .secrets WSL
        log("📁 Création répertoire .secrets WSL...")
        execute_wsl(f"mkdir -p {WSL_SECRETS}", check=False)
        
        # 4. Synchroniser le hash vers WSL
        log("🔄 Synchronisation hash vers WSL...")
        with tempfile.NamedTemporaryFile(mode='w', delete=False, encoding='utf-8') as tmp:
            tmp.write(hash_value)
            tmp_path = tmp.name
        
        try:
            # Convertir le chemin Windows en chemin WSL
            tmp_wsl = execute_wsl(f"wslpath '{tmp_path}'")['stdout']
            # Copier le fichier temporaire vers la destination
            execute_wsl(f"cp {tmp_wsl} {WSL_SECRETS}/qwen-api-user.token")
            log("✅ Hash synchronisé vers WSL")
        finally:
            os.unlink(tmp_path)
        
        # 5. Configurer les permissions
        log("🔒 Configuration permissions...")
        execute_wsl(f"chmod 600 {WSL_SECRETS}/qwen-api-user.token")
        log("✅ Permissions configurées")
        
        # 6. Vérifier la synchronisation
        log("🔍 Vérification synchronisation...")
        verify = execute_wsl(f"cat {WSL_SECRETS}/qwen-api-user.token")
        synced_hash = verify['stdout']
        
        if synced_hash != hash_value:
            log(f"❌ Hash non synchronisé: '{synced_hash[:30]}...' != '{hash_value[:30]}...'")
            return False
        
        log("✅ Synchronisation vérifiée avec succès")
        
        # 7. Redémarrer le container Docker
        log("🔄 Redémarrage container Docker...")
        container_name = "comfyui-qwen"
        
        # Vérifier si le container existe
        check_result = execute_docker_windows(
            f"ps -a --filter name={container_name} --format {{{{.Names}}}}",
            check=False
        )
        container_exists = container_name in check_result['stdout']
        
        if container_exists:
            log(f"📦 Container {container_name} détecté")
            # Arrêter
            execute_docker_windows(f"stop {container_name}", check=False)
            log("⏹ Container arrêté")
            # Démarrer
            execute_docker_windows(f"start {container_name}")
            log("▶️ Container démarré")
        else:
            log(f"⚠️ Container {container_name} non trouvé")
        
        # 8. Attendre le démarrage
        log("⏳ Attente démarrage ComfyUI (30s)...")
        import time
        time.sleep(30)
        
        # 9. Vérifier le statut
        log("🔍 Vérification statut container...")
        status_result = execute_docker_windows(
            f"inspect -f '{{{{.State.Status}}}}' {container_name}",
            check=False
        )
        container_status = status_result['stdout'].strip().strip("'")
        
        if container_status != 'running':
            log(f"❌ Container non démarré: {container_status}")
            return False
        
        log(f"✅ Container {container_name}: {container_status}")
        
        return True
        
    except Exception as e:
        log(f"❌ Erreur synchronisation: {e}")
        return False

def test_authentication():
    """Test l'authentification ComfyUI après synchronisation"""
    log("\n🧪 TEST D'AUTHENTIFICATION")
    
    try:
        import requests
        
        # Lire le hash
        hash_value = WINDOWS_HASH_FILE.read_text(encoding='utf-8').strip()
        
        # Test d'authentification
        log("🔑 Test authentification avec hash bcrypt...")
        response = requests.get(
            "http://localhost:8188/system_stats",
            headers={"Authorization": f"Bearer {hash_value}"},
            timeout=10
        )
        
        if response.status_code == 200:
            log("✅ Authentification réussie!")
            system_info = response.json()
            log(f"📊 Infos système: {len(system_info)} champs")
            return True
        else:
            log(f"❌ Échec authentification: HTTP {response.status_code}")
            log(f"📝 Réponse: {response.text[:200]}")
            return False
            
    except Exception as e:
        log(f"❌ Erreur test authentification: {e}")
        return False

def main():
    """Fonction principale"""
    print("╔═══════════════════════════════════════════════════╗")
    print("║  SYNCHRONISATION CREDENTIALS COMFYUI QWEN       ║")
    print("║                Phase 29 - Adaptation               ║")
    print("╚═══════════════════════════════════════════════════╝")
    print(f"📅 Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # Étape 1: Synchronisation
    sync_success = synchronize_credentials()
    
    if sync_success:
        # Étape 2: Test d'authentification
        auth_success = test_authentication()
        
        if auth_success:
            log("\n🎉 SUCCÈS COMPLET!")
            log("✅ Credentials synchronisés")
            log("✅ Container redémarré")
            log("✅ Authentification validée")
            return 0
        else:
            log("\n⚠️ SUCCÈS PARTIEL!")
            log("✅ Credentials synchronisés")
            log("✅ Container redémarré")
            log("❌ Authentification échouée")
            return 1
    else:
        log("\n❌ ÉCHEC SYNCHRONISATION!")
        return 2

if __name__ == "__main__":
    sys.exit(main())