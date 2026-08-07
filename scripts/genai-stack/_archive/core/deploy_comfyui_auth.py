#!/usr/bin/env python3
"""
deploy-comfyui-auth.py - Script de déploiement one-liner robuste pour ComfyUI-Login

Ce script implémente l'approche "Back to Basics" :
1. Vérification de l'environnement (Docker, Python, Chemins)
2. Synchronisation des tokens (Source de vérité unique)
3. Démarrage du conteneur (Idempotent)
4. Installation des dépendances (via docker exec)
5. Vérification de santé

Usage:
    python scripts/genai-auth/deploy-comfyui-auth.py [--force] [--skip-models]

Auteur: Roo Code Mode (Phase 32)
Date: 2025-11-30
"""

import argparse
import logging
import os
import subprocess
import sys
import time
import json
from pathlib import Path
from typing import Optional, Dict, Any

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("DeployComfyUI")

# Constantes
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent.parent
DOCKER_COMPOSE_DIR = PROJECT_ROOT / "docker-configurations" / "services" / "comfyui-qwen"
CONTAINER_NAME = "comfyui-qwen"
COMFYUI_PORT = 8188
SECRETS_DIR = PROJECT_ROOT / ".secrets"

class DeploymentManager:
    def __init__(self, args):
        self.args = args
        self.start_time = time.time()
        self.status = "INIT"

    def log_step(self, message: str):
        logger.info(f"\n{'='*50}")
        logger.info(f"🚀 ÉTAPE: {message}")
        logger.info(f"{'='*50}")

    def check_prerequisites(self) -> bool:
        self.log_step("Vérification des prérequis")
        
        # 1. Vérifier Docker
        try:
            subprocess.run(["docker", "--version"], check=True, capture_output=True)
            logger.info("✅ Docker est installé")
        except (subprocess.CalledProcessError, FileNotFoundError):
            logger.error("❌ Docker n'est pas installé ou accessible")
            return False

        # 2. Vérifier docker-compose
        try:
            subprocess.run(["docker-compose", "--version"], check=True, capture_output=True)
            logger.info("✅ docker-compose est installé")
        except (subprocess.CalledProcessError, FileNotFoundError):
            logger.error("❌ docker-compose n'est pas installé ou accessible")
            return False

        # 3. Vérifier les chemins critiques
        if not DOCKER_COMPOSE_DIR.exists():
            logger.error(f"❌ Répertoire docker-compose introuvable: {DOCKER_COMPOSE_DIR}")
            return False
        
        logger.info(f"✅ Répertoire de configuration: {DOCKER_COMPOSE_DIR}")
        return True

    def sync_tokens(self) -> bool:
        self.log_step("Synchronisation des tokens")
        
        try:
            # Ajouter le chemin des scripts au PYTHONPATH pour importer token_synchronizer
            sys.path.append(str(PROJECT_ROOT / "scripts" / "genai-auth" / "utils"))
            from token_synchronizer import TokenSynchronizer
            
            synchronizer = TokenSynchronizer(root_dir=PROJECT_ROOT)
            
            # Exécuter l'unification complète
            logger.info("🔄 Lancement de l'unification des tokens...")
            if synchronizer.run_complete_unification():
                logger.info("✅ Tokens synchronisés avec succès")
                return True
            else:
                logger.error("❌ Échec de la synchronisation des tokens")
                return False
                
        except ImportError:
            logger.error("❌ Impossible d'importer token_synchronizer.py")
            return False
        except Exception as e:
            logger.error(f"❌ Erreur lors de la synchronisation des tokens: {e}")
            return False

    def start_container(self) -> bool:
        self.log_step("Démarrage du conteneur Docker")
        
        # Vérifier si le conteneur tourne déjà
        try:
            result = subprocess.run(
                ["docker", "ps", "--filter", f"name={CONTAINER_NAME}", "--format", "{{.Names}}"],
                capture_output=True, text=True
            )
            if CONTAINER_NAME in result.stdout.strip():
                if self.args.force:
                    logger.info(f"🔄 Redémarrage forcé du conteneur {CONTAINER_NAME}...")
                    subprocess.run(["docker", "stop", CONTAINER_NAME], check=True)
                    subprocess.run(["docker", "rm", CONTAINER_NAME], check=True)
                else:
                    logger.info(f"✅ Le conteneur {CONTAINER_NAME} est déjà en cours d'exécution")
                    return True
        except Exception as e:
            logger.warning(f"⚠️ Erreur lors de la vérification du conteneur: {e}")

        # Démarrer le conteneur
        try:
            logger.info(f"📂 Contexte Docker: {DOCKER_COMPOSE_DIR}")
            cmd = ["docker-compose", "up", "-d", "--build" if self.args.force else "--no-recreate"]
            
            subprocess.run(
                cmd,
                cwd=DOCKER_COMPOSE_DIR,
                check=True
            )
            logger.info(f"✅ Conteneur {CONTAINER_NAME} démarré")
            return True
        except subprocess.CalledProcessError as e:
            logger.error(f"❌ Échec du démarrage du conteneur: {e}")
            return False

    def wait_for_service(self, timeout: int = 60) -> bool:
        self.log_step("Attente de la disponibilité du service")
        
        start_wait = time.time()
        while time.time() - start_wait < timeout:
            try:
                # Vérifier si le port est ouvert (via curl dans le conteneur ou localement)
                # On utilise docker exec pour vérifier l'état interne
                result = subprocess.run(
                    ["docker", "exec", CONTAINER_NAME, "curl", "-s", "-o", "/dev/null", "-w", "%{http_code}", "http://localhost:8188"],
                    capture_output=True, text=True
                )
                status_code = result.stdout.strip()
                
                if status_code in ["200", "401", "403"]:
                    logger.info(f"✅ Service ComfyUI répond (HTTP {status_code})")
                    return True
                
                logger.info(f"⏳ En attente... (HTTP {status_code})")
            except Exception:
                logger.info("⏳ En attente du démarrage...")
            
            time.sleep(2)
            
        logger.error(f"❌ Timeout ({timeout}s) en attendant le service")
        return False

    def install_comfyui_login(self) -> bool:
        self.log_step("Installation de ComfyUI-Login")
        
        # Script d'installation interne à exécuter dans le conteneur
        install_script = """
import os
import sys
import subprocess
from pathlib import Path

CUSTOM_NODES_DIR = Path("/workspace/ComfyUI/custom_nodes")
LOGIN_REPO = "https://github.com/Comfy-Org/ComfyUI_Login.git"
LOGIN_DIR = CUSTOM_NODES_DIR / "ComfyUI_Login"

def install():
    print(f"Installation dans {LOGIN_DIR}...")
    
    if not LOGIN_DIR.exists():
        print("Clonage du dépôt...")
        subprocess.run(["git", "clone", LOGIN_REPO, str(LOGIN_DIR)], check=True)
    else:
        print("Dépôt déjà présent, mise à jour...")
        subprocess.run(["git", "-C", str(LOGIN_DIR), "pull"], check=True)
        
    print("Installation des dépendances...")
    req_file = LOGIN_DIR / "requirements.txt"
    if req_file.exists():
        subprocess.run([sys.executable, "-m", "pip", "install", "-r", str(req_file)], check=True)
    
    print("✅ Installation terminée")

if __name__ == "__main__":
    try:
        install()
    except Exception as e:
        print(f"❌ Erreur: {e}")
        sys.exit(1)
"""
        
        # Écrire le script temporaire
        temp_script = PROJECT_ROOT / "temp_install_login.py"
        with open(temp_script, "w") as f:
            f.write(install_script)
            
        try:
            # Copier le script dans le conteneur
            subprocess.run(
                ["docker", "cp", str(temp_script), f"{CONTAINER_NAME}:/workspace/temp_install_login.py"],
                check=True
            )
            
            # Exécuter le script
            logger.info("Exécution du script d'installation dans le conteneur...")
            subprocess.run(
                ["docker", "exec", CONTAINER_NAME, "python3", "/workspace/temp_install_login.py"],
                check=True
            )
            
            logger.info("✅ ComfyUI-Login installé/mis à jour")
            return True
            
        except subprocess.CalledProcessError as e:
            logger.error(f"❌ Erreur lors de l'installation de ComfyUI-Login: {e}")
            return False
        finally:
            if temp_script.exists():
                temp_script.unlink()

    def run(self) -> bool:
        logger.info("🚀 DÉMARRAGE DU DÉPLOIEMENT COMFYUI-AUTH")
        
        if not self.check_prerequisites():
            return False
            
        if not self.sync_tokens():
            return False
            
        if not self.start_container():
            return False
            
        if self.wait_for_service(timeout=600):
            logger.info("\n✨ DÉPLOIEMENT TERMINÉ AVEC SUCCÈS ✨")
            logger.info(f"URL: http://localhost:{COMFYUI_PORT}")
            return True
        else:
            logger.error("❌ Le service ne répond pas après le redémarrage final")
            return False

def main():
    parser = argparse.ArgumentParser(description="Déploiement robuste de ComfyUI avec Authentification")
    parser.add_argument("--force", action="store_true", help="Force la reconstruction et le redémarrage")
    parser.add_argument("--skip-models", action="store_true", help="Ne vérifie pas les modèles (plus rapide)")
    
    args = parser.parse_args()
    
    manager = DeploymentManager(args)
    success = manager.run()
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()