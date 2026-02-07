#!/usr/bin/env python3
"""
cleanup-comfyui-auth.py - Script de nettoyage one-liner pour ComfyUI-Login

Ce script permet de repartir d'un état propre :
1. Arrêt du conteneur
2. Suppression du conteneur
3. Optionnel : Suppression des volumes (nettoyage profond)
4. Optionnel : Suppression des tokens (reset auth)

Usage:
    python scripts/genai-auth/cleanup-comfyui-auth.py [--deep] [--reset-auth]

Auteur: Roo Code Mode (Phase 32)
Date: 2025-11-30
"""

import argparse
import logging
import subprocess
import sys
import shutil
from pathlib import Path

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("CleanupComfyUI")

# Constantes
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent.parent
CONTAINER_NAME = "comfyui-qwen"
SECRETS_DIR = PROJECT_ROOT / ".secrets"

class CleanupManager:
    def __init__(self, args):
        self.args = args

    def log_step(self, message: str):
        logger.info(f"\n{'='*50}")
        logger.info(f"🧹 NETTOYAGE: {message}")
        logger.info(f"{'='*50}")

    def stop_container(self) -> bool:
        self.log_step("Arrêt et suppression du conteneur")
        
        try:
            # Vérifier si le conteneur existe
            result = subprocess.run(
                ["docker", "ps", "-a", "--filter", f"name={CONTAINER_NAME}", "--format", "{{.Names}}"],
                capture_output=True, text=True
            )
            
            if CONTAINER_NAME not in result.stdout.strip():
                logger.info(f"✅ Le conteneur {CONTAINER_NAME} n'existe pas")
                return True
                
            logger.info(f"Arrêt de {CONTAINER_NAME}...")
            subprocess.run(["docker", "stop", CONTAINER_NAME], check=False)
            
            logger.info(f"Suppression de {CONTAINER_NAME}...")
            subprocess.run(["docker", "rm", CONTAINER_NAME], check=True)
            
            logger.info(f"✅ Conteneur {CONTAINER_NAME} supprimé")
            return True
            
        except subprocess.CalledProcessError as e:
            logger.error(f"❌ Erreur lors de la suppression du conteneur: {e}")
            return False

    def clean_volumes(self) -> bool:
        if not self.args.deep:
            return True
            
        self.log_step("Nettoyage des volumes (Deep Clean)")
        
        # Attention : on ne supprime PAS les modèles partagés ou les outputs
        # On supprime uniquement le workspace local du conteneur s'il existe
        workspace_dir = PROJECT_ROOT / "docker-configurations" / "services" / "comfyui-qwen" / "workspace"
        
        if workspace_dir.exists():
            try:
                logger.warning(f"⚠️ Suppression du workspace local: {workspace_dir}")
                # Demander confirmation si interactif
                if sys.stdin.isatty():
                    response = input(f"Confirmer la suppression de {workspace_dir} ? [y/N] ")
                    if response.lower() != 'y':
                        logger.info("Annulé par l'utilisateur")
                        return True
                
                shutil.rmtree(workspace_dir)
                logger.info("✅ Workspace supprimé")
            except Exception as e:
                logger.error(f"❌ Erreur suppression workspace: {e}")
                return False
        else:
            logger.info("ℹ️ Pas de workspace local à supprimer")
            
        return True

    def reset_auth(self) -> bool:
        if not self.args.reset_auth:
            return True
            
        self.log_step("Réinitialisation de l'authentification")
        
        config_path = SECRETS_DIR / "comfyui_auth_tokens.conf"
        
        if config_path.exists():
            try:
                # Backup avant suppression
                backup_path = config_path.with_suffix(f".backup.{int(time.time())}")
                shutil.copy2(config_path, backup_path)
                logger.info(f"Backup créé: {backup_path}")
                
                config_path.unlink()
                logger.info("✅ Configuration des tokens supprimée")
            except Exception as e:
                logger.error(f"❌ Erreur suppression config tokens: {e}")
                return False
        else:
            logger.info("ℹ️ Pas de configuration de tokens à supprimer")
            
        return True

    def run(self) -> bool:
        logger.info("🚀 DÉMARRAGE DU NETTOYAGE")
        
        if not self.stop_container():
            return False
            
        if not self.clean_volumes():
            return False
            
        if not self.reset_auth():
            return False
            
        logger.info("\n✨ NETTOYAGE TERMINÉ ✨")
        return True

def main():
    parser = argparse.ArgumentParser(description="Nettoyage de l'environnement ComfyUI")
    parser.add_argument("--deep", action="store_true", help="Supprime aussi le workspace local (Attention !)")
    parser.add_argument("--reset-auth", action="store_true", help="Supprime la configuration des tokens")
    
    args = parser.parse_args()
    
    manager = CleanupManager(args)
    success = manager.run()
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    import time
    main()