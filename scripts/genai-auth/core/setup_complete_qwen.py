#!/usr/bin/env python3
"""
Wrapper d'installation complète du système Qwen pour génération d'images ComfyUI.

Ce script consolide tous les progrès de la Phase 29 :
1. Vérification prérequis (Docker, WSL, Python)
2. Démarrage container comfyui-qwen
3. Installation ComfyUI-Login (authentification bcrypt)
4. Téléchargement modèles FP8 officiels Comfy-Org
5. Configuration authentification (génération credentials)
6. Test end-to-end (génération image validation)
7. Génération rapport d'installation

Usage:
    python scripts/genai-auth/core/setup_complete_qwen.py [OPTIONS]

Options:
    --skip-docker      : Ne pas démarrer le container Docker (déjà en cours)
    --skip-models      : Ne pas télécharger les modèles (déjà présents)
    --skip-auth        : Ne pas installer ComfyUI-Login (déjà installé)
    --skip-test        : Ne pas exécuter le test de génération d'image
    --report-dir PATH  : Répertoire de génération du rapport (défaut: rapports/)

Auteur: Consolidation Phase 29
Date: 2025-11-02
"""

import argparse
import json
import logging
import os
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple, Optional

# Configuration logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Constantes (extraites des scripts validés Phase 29)
COMFYUI_HOST = "localhost"
COMFYUI_PORT = 8188
DOCKER_CONTAINER_NAME = "comfyui-qwen"
MODELS_DIR = Path("/mnt/d/Dev/ai-models/ComfyUI")

# Architecture modèles FP8 officiels validée
QWEN_MODELS = {
    "diffusion": {
        "name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "repo": "Comfy-Org/Qwen-Image-Edit_ComfyUI",
        "filename": "split_files/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "size_gb": 20.0,
        "container_dir": "/workspace/ComfyUI/models/diffusion_models/"
    },
    "clip": {
        "name": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "repo": "Comfy-Org/Qwen-Image_ComfyUI",
        "filename": "split_files/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "size_gb": 8.8,
        "container_dir": "/workspace/ComfyUI/models/text_encoders/"
    },
    "vae": {
        "name": "qwen_image_vae.safetensors",
        "repo": "Comfy-Org/Qwen-Image_ComfyUI",
        "filename": "split_files/vae/qwen_image_vae.safetensors",
        "size_gb": 0.243,
        "container_dir": "/workspace/ComfyUI/models/vae/"
    }
}

# Chemins WSL et Windows
WSL_COMFYUI_PATH = "/home/jesse/SD/workspace/comfyui-qwen"
WSL_CUSTOM_NODES = f"{WSL_COMFYUI_PATH}/ComfyUI/custom_nodes"
WINDOWS_SECRETS = Path(".secrets")
BCRYPT_TOKEN_FILE = WINDOWS_SECRETS / "qwen-api-user.token"


class QwenSetup:
    """Gestionnaire d'installation complète du système Qwen."""

    def __init__(self, args):
        self.args = args
        self.report_data = {
            "timestamp_start": datetime.now().isoformat(),
            "steps": [],
            "errors": [],
            "status": "IN_PROGRESS"
        }

    def run(self) -> bool:
        """Exécute toutes les étapes d'installation."""
        steps = [
            ("Vérification prérequis", self.check_prerequisites, "prerequisites"),
            ("Démarrage container Docker", self.start_docker_container, "docker"),
            ("Installation ComfyUI-Login", self.install_comfyui_login, "auth"),
            ("Téléchargement modèles FP8", self.download_models, "models"),
            ("Configuration authentification", self.configure_auth, "config"),
            ("Test génération image", self.test_image_generation, "test"),
        ]

        success = True
        for step_name, step_func, step_key in steps:
            logger.info(f"\n{'='*60}\n{step_name}\n{'='*60}")
            
            # Vérifier si l'étape doit être sautée
            skip_key = f"skip_{step_key}"
            if hasattr(self.args, skip_key) and getattr(self.args, skip_key):
                logger.info(f"⏭️  Étape sautée (flag --skip-{step_key})")
                self.report_data["steps"].append({
                    "name": step_name,
                    "status": "SKIPPED",
                    "timestamp": datetime.now().isoformat()
                })
                continue

            try:
                step_success = step_func()
                status = "SUCCESS" if step_success else "FAILED"
                self.report_data["steps"].append({
                    "name": step_name,
                    "status": status,
                    "timestamp": datetime.now().isoformat()
                })
                
                if not step_success:
                    logger.error(f"❌ Échec de l'étape: {step_name}")
                    success = False
                    break
                else:
                    logger.info(f"✅ {step_name} complété")
            except Exception as e:
                logger.error(f"❌ Exception dans {step_name}: {e}")
                self.report_data["errors"].append({
                    "step": step_name,
                    "error": str(e),
                    "timestamp": datetime.now().isoformat()
                })
                success = False
                break

        self.report_data["timestamp_end"] = datetime.now().isoformat()
        self.report_data["status"] = "SUCCESS" if success else "FAILED"
        self.generate_report()
        
        return success

    def check_prerequisites(self) -> bool:
        """Vérifie et installe automatiquement les prérequis manquants."""
        logger.info("Vérification de Docker...")
        try:
            result = subprocess.run(
                ["docker", "--version"],
                capture_output=True,
                text=True,
                check=True
            )
            logger.info(f"✅ Docker installé: {result.stdout.strip()}")
        except (subprocess.CalledProcessError, FileNotFoundError):
            logger.error("❌ Docker non installé ou inaccessible")
            return False

        logger.info("Vérification de Python...")
        try:
            result = subprocess.run(
                [sys.executable, "--version"],
                capture_output=True,
                text=True,
                check=True
            )
            logger.info(f"✅ Python installé: {result.stdout.strip()}")
        except (subprocess.CalledProcessError, FileNotFoundError):
            logger.error("❌ Python non installé ou inaccessible")
            return False

        logger.info("Vérification de huggingface-hub...")
        
        # Vérifier via import Python (plus fiable que CLI Windows)
        try:
            import huggingface_hub
            logger.info(f"✅ huggingface-hub déjà installé: {huggingface_hub.__version__}")
        except ImportError:
            logger.warning("⚠️ huggingface-hub non installé, installation automatique...")
            
            # Installation automatique via pip
            try:
                install_result = subprocess.run(
                    [sys.executable, "-m", "pip", "install", "huggingface-hub"],
                    capture_output=True,
                    text=True,
                    check=True
                )
                logger.info("✅ huggingface-hub installé avec succès")
                
                # Vérification post-installation via import
                try:
                    import huggingface_hub
                    logger.info(f"✅ huggingface-hub vérifié: {huggingface_hub.__version__}")
                except ImportError:
                    logger.error("❌ huggingface-hub toujours inaccessible après installation")
                    return False
                
            except subprocess.CalledProcessError as e:
                logger.error(f"❌ Échec installation huggingface-hub: {e.stderr}")
                return False

        return True

    def start_docker_container(self) -> bool:
        """Démarre le container comfyui-qwen via docker-compose."""
        if self.args.skip_docker:
            return True
        
        logger.info(f"Vérification état container {DOCKER_CONTAINER_NAME}...")
        try:
            result = subprocess.run(
                ["docker", "ps", "--filter", f"name={DOCKER_CONTAINER_NAME}", "--format", "{{.Names}}"],
                capture_output=True,
                text=True,
                check=True
            )
            
            if DOCKER_CONTAINER_NAME in result.stdout:
                logger.info(f"✅ Container {DOCKER_CONTAINER_NAME} déjà en cours")
                return True
            
            logger.info(f"Démarrage du container {DOCKER_CONTAINER_NAME}...")
            result = subprocess.run(
                ["docker-compose", "up", "-d", DOCKER_CONTAINER_NAME],
                cwd="docker-configurations/comfyui-qwen",
                capture_output=True,
                text=True,
                check=True
            )
            
            # Attendre que le port 8188 soit accessible
            logger.info(f"Attente que ComfyUI soit accessible sur port {COMFYUI_PORT}...")
            import requests
            max_attempts = 30
            for i in range(max_attempts):
                try:
                    response = requests.get(f"http://{COMFYUI_HOST}:{COMFYUI_PORT}/", timeout=2)
                    if response.status_code in [200, 401]:  # 401 = auth requise (OK)
                        logger.info(f"✅ ComfyUI accessible après {i+1} tentatives")
                        return True
                except requests.RequestException:
                    time.sleep(2)
            
            logger.error(f"❌ ComfyUI non accessible après {max_attempts} tentatives")
            return False
            
        except subprocess.CalledProcessError as e:
            logger.error(f"❌ Erreur Docker: {e.stderr}")
            return False

    def install_comfyui_login(self) -> bool:
        """Installe le custom node ComfyUI-Login pour authentification."""
        if self.args.skip_auth:
            return True
        
        logger.info("Installation de ComfyUI-Login...")
        
        # Appeler le script existant en subprocess
        script_path = Path("scripts/genai-auth/core/install_comfyui_with_auth.py")
        if not script_path.exists():
            logger.error(f"❌ Script install_comfyui_with_auth.py non trouvé: {script_path}")
            return False
        
        try:
            result = subprocess.run(
                [sys.executable, str(script_path)],
                capture_output=True,
                text=True,
                timeout=600
            )
            
            if result.returncode == 0:
                logger.info("✅ ComfyUI-Login installé avec succès")
                return True
            else:
                logger.error(f"❌ Échec installation ComfyUI-Login")
                logger.error(f"stderr: {result.stderr}")
                return False
                
        except subprocess.TimeoutExpired:
            logger.error("❌ Timeout installation ComfyUI-Login (>600s)")
            return False
        except Exception as e:
            logger.error(f"❌ Exception installation ComfyUI-Login: {e}")
            return False

    def download_models(self) -> bool:
        """Télécharge les modèles FP8 officiels Comfy-Org."""
        if self.args.skip_models:
            return True
        
        logger.info("Téléchargement des modèles FP8...")
        
        # Vérifier token HuggingFace
        token_file = Path(".secrets/.env.huggingface")
        if not token_file.exists():
            logger.error(f"❌ Token HuggingFace non trouvé: {token_file}")
            return False
        
        try:
            from huggingface_hub import hf_hub_download
        except ImportError:
            logger.error("❌ huggingface_hub non installé (pip install huggingface-hub)")
            return False
        
        # Charger token
        with open(token_file) as f:
            content = f.read().strip()
            token = content.split("=", 1)[1].strip() if "=" in content else content.strip()
        
        logger.info(f"✅ Token HuggingFace chargé")
        
        # Télécharger chaque modèle
        for model_type, model_info in QWEN_MODELS.items():
            logger.info(f"\n📥 Téléchargement {model_type.upper()}: {model_info['name']} ({model_info['size_gb']:.2f} GB)")
            
            # Vérifier si déjà présent dans le container
            check_cmd = [
                "docker", "exec", DOCKER_CONTAINER_NAME,
                "test", "-f", f"{model_info['container_dir']}{model_info['name']}"
            ]
            result = subprocess.run(check_cmd, capture_output=True)
            
            if result.returncode == 0:
                logger.info(f"✅ {model_type.upper()} déjà présent dans le container")
                continue
            
            # Télécharger via HuggingFace Hub
            try:
                local_file = hf_hub_download(
                    repo_id=model_info["repo"],
                    filename=model_info["filename"],
                    token=token,
                    local_dir=f"./temp_qwen_download/{model_type}",
                    local_dir_use_symlinks=False
                )
                logger.info(f"✅ Téléchargé: {local_file}")
                
                # Copier dans le container
                src_file = Path(local_file)
                dest_path = f"{model_info['container_dir']}{model_info['name']}"
                
                logger.info(f"📋 Copie vers container: {dest_path}")
                copy_cmd = [
                    "docker", "cp",
                    str(src_file),
                    f"{DOCKER_CONTAINER_NAME}:{dest_path}"
                ]
                subprocess.run(copy_cmd, check=True, capture_output=True)
                logger.info(f"✅ {model_type.upper()} copié dans le container")
                
            except Exception as e:
                logger.error(f"❌ Erreur téléchargement {model_type}: {e}")
                return False
        
        logger.info("✅ Tous les modèles FP8 installés")
        return True

    def configure_auth(self) -> bool:
        """Configure l'authentification bcrypt avec synchroniseur unifié."""
        logger.info("Configuration de l'authentification avec synchroniseur unifié...")
        
        try:
            # Importer et utiliser le synchroniseur unifié
            from ..utils.token_synchronizer import TokenSynchronizer
            
            # Créer le synchroniseur
            synchronizer = TokenSynchronizer()
            
            # Exécuter l'unification complète
            logger.info("🔄 Lancement de l'unification des tokens...")
            success = synchronizer.run_complete_unification()
            
            if success:
                logger.info("✅ Authentification unifiée et configurée avec succès")
                return True
            else:
                logger.error("❌ Échec de l'unification des tokens")
                return False
                
        except Exception as e:
            logger.error(f"❌ Erreur configuration authentification: {e}")
            return False

    def test_image_generation(self) -> bool:
        """Teste la génération d'image end-to-end.
        
        CORRECTION CRITIQUE (2025-11-06):
        - La logique précédente retournait systématiquement True même en cas d'échec
        - Cela générait des faux positifs dans les rapports d'installation
        - Nouvelle politique: échec du test = échec de l'installation (retourne False)
        """
        if self.args.skip_test:
            logger.info("⏭️ Test de génération d'image sauté (flag --skip-test)")
            return True
        
        logger.info("Test de génération d'image...")
        
        # Appeler le script de test consolidé (PRINCIPE SDDD)
        script_path = Path("scripts/genai-auth/utils/test_generation_image_fp8_officiel.py")
        
        if not script_path.exists():
            logger.error(f"❌ Script de test non trouvé: {script_path}")
            logger.error("❌ Test de génération d'image impossible sans script de test")
            logger.error("💡 Solution: Installer le script de test ou utiliser --skip-test")
            # ANCIENNE LOGIQUE: return True  # Ne pas bloquer l'installation
            # NOUVELLE LOGIQUE: return False  # Échec du test = échec de l'installation
            return False
        
        try:
            logger.info(f"🔄 Exécution du script de test: {script_path}")
            result = subprocess.run(
                [sys.executable, str(script_path)],
                capture_output=True,
                text=True,
                timeout=600
            )
            
            # Logging détaillé pour diagnostic
            if result.stdout:
                logger.info(f"📋 STDOUT du script de test:\n{result.stdout}")
            if result.stderr:
                logger.warning(f"⚠️ STDERR du script de test:\n{result.stderr}")
            
            if result.returncode == 0:
                logger.info("✅ Test de génération d'image réussi")
                logger.info("🎯 ComfyUI est fonctionnel et prêt à générer des images")
                return True
            else:
                logger.error(f"❌ Test de génération d'image échoué (code {result.returncode})")
                logger.error("❌ ComfyUI n'est pas fonctionnel - installation incomplète")
                logger.error("💡 Actions recommandées:")
                logger.error("   1. Vérifier les logs du script de test ci-dessus")
                logger.error("   2. Valider que ComfyUI est accessible sur http://localhost:8188")
                logger.error("   3. Vérifier l'installation des modèles FP8")
                logger.error("   4. Confirmer la configuration d'authentification")
                # ANCIENNE LOGIQUE: return True  # Ne pas bloquer l'installation
                # NOUVELLE LOGIQUE: return False  # Échec du test = échec de l'installation
                return False
                
        except subprocess.TimeoutExpired:
            logger.error("❌ Timeout test génération (>600s)")
            logger.error("❌ ComfyUI ne répond pas dans un délai raisonnable")
            logger.error("💡 Causes possibles: problèmes de ressources, modèles non chargés, configuration incorrecte")
            # ANCIENNE LOGIQUE: return True  # Ne pas bloquer l'installation
            # NOUVELLE LOGIQUE: return False  # Échec du test = échec de l'installation
            return False
        except Exception as e:
            logger.error(f"❌ Exception critique lors du test de génération: {e}")
            logger.error(f"❌ Type d'exception: {type(e).__name__}")
            logger.error("❌ Le test n'a pas pu s'exécuter correctement")
            logger.error("💡 Vérifier l'environnement Python et les dépendances")
            # ANCIENNE LOGIQUE: return True  # Ne pas bloquer l'installation
            # NOUVELLE LOGIQUE: return False  # Échec du test = échec de l'installation
            return False

    def generate_report(self):
        """Génère un rapport d'installation."""
        report_dir = Path(self.args.report_dir) if self.args.report_dir else Path("rapports")
        report_dir.mkdir(parents=True, exist_ok=True)
        
        timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        report_path = report_dir / f"installation-qwen-{timestamp}.json"
        
        with open(report_path, 'w', encoding='utf-8') as f:
            json.dump(self.report_data, f, indent=2, ensure_ascii=False)
        
        logger.info(f"\n📄 Rapport d'installation généré: {report_path}")
        
        # Afficher résumé
        logger.info("\n" + "="*60)
        logger.info("RÉSUMÉ DE L'INSTALLATION")
        logger.info("="*60)
        logger.info(f"Statut: {self.report_data['status']}")
        logger.info(f"Début: {self.report_data['timestamp_start']}")
        logger.info(f"Fin: {self.report_data['timestamp_end']}")
        logger.info(f"\nÉtapes:")
        for step in self.report_data["steps"]:
            status_emoji = "✅" if step["status"] == "SUCCESS" else "⏭️" if step["status"] == "SKIPPED" else "❌"
            logger.info(f"  {status_emoji} {step['name']}: {step['status']}")
        
        if self.report_data["errors"]:
            logger.error(f"\nErreurs ({len(self.report_data['errors'])}): ")
            for error in self.report_data["errors"]:
                logger.error(f"  - {error['step']}: {error['error']}")


def main():
    parser = argparse.ArgumentParser(
        description="Wrapper d'installation complète du système Qwen (Phase 29)",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('--skip-docker', action='store_true', help="Ne pas démarrer le container Docker")
    parser.add_argument('--skip-models', action='store_true', help="Ne pas télécharger les modèles")
    parser.add_argument('--skip-auth', action='store_true', help="Ne pas installer ComfyUI-Login")
    parser.add_argument('--skip-test', action='store_true', help="Ne pas exécuter le test de génération d'image")
    parser.add_argument('--report-dir', type=str, default="rapports", help="Répertoire de génération du rapport")
    
    # Ajouter des flags simplifiés pour mapping
    parser.add_argument('--skip-prerequisites', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--skip-config', action='store_true', help=argparse.SUPPRESS)
    
    args = parser.parse_args()
    
    logger.info("="*60)
    logger.info("WRAPPER D'INSTALLATION COMPLÈTE QWEN - PHASE 29")
    logger.info("="*60)
    
    setup = QwenSetup(args)
    success = setup.run()
    
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()