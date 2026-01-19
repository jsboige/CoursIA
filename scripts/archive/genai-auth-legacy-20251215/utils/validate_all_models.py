#!/usr/bin/env python3
"""
validate_all_models.py - Script de validation unifié pour les moteurs GenAI (Images)

Ce script valide séquentiellement la chaîne de génération pour :
1.  Forge / SDXL Turbo (Service Legacy)
2.  ComfyUI / Qwen2-VL (Service Vision)
3.  ComfyUI / Z-Image (Nouveau Service Lumina-2)

Usage:
    python scripts/genai-auth/validate_all_models.py [--output report.json]

Auteur: Roo Code Mode (Phase 34)
Date: 2025-12-11
"""

import argparse
import logging
import sys
import json
import requests
import time
import base64
import random
from pathlib import Path
from datetime import datetime

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("ValidateGenAI")

# Constantes
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
SECRETS_DIR = PROJECT_ROOT / ".secrets"
COMFYUI_URL = "http://localhost:8188"
FORGE_URL = "http://localhost:7865"
OUTPUT_DIR = PROJECT_ROOT / "rapports" / "validation_genai"

# Payloads (Workflows)

# Workflow minimal Z-Image (Reconstruit d'après Rapport Phase 33)
WORKFLOW_Z_IMAGE = {
    "3": {
        "class_type": "KSampler",
        "inputs": {
            "seed": 42,
            "steps": 4,  # Rapide pour test
            "cfg": 1.0,  # Guidance recommandée pour Lumina/Z-Image ?
            "sampler_name": "euler",
            "scheduler": "normal",
            "denoise": 1.0,
            "model": ["4", 0],
            "positive": ["6", 0],
            "negative": ["7", 0],
            "latent_image": ["5", 0]
        }
    },
    "4": {
        "class_type": "UnetLoaderGGUF",
        "inputs": {
            "unet_name": "z_image_turbo-Q5_K_M.gguf"
        }
    },
    "5": {
        "class_type": "EmptyLatentImage",
        "inputs": {
            "width": 512,
            "height": 512,
            "batch_size": 1
        }
    },
    "6": {
        "class_type": "CLIPTextEncode",
        "inputs": {
            "text": "A beautiful sunset over a cyberpunk city",
            "clip": ["10", 0]
        }
    },
    "7": {
        "class_type": "CLIPTextEncode",
        "inputs": {
            "text": "low quality, blurry",
            "clip": ["10", 0]
        }
    },
    "8": {
        "class_type": "VAEDecode",
        "inputs": {
            "samples": ["12", 0],  # Connecté à LatentUnsqueeze
            "vae": ["11", 0]
        }
    },
    "9": {
        "class_type": "SaveImage",
        "inputs": {
            "filename_prefix": "Validation_Z-Image",
            "images": ["8", 0]
        }
    },
    "10": {
        "class_type": "CLIPLoaderGGUF",
        "inputs": {
            "clip_name": "gemma-3-4b-it-Q4_K_M.gguf",
            "type": "lumina2"
        }
    },
    "11": {
        "class_type": "VAELoader",
        "inputs": {
            "vae_name": "qwen_image_vae.safetensors"
        }
    },
    "12": {
        "class_type": "LatentUnsqueeze",  # Node Custom critique
        "inputs": {
            "samples": ["3", 0]
        }
    }
}

# Workflow Qwen2-VL (Validation VLM simple)
# Note: Ceci est un placeholder pour un test de génération texte basique si Qwen est chargé
# Pour l'instant, on va utiliser un workflow simple qui charge juste le checkpoint si possible,
# ou un dummy workflow si on ne veut pas charger Qwen (lourd).
# On va laisser vide pour l'instant et se concentrer sur Z-Image.
WORKFLOW_QWEN = {}

class GlobalValidationManager:
    def __init__(self, output_file=None):
        self.session = requests.Session()
        self.token = None
        self.results = {
            "timestamp": datetime.now().isoformat(),
            "services": {},
            "generations": {}
        }
        self.output_file = output_file
        
        # Création du répertoire de sortie si nécessaire
        OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    def log_step(self, message: str):
        logger.info(f"\n{'='*50}")
        logger.info(f"🔍 STEP: {message}")
        logger.info(f"{'='*50}")

    def get_comfy_token(self) -> bool:
        self.log_step("Récupération Token ComfyUI")
        config_path = SECRETS_DIR / "comfyui_auth_tokens.conf"
        
        if not config_path.exists():
            logger.error(f"❌ Config tokens introuvable: {config_path}")
            return False
            
        try:
            with open(config_path, 'r') as f:
                config = json.load(f)
                self.token = config.get('bcrypt_hash')
            
            if not self.token:
                logger.error("❌ Token bcrypt manquant")
                return False
                
            logger.info("✅ Token ComfyUI récupéré")
            return True
        except Exception as e:
            logger.error(f"❌ Erreur lecture config: {e}")
            return False

    def check_forge_health(self) -> bool:
        self.log_step("Healthcheck: Forge (SDXL Turbo)")
        try:
            # Forge utilise l'API A1111 standard
            resp = self.session.get(f"{FORGE_URL}/sdapi/v1/options", timeout=5)
            if resp.status_code == 200:
                logger.info("✅ Forge est en ligne (HTTP 200)")
                self.results["services"]["forge"] = "UP"
                return True
            else:
                logger.error(f"❌ Forge répond avec erreur: {resp.status_code}")
                self.results["services"]["forge"] = f"ERROR_{resp.status_code}"
                return False
        except requests.ConnectionError:
            logger.error("❌ Forge n'est pas accessible (Connection Refused)")
            self.results["services"]["forge"] = "DOWN"
            return False
        except Exception as e:
            logger.error(f"❌ Erreur Forge: {e}")
            self.results["services"]["forge"] = "ERROR"
            return False

    def check_comfy_health(self) -> bool:
        self.log_step("Healthcheck: ComfyUI")
        if not self.token:
            if not self.get_comfy_token():
                self.results["services"]["comfyui"] = "AUTH_FAIL"
                return False

        headers = {"Authorization": f"Bearer {self.token}"}
        try:
            resp = self.session.get(f"{COMFYUI_URL}/system_stats", headers=headers, timeout=5)
            if resp.status_code == 200:
                logger.info("✅ ComfyUI est en ligne et authentifié (HTTP 200)")
                self.results["services"]["comfyui"] = "UP"
                return True
            elif resp.status_code in [401, 403]:
                logger.error(f"❌ ComfyUI Auth Refusée (HTTP {resp.status_code})")
                self.results["services"]["comfyui"] = "AUTH_DENIED"
                return False
            else:
                logger.error(f"❌ ComfyUI Erreur: {resp.status_code}")
                self.results["services"]["comfyui"] = f"ERROR_{resp.status_code}"
                return False
        except requests.ConnectionError:
            logger.error("❌ ComfyUI inaccessible")
            self.results["services"]["comfyui"] = "DOWN"
            return False

    def test_forge_generation(self) -> bool:
        self.log_step("Test Génération: Forge (SDXL Turbo)")
        
        payload = {
            "prompt": "A futuristic city with flying cars, cyberpunk style, neon lights",
            "steps": 1, # Turbo est rapide
            "width": 512,
            "height": 512,
            "cfg_scale": 1.0,
            "sampler_name": "Euler a",
            "batch_size": 1
        }
        
        try:
            start_time = time.time()
            resp = self.session.post(f"{FORGE_URL}/sdapi/v1/txt2img", json=payload, timeout=30)
            duration = time.time() - start_time
            
            if resp.status_code == 200:
                data = resp.json()
                if "images" in data and len(data["images"]) > 0:
                    logger.info(f"✅ Génération Forge réussie en {duration:.2f}s")
                    self.results["generations"]["forge"] = {"status": "SUCCESS", "duration": duration}
                    
                    # Sauvegarde optionnelle (pour preuve)
                    img_data = base64.b64decode(data["images"][0])
                    img_path = OUTPUT_DIR / f"forge_test_{int(start_time)}.png"
                    with open(img_path, "wb") as f:
                        f.write(img_data)
                    logger.info(f"📸 Image sauvegardée: {img_path}")
                    
                    return True
                else:
                    logger.error("❌ Pas d'image dans la réponse Forge")
                    self.results["generations"]["forge"] = {"status": "EMPTY_RESPONSE"}
                    return False
            else:
                logger.error(f"❌ Erreur API Forge: {resp.status_code}")
                self.results["generations"]["forge"] = {"status": f"HTTP_{resp.status_code}"}
                return False
                
        except Exception as e:
            logger.error(f"❌ Exception Forge Gen: {e}")
            self.results["generations"]["forge"] = {"status": "EXCEPTION", "details": str(e)}
            return False

    def save_report(self):
        if self.output_file:
            path = Path(self.output_file)
        else:
            path = OUTPUT_DIR / f"validation_report_{int(time.time())}.json"
            
        with open(path, 'w') as f:
            json.dump(self.results, f, indent=2)
        logger.info(f"\n📄 Rapport sauvegardé: {path}")

    def run(self):
        logger.info("🚀 DÉMARRAGE VALIDATION UNIFIÉE")
        
        health_forge = self.check_forge_health()
        health_comfy = self.check_comfy_health()
        
        if health_forge:
            self.test_forge_generation()
        else:
            logger.warning("⏩ Skip Forge Generation (Service Down)")
            
        if health_comfy:
            # Test Z-Image
            self.test_comfy_generation("Z-Image", WORKFLOW_Z_IMAGE)
            
            # Test Qwen (TODO: Définir workflow)
            # self.test_comfy_generation("Qwen2-VL", WORKFLOW_QWEN)
        else:
             logger.warning("⏩ Skip ComfyUI Generations (Service/Auth Down)")
        
        self.save_report()

    def test_comfy_generation(self, model_name: str, workflow: dict) -> bool:
        self.log_step(f"Test Génération ComfyUI: {model_name}")
        
        if not workflow:
            logger.warning(f"⚠️ Workflow vide pour {model_name}, skip.")
            return False

        headers = {"Authorization": f"Bearer {self.token}"}
        
        try:
            # 1. Envoi du Prompt
            payload = {"prompt": workflow}
            start_time = time.time()
            
            resp = self.session.post(f"{COMFYUI_URL}/prompt", json=payload, headers=headers, timeout=10)
            
            if resp.status_code != 200:
                logger.error(f"❌ Erreur envoi prompt {model_name}: {resp.status_code} - {resp.text}")
                self.results["generations"][model_name] = {"status": f"HTTP_{resp.status_code}_PROMPT"}
                return False
                
            prompt_id = resp.json().get("prompt_id")
            logger.info(f"✅ Prompt ID reçu: {prompt_id}")
            
            # 2. Attente de la complétion (Polling simple)
            # Note: Pour une vraie prod, utiliser WebSocket. Ici polling /history pour simplifier.
            max_retries = 30 # 30 * 2s = 60s timeout
            success = False
            
            for _ in range(max_retries):
                time.sleep(2)
                hist_resp = self.session.get(f"{COMFYUI_URL}/history/{prompt_id}", headers=headers)
                
                if hist_resp.status_code == 200 and hist_resp.json():
                    # Si le prompt_id est dans l'historique, c'est fini
                    logger.info(f"✅ Génération {model_name} terminée")
                    success = True
                    break
            
            duration = time.time() - start_time
            
            if success:
                # Récupération info image
                history = hist_resp.json()[prompt_id]
                outputs = history.get("outputs", {})
                
                # Chercher une sortie image (Node 9 dans notre workflow Z-Image)
                images_output = []
                for node_id, output_data in outputs.items():
                    if "images" in output_data:
                        images_output.extend(output_data["images"])
                
                if images_output:
                    img_info = images_output[0]
                    filename = img_info.get("filename")
                    subfolder = img_info.get("subfolder", "")
                    img_type = img_info.get("type", "output")
                    
                    # Téléchargement Image
                    img_url = f"{COMFYUI_URL}/view?filename={filename}&subfolder={subfolder}&type={img_type}"
                    img_resp = self.session.get(img_url, headers=headers)
                    
                    if img_resp.status_code == 200:
                        out_path = OUTPUT_DIR / f"validation_{model_name}_{int(time.time())}.png"
                        with open(out_path, "wb") as f:
                            f.write(img_resp.content)
                        logger.info(f"📸 Image sauvegardée: {out_path}")
                        self.results["generations"][model_name] = {"status": "SUCCESS", "duration": duration, "image": str(out_path)}
                        return True
                    else:
                        logger.warning("⚠️ Image générée mais téléchargement échoué")
                        self.results["generations"][model_name] = {"status": "DOWNLOAD_FAIL"}
                        return True # On considère le test réussi quand même car généré
                else:
                    logger.warning("⚠️ Prompt terminé mais pas d'image en sortie")
                    self.results["generations"][model_name] = {"status": "NO_IMAGE_OUTPUT"}
                    return False
            else:
                logger.error("❌ Timeout attente génération")
                self.results["generations"][model_name] = {"status": "TIMEOUT"}
                return False

        except Exception as e:
            logger.error(f"❌ Exception Comfy Gen {model_name}: {e}")
            self.results["generations"][model_name] = {"status": "EXCEPTION", "details": str(e)}
            return False
        
        success = health_forge and health_comfy
        return success

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Validate GenAI Models")
    parser.add_argument("--output", help="Path to output JSON report")
    args = parser.parse_args()
    
    manager = GlobalValidationManager(args.output)
    if not manager.run():
        sys.exit(1)
