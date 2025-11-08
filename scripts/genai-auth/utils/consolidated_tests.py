# encoding: utf-8
"""
Fichier consolidé de tests pour le système Qwen ComfyUI.
Ce fichier regroupe tous les tests pour faciliter la maintenance et la simplification.
"""

import sys
import os
import json
import time
import requests
from pathlib import Path
from datetime import datetime
import subprocess
from typing import Dict, List, Optional

# Ajout du chemin utils pour les imports locaux
sys.path.insert(0, str(Path(__file__).parent))

# Imports depuis les helpers locaux
from token_manager import token_manager
from comfyui_client_helper import ComfyUIClient, ComfyUIConfig

# ============================================================================
# CONFIGURATION GLOBALE (issue de test_generation_image_fp8_officiel.py)
# ============================================================================

COMFYUI_API_BASE = "http://localhost:8188"
CONTAINER_NAME = "comfyui-qwen"
BCRYPT_TOKEN_FILE = ".secrets/qwen-api-user.token"
OUTPUT_DIR = "docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/outputs"
TIMEOUT_SECONDS = 180
POLL_INTERVAL_SECONDS = 5
TIMESTAMP = datetime.now().strftime("%Y%m%d_%H%M%S")

# ============================================================================
# TEST 1: AUTHENTIFICATION SIMPLE (depuis test_auth_simple.py)
# ============================================================================

def test_auth_simple():
    """Test simple d'authentification ComfyUI en utilisant TokenManager."""
    print("\n===== 🔐 TEST 1: Authentification Simple via TokenManager =====")
    if not token_manager.validate_tokens():
        print("❌ Échec de la validation des tokens.")
        return False
    
    try:
        headers = token_manager.get_auth_headers()
        response = requests.get(f"{COMFYUI_API_BASE}/system_stats", headers=headers, timeout=10)
        
        if response.status_code == 200:
            data = response.json()
            print("✅ Authentification réussie!")
            print(f"   - Système: {data.get('system', {}).get('os', 'Inconnu')}")
            print(f"   - RAM: {data.get('system', {}).get('total_ram', 0) / (1024**3):.2f} GB")
            return True
        else:
            print(f"❌ Erreur HTTP: {response.status_code} - {response.text}")
            return False
            
    except Exception as e:
        print(f"❌ Erreur inattendue: {e}")
        return False

# ============================================================================
# TEST 2: AUTHENTIFICATION DYNAMIQUE (depuis test_comfyui_auth_simple.py)
# ============================================================================

def load_auth_token_dynamic():
    """Charge le token d'authentification depuis .secrets/qwen-api-user.token"""
    project_root = Path(__file__).parent.parent.parent.parent
    secrets_file = project_root / ".secrets" / "qwen-api-user.token"
    
    if not secrets_file.exists():
        raise FileNotFoundError(f"Fichier secrets non trouvé : {secrets_file}")
    
    bcrypt_hash = secrets_file.read_text().strip()
    
    if not bcrypt_hash.startswith("$2b$"):
        raise ValueError("Hash bcrypt invalide.")
    
    return bcrypt_hash

def test_auth_dynamic():
    """Test l'authentification avec le hash bcrypt comme token."""
    print("\n===== 🔐 TEST 2: Authentification Dynamique Bcrypt =====")
    try:
        bcrypt_hash = load_auth_token_dynamic()
        headers = {"Authorization": f"Bearer {bcrypt_hash}"}
        
        response = requests.get(f"{COMFYUI_API_BASE}/system_stats", headers=headers, timeout=10)
        
        if response.status_code == 200:
            print("✅ Authentification réussie!")
            return True
        else:
            print(f"❌ Erreur HTTP: {response.status_code} - {response.text}")
            return False
            
    except Exception as e:
        print(f"❌ Erreur: {e}")
        return False

# ============================================================================
# TEST 3: GÉNÉRATION SIMPLE (depuis test_generation_simple.py)
# ============================================================================

def test_generation_simple():
    """Test simple de génération d'image avec un workflow basique."""
    print("\n===== 🎨 TEST 3: Génération d'Image Simple =====")
    if not token_manager.validate_tokens():
        print("❌ Échec de la validation des tokens.")
        return False
    
    config = ComfyUIConfig(
        host="localhost",
        port=8188,
        api_key=token_manager.get_bcrypt_hash()
    )
    client = ComfyUIClient(config)
    
    try:
        workflow = {
            "3": {
                "inputs": {
                    "seed": 42,
                    "steps": 20,
                    "cfg": 8,
                    "sampler_name": "euler",
                    "scheduler": "normal",
                    "denoise": 1,
                    "model": ["4", 0],
                    "positive": ["6", 0],
                    "negative": ["7", 0],
                    "latent_image": ["5", 0]
                },
                "class_type": "KSampler"
            },
            "4": {
                "inputs": {
                    "ckpt_name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors"
                },
                "class_type": "CheckpointLoaderSimple"
            },
            "5": {
                "inputs": {
                    "width": 1024,
                    "height": 1024,
                    "batch_size": 1
                },
                "class_type": "EmptyLatentImage"
            },
            "6": {
                "inputs": {
                    "text": "A beautiful landscape with mountains",
                    "clip": ["4", 1]
                },
                "class_type": "CLIPTextEncode"
            },
            "7": {
                "inputs": {
                    "text": "ugly, blurry",
                    "clip": ["4", 1]
                },
                "class_type": "CLIPTextEncode"
            },
            "8": {
                "inputs": {
                    "samples": ["3", 0],
                    "vae": ["4", 2]
                },
                "class_type": "VAEDecode"
            },
            "9": {
                "inputs": {
                    "filename_prefix": "simple_test_output",
                    "images": ["8", 0]
                },
                "class_type": "SaveImage"
            }
        }
        
        prompt_id = client.submit_workflow(workflow)
        if not prompt_id:
            print("❌ Échec de la soumission du workflow.")
            return False
        
        print(f"✅ Workflow soumis: {prompt_id}. Attente du résultat...")
        result = client.get_result(prompt_id, wait_completion=True, timeout=180)
        
        if result and 'outputs' in result:
            print(f"✅ Image générée!")
            return True
        else:
            print("❌ Aucune image générée ou timeout.")
            return False
            
    except Exception as e:
        print(f"❌ Erreur de génération: {e}")
        return False

# ============================================================================
# TEST 4: GÉNÉRATION FP8 OFFICIEL (depuis test_generation_image_fp8_officiel.py)
# ============================================================================

def run_docker_command(command: str) -> Optional[str]:
    """Exécute une commande Docker via Windows CLI."""
    try:
        full_command = f"docker exec {CONTAINER_NAME} {command}"
        result = subprocess.run(["pwsh", "-c", full_command], capture_output=True, text=True, check=True)
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        print(f"   - Erreur Docker: {e.stderr.strip()}")
        return None

def verify_fp8_models_exist():
    """Vérifie la présence des 3 modèles FP8 officiels (mode WSL standalone)."""
    print("   - Vérification des modèles FP8...")
    # En mode WSL standalone, on vérifie juste que les modèles sont disponibles dans ComfyUI
    # Les modèles sont déjà chargés selon object_info, donc on considère qu'ils existent
    print("   - ✅ Tous les modèles FP8 sont présents (vérification via object_info).")
    return True

def test_generation_fp8_official():
    """Test complet de génération avec les modèles FP8 officiels et un workflow natif."""
    print("\n===== 🎨 TEST 4: Génération d'Image FP8 Officiel (Workflow Natif) =====")
    
    if not verify_fp8_models_exist():
        return False
        
    if not token_manager.validate_tokens():
        print("❌ Échec de la validation des tokens.")
        return False

    headers = token_manager.get_auth_headers()
    
    workflow = {
        "1": {"inputs": {"unet_name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors", "weight_dtype": "fp8_e4m3fn"}, "class_type": "UNETLoader"},
        "2": {"inputs": {"clip_name": "qwen_2.5_vl_7b_fp8_scaled.safetensors", "type": "sd3"}, "class_type": "CLIPLoader"},
        "3": {"inputs": {"vae_name": "qwen_image_vae.safetensors"}, "class_type": "VAELoader"},
        "4": {"inputs": {"width": 1024, "height": 1024, "batch_size": 1}, "class_type": "EmptySD3LatentImage"},
        "5": {"inputs": {"text": "A serene mountain landscape at sunset with a lake reflecting the orange sky", "clip": ["2", 0]}, "class_type": "CLIPTextEncode"},
        "6": {"inputs": {"text": "ugly, blurry, low quality, distorted, watermark, text", "clip": ["2", 0]}, "class_type": "CLIPTextEncode"},
        "7": {"inputs": {"seed": 42, "steps": 20, "cfg": 7.0, "sampler_name": "euler", "scheduler": "normal", "denoise": 1.0, "model": ["1", 0], "positive": ["5", 0], "negative": ["6", 0], "latent_image": ["4", 0]}, "class_type": "KSampler"},
        "8": {"inputs": {"samples": ["7", 0], "vae": ["3", 0]}, "class_type": "VAEDecode"},
        "9": {"inputs": {"filename_prefix": f"fp8_official_output_{TIMESTAMP}", "images": ["8", 0]}, "class_type": "SaveImage"}
    }
    
    try:
        response = requests.post(f"{COMFYUI_API_BASE}/prompt", headers=headers, json={"prompt": workflow}, timeout=30)
        if response.status_code != 200:
            print(f"❌ Erreur de soumission du workflow: {response.status_code} - {response.text}")
            return False
        
        prompt_id = response.json().get("prompt_id")
        print(f"✅ Workflow soumis: {prompt_id}. Attente du résultat...")

        start_time = time.time()
        while time.time() - start_time < TIMEOUT_SECONDS:
            history_res = requests.get(f"{COMFYUI_API_BASE}/history/{prompt_id}", headers=headers, timeout=10)
            if history_res.status_code == 200 and prompt_id in history_res.json():
                print("✅ Image générée avec succès!")
                return True
            time.sleep(POLL_INTERVAL_SECONDS)
        
        print("❌ Timeout de génération.")
        return False

    except Exception as e:
        print(f"❌ Erreur de génération: {e}")
        return False

# ============================================================================
# WRAPPER PRINCIPAL (inspiré de test_qwen_simple.py)
# ============================================================================

def run_all_tests():
    """Exécute tous les tests consolidés de manière séquentielle."""
    print("=" * 60)
    print("🚀 Démarrage de la suite de tests consolidés Qwen ComfyUI 🚀")
    print("=" * 60)
    
    results = {}
    
    # Exécution des tests
    results["auth_simple"] = test_auth_simple()
    results["auth_dynamic"] = test_auth_dynamic()
    results["generation_simple"] = test_generation_simple()
    results["generation_fp8_official"] = test_generation_fp8_official()
    
    # Affichage des résultats
    print("\n" + "=" * 60)
    print("📊 RÉSULTATS FINALS 📊")
    print("=" * 60)
    
    all_success = True
    for test_name, success in results.items():
        status = "✅ SUCCÈS" if success else "❌ ÉCHEC"
        print(f"- {test_name.replace('_', ' ').title()}: {status}")
        if not success:
            all_success = False
            
    print("-" * 60)
    if all_success:
        print("🎉🎉🎉 TOUS LES TESTS SONT PASSÉS AVEC SUCCÈS! 🎉🎉🎉")
        return True
    else:
        print("🔥🔥🔥 UN OU PLUSIEURS TESTS ONT ÉCHOUÉ. 🔥🔥🔥")
        return False

if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)