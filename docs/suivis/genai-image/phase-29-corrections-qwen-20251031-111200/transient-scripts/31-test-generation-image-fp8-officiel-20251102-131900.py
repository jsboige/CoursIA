#!/usr/bin/env python3
"""
Script de Test FINAL : Génération Image ComfyUI Qwen avec Modèles FP8 Officiels
==================================================================================

Phase 29 - ÉTAPE 31 (FINALE)
Création : 2025-11-02 13:19:00 UTC+1

Objectif :
    Tester la génération d'image avec les 3 modèles FP8 officiels Comfy-Org
    installés dans le rapport 30, utilisant un workflow 100% natif ComfyUI.

Architecture :
    - Workflow : 100% nodes natifs (Load Diffusion Model, Load CLIP, Load VAE)
    - Modèles installés (Rapport 30) :
      * Diffusion : qwen_image_edit_2509_fp8_e4m3fn.safetensors (20GB)
      * Text Encoder : qwen_2.5_vl_7b_fp8_scaled.safetensors (8.8GB)
      * VAE : qwen_image_vae.safetensors (243MB)
    - Authentification : Hash bcrypt validé (Rapport 18)
    - Container Docker : comfyui-qwen (Windows CLI)
    - API ComfyUI : http://localhost:8188

Workflow Natif ComfyUI :
    1. Load Diffusion Model → qwen_image_edit_2509_fp8_e4m3fn.safetensors
    2. Load CLIP → qwen_2.5_vl_7b_fp8_scaled.safetensors
    3. Load VAE → qwen_image_vae.safetensors
    4. EmptySD3LatentImage → 1024x1024
    5. CLIP Text Encode (Positive) → Prompt utilisateur
    6. CLIP Text Encode (Negative) → Prompt négatif
    7. KSampler → euler, 20 steps, CFG 7.0
    8. VAE Decode → Décodage latent
    9. Save Image → qwen_fp8_validation_YYYYMMDD_HHMMSS.png

Contraintes ABSOLUES :
    ✅ Utiliser UNIQUEMENT les loaders natifs ComfyUI
    ✅ PAS de custom nodes Qwen (QwenVLCLIPLoader, etc.)
    ✅ Vérifier présence des 3 modèles FP8 officiels AVANT soumission
    ✅ Logger CHAQUE étape avec statut clair
    ✅ Copier image générée vers outputs/

Références :
    - Rapport 30 : Installation modèles FP8 officiels
    - Rapport 26 : Documentation officielle ComfyUI Qwen
    - Rapport 18 : Résolution authentification ComfyUI-Login
"""

import json
import os
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional

import requests

# ============================================================================
# CONFIGURATION GLOBALE
# ============================================================================

COMFYUI_API_BASE = "http://localhost:8188"
CONTAINER_NAME = "comfyui-qwen"
BCRYPT_TOKEN_FILE = ".secrets/qwen-api-user.token"
OUTPUT_DIR = "docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/outputs"
TIMEOUT_SECONDS = 600  # 10 minutes (modèle FP8 peut être plus lent)
POLL_INTERVAL_SECONDS = 5

# Timestamp pour nommage unique
TIMESTAMP = datetime.now().strftime("%Y%m%d_%H%M%S")

# ============================================================================
# WORKFLOW JSON NATIF COMFYUI - MODÈLES FP8 OFFICIELS
# ============================================================================

# Architecture basée sur documentation officielle ComfyUI (Rapport 26)
# Utilise UNIQUEMENT des nodes natifs ComfyUI sans custom nodes

WORKFLOW_TEMPLATE = {
    "1": {
        "inputs": {
            "unet_name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
            "weight_dtype": "fp8_e4m3fn"
        },
        "class_type": "UNETLoader",
        "_meta": {"title": "Load Diffusion Model"}
    },
    "2": {
        "inputs": {
            "clip_name": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
            "type": "sd3"
        },
        "class_type": "CLIPLoader",
        "_meta": {"title": "Load CLIP"}
    },
    "3": {
        "inputs": {
            "vae_name": "qwen_image_vae.safetensors"
        },
        "class_type": "VAELoader",
        "_meta": {"title": "Load VAE"}
    },
    "4": {
        "inputs": {
            "width": 1024,
            "height": 1024,
            "batch_size": 1
        },
        "class_type": "EmptySD3LatentImage",
        "_meta": {"title": "Empty SD3 Latent Image"}
    },
    "5": {
        "inputs": {
            "text": "A serene mountain landscape at sunset with a lake reflecting the orange sky",
            "clip": ["2", 0]
        },
        "class_type": "CLIPTextEncode",
        "_meta": {"title": "CLIP Text Encode (Positive)"}
    },
    "6": {
        "inputs": {
            "text": "ugly, blurry, low quality, distorted, watermark, text",
            "clip": ["2", 0]
        },
        "class_type": "CLIPTextEncode",
        "_meta": {"title": "CLIP Text Encode (Negative)"}
    },
    "7": {
        "inputs": {
            "seed": 42,
            "steps": 20,
            "cfg": 7.0,
            "sampler_name": "euler",
            "scheduler": "normal",
            "denoise": 1.0,
            "model": ["1", 0],
            "positive": ["5", 0],
            "negative": ["6", 0],
            "latent_image": ["4", 0]
        },
        "class_type": "KSampler",
        "_meta": {"title": "KSampler"}
    },
    "8": {
        "inputs": {
            "samples": ["7", 0],
            "vae": ["3", 0]
        },
        "class_type": "VAEDecode",
        "_meta": {"title": "VAE Decode"}
    },
    "9": {
        "inputs": {
            "filename_prefix": f"qwen_fp8_validation_{TIMESTAMP}",
            "images": ["8", 0]
        },
        "class_type": "SaveImage",
        "_meta": {"title": "Save Image"}
    }
}

# ============================================================================
# FONCTIONS UTILITAIRES
# ============================================================================

def print_section(title: str, level: int = 1) -> None:
    """Affiche une section formatée."""
    separator = "=" * 80 if level == 1 else "-" * 80
    print(f"\n{separator}")
    print(f"{title}")
    print(f"{separator}\n")


def print_status(status: str, message: str) -> None:
    """Affiche un statut avec emoji."""
    emoji = "✅" if status == "success" else "❌" if status == "error" else "⚠️"
    print(f"{emoji} {message}")


def run_docker_command(command: str) -> Optional[str]:
    """
    Exécute une commande Docker via Windows CLI.
    
    Args:
        command: Commande à exécuter dans le container
        
    Returns:
        Sortie de la commande ou None en cas d'erreur
    """
    try:
        full_command = f"docker exec {CONTAINER_NAME} {command}"
        result = subprocess.run(
            ["pwsh", "-c", full_command],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        print_status("error", f"Erreur Docker : {e.stderr}")
        return None


def load_auth_token() -> Optional[str]:
    """
    Charge le token d'authentification bcrypt depuis .secrets/qwen-api-user.token.
    
    Returns:
        Token bcrypt ou None en cas d'erreur
    """
    print_section("ÉTAPE 1 : Chargement Token Authentification", level=2)
    
    if not os.path.exists(BCRYPT_TOKEN_FILE):
        print_status("error", f"Fichier token bcrypt non trouvé : {BCRYPT_TOKEN_FILE}")
        return None
    
    try:
        with open(BCRYPT_TOKEN_FILE, 'r') as f:
            token = f.read().strip()
            if token.startswith("$2b$"):
                print_status("success", f"Token bcrypt chargé : {token[:20]}...")
                return token
            else:
                print_status("error", "Format token invalide (doit commencer par $2b$)")
                return None
        
    except Exception as e:
        print_status("error", f"Erreur lecture token bcrypt : {e}")
        return None


def verify_fp8_models() -> bool:
    """
    Vérifie la présence des 3 modèles FP8 officiels dans le container.
    
    Returns:
        True si tous les modèles sont présents, False sinon
    """
    print_section("ÉTAPE 2 : Vérification Modèles FP8 Officiels", level=2)
    
    models_to_check = {
        "Diffusion Model": "/workspace/ComfyUI/models/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "Text Encoder": "/workspace/ComfyUI/models/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "VAE": "/workspace/ComfyUI/models/vae/qwen_image_vae.safetensors"
    }
    
    all_present = True
    
    for model_type, model_path in models_to_check.items():
        print(f"\nVérification {model_type}...")
        output = run_docker_command(f"ls -lh {model_path}")
        
        if output and ".safetensors" in output:
            # Extraire taille du fichier
            parts = output.split()
            size = parts[4] if len(parts) > 4 else "Unknown"
            print_status("success", f"{model_type} présent ({size})")
            print(f"  Chemin : {model_path}")
        else:
            print_status("error", f"{model_type} MANQUANT : {model_path}")
            all_present = False
    
    if all_present:
        print_status("success", "Tous les modèles FP8 officiels sont présents")
    else:
        print_status("error", "Un ou plusieurs modèles manquants. Exécuter rapport 30 d'abord.")
    
    return all_present


def verify_container_running() -> bool:
    """
    Vérifie que le container ComfyUI est actif.
    
    Returns:
        True si actif, False sinon
    """
    print_section("ÉTAPE 0 : Vérification Container Docker", level=2)
    
    try:
        result = subprocess.run(
            ["pwsh", "-c", f"docker ps --filter name={CONTAINER_NAME} --format '{{{{.Names}}}}'"],
            capture_output=True,
            text=True,
            check=True
        )
        
        if CONTAINER_NAME in result.stdout:
            print_status("success", f"Container {CONTAINER_NAME} actif")
            return True
        else:
            print_status("error", f"Container {CONTAINER_NAME} non actif")
            print("Démarrer avec : cd docker-configurations/comfyui-qwen && docker-compose up -d")
            return False
            
    except subprocess.CalledProcessError as e:
        print_status("error", f"Erreur vérification Docker : {e.stderr}")
        return False


def submit_workflow(workflow: Dict, token: str) -> Optional[str]:
    """
    Soumet le workflow à l'API ComfyUI.
    
    Args:
        workflow: Workflow JSON adapté
        token: Token d'authentification bcrypt
        
    Returns:
        Prompt ID ou None en cas d'erreur
    """
    print_section("ÉTAPE 3 : Soumission Workflow à ComfyUI", level=2)
    
    headers = {
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json"
    }
    
    payload = {
        "prompt": workflow
    }
    
    try:
        print(f"URL : {COMFYUI_API_BASE}/prompt")
        print(f"Headers : Authorization: Bearer {token[:20]}...")
        print(f"Workflow : {len(json.dumps(workflow))} caractères")
        
        response = requests.post(
            f"{COMFYUI_API_BASE}/prompt",
            headers=headers,
            json=payload,
            timeout=30
        )
        
        print(f"Status Code : {response.status_code}")
        
        if response.status_code == 200:
            data = response.json()
            prompt_id = data.get("prompt_id")
            print_status("success", f"Workflow soumis avec succès. Prompt ID : {prompt_id}")
            return prompt_id
        else:
            print_status("error", f"Erreur API : {response.status_code}")
            print(f"Réponse : {response.text}")
            return None
            
    except Exception as e:
        print_status("error", f"Erreur soumission workflow : {e}")
        return None


def poll_execution_status(prompt_id: str, token: str) -> bool:
    """
    Polling du statut d'exécution du workflow.
    
    Args:
        prompt_id: ID du prompt soumis
        token: Token d'authentification bcrypt
        
    Returns:
        True si succès, False sinon
    """
    print_section("ÉTAPE 4 : Polling Statut Exécution", level=2)
    
    headers = {
        "Authorization": f"Bearer {token}"
    }
    
    start_time = time.time()
    iteration = 0
    
    while time.time() - start_time < TIMEOUT_SECONDS:
        iteration += 1
        elapsed = int(time.time() - start_time)
        
        print(f"\n[{iteration}] Vérification statut (temps écoulé : {elapsed}s / {TIMEOUT_SECONDS}s)...")
        
        try:
            response = requests.get(
                f"{COMFYUI_API_BASE}/history/{prompt_id}",
                headers=headers,
                timeout=10
            )
            
            if response.status_code == 200:
                data = response.json()
                
                if prompt_id in data:
                    history_item = data[prompt_id]
                    status = history_item.get("status", {})
                    
                    # Vérifier si terminé
                    if status.get("completed", False):
                        print_status("success", f"Génération terminée en {elapsed}s")
                        return True
                    
                    # Vérifier erreurs
                    if "error" in history_item or status.get("status_str") == "error":
                        error_msg = history_item.get("error", status.get("error", "Erreur inconnue"))
                        print_status("error", f"Erreur génération : {error_msg}")
                        return False
                    
                    # Afficher progression
                    if "status_str" in status:
                        print(f"  Statut : {status['status_str']}")
                
            else:
                print(f"  Status Code : {response.status_code}")
            
        except Exception as e:
            print(f"  Erreur polling : {e}")
        
        time.sleep(POLL_INTERVAL_SECONDS)
    
    print_status("error", f"Timeout après {TIMEOUT_SECONDS}s")
    return False


def verify_and_copy_output() -> Optional[str]:
    """
    Vérifie la génération d'image et copie vers outputs/.
    
    Returns:
        Chemin de l'image copiée ou None en cas d'erreur
    """
    print_section("ÉTAPE 5 : Vérification et Copie Output", level=2)
    
    # Créer répertoire outputs si nécessaire
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    
    # Lister fichiers générés
    print("Recherche images générées...")
    output = run_docker_command("bash -c 'ls -lt /workspace/ComfyUI/output/ | head -20'")
    
    if not output:
        print_status("error", "Impossible de lister le répertoire output")
        return None
    
    print("Fichiers récents dans /workspace/ComfyUI/output/ :")
    print(output)
    
    # Trouver dernière image qwen_fp8_validation
    latest_image = None
    for line in output.split("\n"):
        if f"qwen_fp8_validation_{TIMESTAMP}" in line and (".png" in line or ".jpg" in line):
            latest_image = line.split()[-1]
            break
    
    if not latest_image:
        print_status("error", f"Aucune image générée trouvée avec préfixe 'qwen_fp8_validation_{TIMESTAMP}'")
        return None
    
    print(f"\nImage trouvée : {latest_image}")
    
    # Copier vers Windows via Docker API
    container_path = f"{CONTAINER_NAME}:/workspace/ComfyUI/output/{latest_image}"
    windows_dest_path = os.path.join(OUTPUT_DIR, latest_image)
    
    print(f"\nCopie vers Windows...")
    print(f"  Source Container : {container_path}")
    print(f"  Destination : {windows_dest_path}")
    
    try:
        # Utiliser docker cp pour copier depuis le container
        copy_command = f'docker cp {container_path} "{windows_dest_path}"'
        result = subprocess.run(
            ["pwsh", "-c", copy_command],
            capture_output=True,
            text=True,
            check=True
        )
        
        # Vérifier existence
        if os.path.exists(windows_dest_path):
            file_size = os.path.getsize(windows_dest_path)
            print_status("success", f"Image copiée avec succès ({file_size} bytes)")
            print(f"Emplacement : {windows_dest_path}")
            return windows_dest_path
        else:
            print_status("error", "Fichier destination non trouvé après copie")
            return None
            
    except subprocess.CalledProcessError as e:
        print_status("error", f"Erreur copie : {e.stderr}")
        return None


# ============================================================================
# FONCTION PRINCIPALE
# ============================================================================

def main() -> int:
    """
    Fonction principale du script de test.
    
    Returns:
        0 si succès, 1 sinon
    """
    print_section("TEST GÉNÉRATION IMAGE COMFYUI QWEN - MODÈLES FP8 OFFICIELS")
    print(f"Timestamp : {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Container Docker : {CONTAINER_NAME}")
    print(f"API ComfyUI : {COMFYUI_API_BASE}")
    print(f"Timeout : {TIMEOUT_SECONDS}s")
    print(f"Output : {OUTPUT_DIR}")
    
    # Étape 0 : Vérification container
    if not verify_container_running():
        print_status("error", "Container Docker non actif")
        return 1
    
    # Étape 1 : Authentification
    token = load_auth_token()
    if not token:
        print_status("error", "Échec chargement token authentification")
        return 1
    
    # Étape 2 : Vérification modèles FP8
    if not verify_fp8_models():
        print_status("error", "Échec vérification modèles FP8 officiels")
        return 1
    
    # Étape 3 : Soumission workflow
    prompt_id = submit_workflow(WORKFLOW_TEMPLATE, token)
    if not prompt_id:
        print_status("error", "Échec soumission workflow")
        return 1
    
    # Étape 4 : Polling statut
    if not poll_execution_status(prompt_id, token):
        print_status("error", "Échec génération image")
        return 1
    
    # Étape 5 : Vérification et copie output
    output_path = verify_and_copy_output()
    if not output_path:
        print_status("error", "Échec vérification/copie output")
        return 1
    
    # Succès
    print_section("RÉSULTAT FINAL : SUCCÈS ✅", level=1)
    print_status("success", "Test de génération image réussi avec modèles FP8 officiels")
    print_status("success", f"Image disponible : {output_path}")
    print("\nModèles utilisés :")
    print("  - Diffusion : qwen_image_edit_2509_fp8_e4m3fn.safetensors (20GB)")
    print("  - Text Encoder : qwen_2.5_vl_7b_fp8_scaled.safetensors (8.8GB)")
    print("  - VAE : qwen_image_vae.safetensors (243MB)")
    print("\nWorkflow : 100% nodes natifs ComfyUI (UNETLoader, CLIPLoader, VAELoader)")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())