#!/usr/bin/env python3
"""
Script de Test : Génération Image ComfyUI Qwen avec Workflow Officiel
======================================================================

Phase 29 - ÉTAPE 24A
Création : 2025-11-02 10:50:27 UTC+1

Objectif :
    Tester la génération d'image avec le workflow JSON natif officiel ComfyUI
    extrait de la documentation comfyanonymous.github.io

Architecture :
    - Workflow JSON source : Rapport 26 (ligne 487)
    - Authentification : Hash bcrypt validé (Rapport 18)
    - Container Docker : comfyui-qwen (Windows CLI)
    - API ComfyUI : http://localhost:8188

Contraintes ABSOLUES :
    ✅ Utiliser workflow officiel EXACT (pas de custom nodes)
    ✅ Vérifier modèles disponibles AVANT adaptation
    ✅ Logger CHAQUE étape avec statut clair
    ✅ Copier image générée vers rapports/

Références :
    - Rapport 26 : docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/26-extraction-documentation-officielle-qwen-20251102-101620.md
    - Rapport 28 : docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/28-reconciliation-decision-architecture-20251102-102551.md
    - Rapport 18 : docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/18-resolution-finale-authentification-comfyui-login-20251101-232000.md
"""

import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional

import requests

# ============================================================================
# CONFIGURATION GLOBALE
# ============================================================================

COMFYUI_API_BASE = "http://localhost:8188"
CONTAINER_NAME = "comfyui-qwen"
SECRETS_FILE = ".secrets/.env.generated"
OUTPUT_DIR = "docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports"
TIMEOUT_SECONDS = 300  # 5 minutes
POLL_INTERVAL_SECONDS = 5

# ============================================================================
# WORKFLOW JSON OFFICIEL (Source : Rapport 26, ligne 487)
# ============================================================================

WORKFLOW_TEMPLATE = {
    "3": {
        "inputs": {
            "ckpt_name": "PLACEHOLDER_DIFFUSION_MODEL"
        },
        "class_type": "DiffusionModelLoader",
        "_meta": {"title": "Diffusion Model Loader"}
    },
    "9": {
        "inputs": {
            "clip_name": "PLACEHOLDER_CLIP_MODEL"
        },
        "class_type": "CLIPLoader",
        "_meta": {"title": "CLIP Loader"}
    },
    "11": {
        "inputs": {
            "vae_name": "PLACEHOLDER_VAE_MODEL"
        },
        "class_type": "VAELoader",
        "_meta": {"title": "VAE Loader"}
    },
    "5": {
        "inputs": {
            "width": 1024,
            "height": 1024,
            "batch_size": 1
        },
        "class_type": "EmptyLatentImage",
        "_meta": {"title": "Empty Latent Image"}
    },
    "6": {
        "inputs": {
            "text": "A beautiful landscape with mountains and a lake at sunset",
            "clip": ["9", 0]
        },
        "class_type": "CLIPTextEncode",
        "_meta": {"title": "CLIP Text Encode (Positive)"}
    },
    "7": {
        "inputs": {
            "text": "ugly, blurry, low quality, distorted",
            "clip": ["9", 0]
        },
        "class_type": "CLIPTextEncode",
        "_meta": {"title": "CLIP Text Encode (Negative)"}
    },
    "10": {
        "inputs": {
            "seed": 42,
            "steps": 20,
            "cfg": 7.0,
            "sampler_name": "euler",
            "scheduler": "normal",
            "denoise": 1.0,
            "model": ["3", 0],
            "positive": ["6", 0],
            "negative": ["7", 0],
            "latent_image": ["5", 0]
        },
        "class_type": "KSampler",
        "_meta": {"title": "KSampler"}
    },
    "8": {
        "inputs": {
            "samples": ["10", 0],
            "vae": ["11", 0]
        },
        "class_type": "VAEDecode",
        "_meta": {"title": "VAE Decode"}
    },
    "12": {
        "inputs": {
            "filename_prefix": "qwen_test_workflow_officiel",
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
    Charge le token d'authentification bcrypt depuis .secrets/.env.generated.
    
    Returns:
        Token bcrypt ou None en cas d'erreur
    """
    print_section("ÉTAPE 1 : Chargement Token Authentification", level=2)
    
    if not os.path.exists(SECRETS_FILE):
        print_status("error", f"Fichier secrets non trouvé : {SECRETS_FILE}")
        return None
    
    try:
        with open(SECRETS_FILE, 'r') as f:
            for line in f:
                if line.startswith("QWEN_API_USER_TOKEN="):
                    token = line.split("=", 1)[1].strip().strip('"')
                    print_status("success", f"Token chargé : {token[:20]}...")
                    return token
        
        print_status("error", "Variable QWEN_API_USER_TOKEN non trouvée dans .env.generated")
        return None
        
    except Exception as e:
        print_status("error", f"Erreur lecture secrets : {e}")
        return None


def list_available_models() -> Optional[Dict[str, List[str]]]:
    """
    Liste les modèles disponibles dans le container Docker.
    
    Returns:
        Dictionnaire {type_modele: [fichiers]} ou None en cas d'erreur
    """
    print_section("ÉTAPE 2 : Vérification Modèles Disponibles", level=2)
    
    # MODIFICATION ÉTAPE 24D - Phase 29
    # Chemins adaptés pour structure unifiée Qwen-Image-Edit-2509-FP8
    # Diagnostic ÉTAPE 24C : /workspace/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8/
    
    models = {
        "diffusion": [],
        "clip": [],
        "vae": []
    }
    
    # Vérifier modèles de diffusion - Structure unifiée Qwen transformer/
    print("Recherche modèles de diffusion (transformer)...")
    output = run_docker_command("ls -la /workspace/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8/transformer/")
    if output:
        for line in output.split("\n"):
            if ".safetensors" in line:
                filename = line.split()[-1]
                models["diffusion"].append(filename)
                print(f"  - {filename}")
    
    # Vérifier modèles CLIP - Structure unifiée Qwen text_encoder/
    print("\nRecherche modèles CLIP (text_encoder)...")
    output = run_docker_command("ls -la /workspace/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8/text_encoder/")
    if output:
        for line in output.split("\n"):
            if ".safetensors" in line or ".bin" in line:
                filename = line.split()[-1]
                models["clip"].append(filename)
                print(f"  - {filename}")
    
    # Vérifier modèles VAE - Structure unifiée Qwen vae/
    print("\nRecherche modèles VAE...")
    output = run_docker_command("ls -la /workspace/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8/vae/")
    if output:
        for line in output.split("\n"):
            if ".safetensors" in line or ".bin" in line:
                filename = line.split()[-1]
                models["vae"].append(filename)
                print(f"  - {filename}")
    
    # Validation
    if not models["diffusion"]:
        print_status("error", "Aucun modèle de diffusion trouvé !")
        return None
    
    if not models["clip"]:
        print_status("warning", "Aucun modèle CLIP trouvé (optionnel)")
    
    if not models["vae"]:
        print_status("warning", "Aucun modèle VAE trouvé (optionnel)")
    
    print_status("success", f"Modèles trouvés : {len(models['diffusion'])} diffusion, {len(models['clip'])} CLIP, {len(models['vae'])} VAE")
    
    return models


def adapt_workflow(models: Dict[str, List[str]]) -> Dict:
    """
    Adapte le workflow JSON avec les noms de modèles réels.
    
    Args:
        models: Dictionnaire des modèles disponibles
        
    Returns:
        Workflow JSON adapté
    """
    print_section("ÉTAPE 3 : Adaptation Workflow JSON", level=2)
    
    workflow = json.loads(json.dumps(WORKFLOW_TEMPLATE))  # Deep copy
    
    # Remplacer modèle de diffusion
    if models["diffusion"]:
        workflow["3"]["inputs"]["ckpt_name"] = models["diffusion"][0]
        print(f"Diffusion Model : {models['diffusion'][0]}")
    
    # Remplacer modèle CLIP (optionnel)
    if models["clip"]:
        workflow["9"]["inputs"]["clip_name"] = models["clip"][0]
        print(f"CLIP Model : {models['clip'][0]}")
    else:
        # Supprimer node CLIP si pas de modèle
        del workflow["9"]
        workflow["6"]["inputs"]["clip"] = ["3", 1]  # Utiliser CLIP du diffusion model
        workflow["7"]["inputs"]["clip"] = ["3", 1]
        print("CLIP Model : Utilisation CLIP intégré au diffusion model")
    
    # Remplacer modèle VAE (optionnel)
    if models["vae"]:
        workflow["11"]["inputs"]["vae_name"] = models["vae"][0]
        print(f"VAE Model : {models['vae'][0]}")
    else:
        # Supprimer node VAE si pas de modèle
        del workflow["11"]
        workflow["8"]["inputs"]["vae"] = ["3", 2]  # Utiliser VAE du diffusion model
        print("VAE Model : Utilisation VAE intégré au diffusion model")
    
    print_status("success", "Workflow adapté avec succès")
    
    return workflow


def submit_workflow(workflow: Dict, token: str) -> Optional[str]:
    """
    Soumet le workflow à l'API ComfyUI.
    
    Args:
        workflow: Workflow JSON adapté
        token: Token d'authentification bcrypt
        
    Returns:
        Prompt ID ou None en cas d'erreur
    """
    print_section("ÉTAPE 4 : Soumission Workflow à ComfyUI", level=2)
    
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
    print_section("ÉTAPE 5 : Polling Statut Exécution", level=2)
    
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
                    if "error" in status:
                        error_msg = status.get("error", "Erreur inconnue")
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


def verify_and_copy_output() -> bool:
    """
    Vérifie la génération d'image et copie vers rapports/.
    
    Returns:
        True si succès, False sinon
    """
    print_section("ÉTAPE 6 : Vérification et Copie Output", level=2)
    
    # Lister fichiers générés
    print("Recherche images générées...")
    output = run_docker_command("ls -lt /workspace/output/ | head -20")
    
    if not output:
        print_status("error", "Impossible de lister le répertoire output")
        return False
    
    print("Fichiers récents dans /workspace/output/ :")
    print(output)
    
    # Trouver dernière image qwen_test_workflow_officiel
    latest_image = None
    for line in output.split("\n"):
        if "qwen_test_workflow_officiel" in line and (".png" in line or ".jpg" in line):
            latest_image = line.split()[-1]
            break
    
    if not latest_image:
        print_status("error", "Aucune image générée trouvée avec préfixe 'qwen_test_workflow_officiel'")
        return False
    
    print(f"\nImage trouvée : {latest_image}")
    
    # Copier vers Windows
    container_path = f"/workspace/output/{latest_image}"
    host_wsl_path = f"/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/output/{latest_image}"
    windows_dest_path = os.path.join(OUTPUT_DIR, latest_image)
    
    print(f"\nCopie vers Windows...")
    print(f"  Source WSL : {host_wsl_path}")
    print(f"  Destination : {windows_dest_path}")
    
    try:
        # Utiliser wsl cp pour copier depuis WSL vers Windows
        copy_command = f'wsl cp "{host_wsl_path}" "{windows_dest_path}"'
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
            return True
        else:
            print_status("error", "Fichier destination non trouvé après copie")
            return False
            
    except subprocess.CalledProcessError as e:
        print_status("error", f"Erreur copie : {e.stderr}")
        return False


# ============================================================================
# FONCTION PRINCIPALE
# ============================================================================

def main() -> int:
    """
    Fonction principale du script de test.
    
    Returns:
        0 si succès, 1 sinon
    """
    print_section("TEST GÉNÉRATION IMAGE COMFYUI QWEN - WORKFLOW OFFICIEL")
    print(f"Timestamp : {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Container Docker : {CONTAINER_NAME}")
    print(f"API ComfyUI : {COMFYUI_API_BASE}")
    print(f"Timeout : {TIMEOUT_SECONDS}s")
    
    # Étape 1 : Authentification
    token = load_auth_token()
    if not token:
        print_status("error", "Échec chargement token authentification")
        return 1
    
    # Étape 2 : Vérification modèles
    models = list_available_models()
    if not models:
        print_status("error", "Échec vérification modèles disponibles")
        return 1
    
    # Étape 3 : Adaptation workflow
    try:
        workflow = adapt_workflow(models)
    except Exception as e:
        print_status("error", f"Échec adaptation workflow : {e}")
        return 1
    
    # Étape 4 : Soumission workflow
    prompt_id = submit_workflow(workflow, token)
    if not prompt_id:
        print_status("error", "Échec soumission workflow")
        return 1
    
    # Étape 5 : Polling statut
    if not poll_execution_status(prompt_id, token):
        print_status("error", "Échec génération image")
        return 1
    
    # Étape 6 : Vérification et copie output
    if not verify_and_copy_output():
        print_status("error", "Échec vérification/copie output")
        return 1
    
    # Succès
    print_section("RÉSULTAT FINAL : SUCCÈS", level=1)
    print_status("success", "Test de génération image réussi avec workflow officiel ComfyUI")
    print_status("success", "Image disponible dans docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())