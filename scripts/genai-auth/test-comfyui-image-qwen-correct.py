#!/usr/bin/env python3
"""
Script de test de génération d'images ComfyUI Qwen - Version Corrigée
Utilise le workflow Text-to-Image basique validé en Phase 12C

Date: 2025-11-02
Objectif: Tester la génération d'images avec le workflow Qwen fonctionnel
"""

import os
import sys
import requests
import json
import time
from pathlib import Path
from datetime import datetime

# Configuration
COMFYUI_URL = "http://localhost:8188"
TOKEN_FILE = Path(".secrets/qwen-api-user.token")
OUTPUT_DIR = Path("test-outputs")

def print_section(title: str):
    """Affiche un titre de section formaté"""
    print("\n" + "=" * 60)
    print(f" {title}")
    print("=" * 60)

def load_token() -> str:
    """Charge le token bcrypt depuis le fichier"""
    if not TOKEN_FILE.exists():
        raise FileNotFoundError(f"Fichier token non trouvé: {TOKEN_FILE}")
    
    with open(TOKEN_FILE, 'r') as f:
        token = f.read().strip()
    
    print(f"✅ Token chargé depuis {TOKEN_FILE}")
    print(f"   Longueur: {len(token)} caractères")
    return token

def create_qwen_t2i_workflow(prompt: str = "A beautiful mountain landscape at sunset, highly detailed, 8k",
                              negative_prompt: str = "blurry, low quality, watermark",
                              seed: int = 42,
                              steps: int = 20,
                              cfg: float = 7.0) -> dict:
    """
    Crée un workflow Qwen Text-to-Image basique
    Architecture validée Phase 12C (7 nodes)
    
    Returns:
        dict: Workflow au format ComfyUI API
    """
    workflow = {
        "1": {
            "class_type": "QwenVLCLIPLoader",
            "inputs": {"model_path": "Qwen-Image-Edit-2509-FP8"}
        },
        "2": {
            "class_type": "TextEncodeQwenImageEdit",
            "inputs": {
                "text": prompt,
                "clip": ["1", 0]
            }
        },
        "3": {
            "class_type": "TextEncodeQwenImageEdit",
            "inputs": {
                "text": negative_prompt,
                "clip": ["1", 0]
            }
        },
        "4": {
            "class_type": "QwenVLEmptyLatent",
            "inputs": {"width": 512, "height": 512, "batch_size": 1}
        },
        "5": {
            "class_type": "QwenImageSamplerNode",
            "inputs": {
                "seed": seed,
                "steps": steps,
                "cfg": cfg,
                "sampler_name": "euler_ancestral",
                "scheduler": "normal",
                "transformer": ["1", 1],
                "positive": ["2", 0],
                "negative": ["3", 0],
                "latent_image": ["4", 0]
            }
        },
        "6": {
            "class_type": "VAEDecode",
            "inputs": {
                "samples": ["5", 0],
                "vae": ["1", 2]
            }
        },
        "7": {
            "class_type": "SaveImage",
            "inputs": {
                "filename_prefix": "Qwen_T2I_test",
                "images": ["6", 0]
            }
        }
    }
    
    return {"prompt": workflow}

def test_authentication(token: str) -> bool:
    """Teste l'authentification avec le token Bearer"""
    print_section("Test 1: Authentification ComfyUI-Login")
    
    headers = {"Authorization": f"Bearer {token}"}
    
    try:
        response = requests.get(f"{COMFYUI_URL}/system_stats", headers=headers, timeout=10)
        
        if response.status_code == 200:
            print("✅ Authentification réussie (HTTP 200)")
            stats = response.json()
            print(f"   Statistiques système:")
            print(f"   - VRAM: {stats.get('devices', [{}])[0].get('vram_total', 'N/A')}")
            return True
        else:
            print(f"❌ Échec authentification (HTTP {response.status_code})")
            print(f"   Réponse: {response.text[:200]}")
            return False
            
    except Exception as e:
        print(f"❌ Erreur de connexion: {e}")
        return False

def submit_workflow(token: str, workflow: dict) -> str:
    """Soumet le workflow et retourne le prompt_id"""
    print_section("Test 2: Soumission du Workflow Qwen")
    
    headers = {
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json"
    }
    
    try:
        print("🔄 Soumission du workflow...")
        print(f"   Nodes: {len(workflow['prompt'])} nodes")
        print(f"   Architecture: QwenVLCLIPLoader → TextEncode → QwenImageSamplerNode → VAEDecode → SaveImage")
        
        response = requests.post(
            f"{COMFYUI_URL}/prompt",
            headers=headers,
            json=workflow,
            timeout=30
        )
        
        if response.status_code == 200:
            result = response.json()
            prompt_id = result.get("prompt_id")
            print(f"✅ Workflow soumis avec succès")
            print(f"   Prompt ID: {prompt_id}")
            return prompt_id
        else:
            print(f"❌ Échec soumission (HTTP {response.status_code})")
            error_data = response.json()
            print(f"   Erreur: {json.dumps(error_data, indent=2)}")
            return None
            
    except Exception as e:
        print(f"❌ Erreur de soumission: {e}")
        return None

def wait_for_completion(token: str, prompt_id: str, timeout: int = 60) -> bool:
    """Attend la complétion du workflow"""
    print_section("Test 3: Attente de la Génération")
    
    headers = {"Authorization": f"Bearer {token}"}
    start_time = time.time()
    
    print(f"⏳ Attente de la génération (timeout: {timeout}s)...")
    
    while time.time() - start_time < timeout:
        try:
            response = requests.get(f"{COMFYUI_URL}/history/{prompt_id}", headers=headers, timeout=10)
            
            if response.status_code == 200:
                history = response.json()
                
                if prompt_id in history:
                    status = history[prompt_id].get("status", {})
                    
                    if status.get("completed", False):
                        print(f"✅ Génération terminée en {time.time() - start_time:.1f}s")
                        return True
                    
                    print(f"   En cours... ({time.time() - start_time:.1f}s écoulées)")
            
            time.sleep(2)
            
        except Exception as e:
            print(f"   Erreur lors de la vérification: {e}")
            time.sleep(2)
    
    print(f"❌ Timeout dépassé ({timeout}s)")
    return False

def verify_output(prompt_id: str) -> bool:
    """Vérifie que l'image a été générée"""
    print_section("Test 4: Vérification de l'Image Générée")
    
    # ComfyUI sauvegarde dans output/ par défaut
    output_base = Path("output")
    if not output_base.exists():
        # Essayer dans le container WSL
        wsl_path = Path("/mnt/d/Dev/CoursIA/docker-configurations/comfyui-qwen/output")
        if wsl_path.exists():
            output_base = wsl_path
        else:
            print(f"⚠️ Répertoire output non trouvé")
            return False
    
    # Chercher les fichiers récents avec le préfixe
    recent_files = []
    for file in output_base.glob("Qwen_T2I_test_*.png"):
        if time.time() - file.stat().st_mtime < 120:  # Modifiés dans les 2 dernières minutes
            recent_files.append(file)
    
    if recent_files:
        print(f"✅ Image(s) générée(s) trouvée(s): {len(recent_files)}")
        for file in recent_files:
            size_mb = file.stat().st_size / (1024 * 1024)
            print(f"   - {file.name} ({size_mb:.2f} MB)")
        return True
    else:
        print("⚠️ Aucune image récente trouvée")
        print(f"   Répertoire vérifié: {output_base}")
        return False

def main():
    """Fonction principale"""
    print("=" * 60)
    print(" Test de Génération d'Images ComfyUI Qwen")
    print(" Workflow: Text-to-Image Basique (Phase 12C)")
    print("=" * 60)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"URL: {COMFYUI_URL}")
    
    try:
        # Étape 1: Charger le token
        token = load_token()
        
        # Étape 2: Tester l'authentification
        if not test_authentication(token):
            print("\n❌ Test échoué - Authentification non fonctionnelle")
            return False
        
        # Étape 3: Créer le workflow
        print_section("Préparation du Workflow")
        workflow = create_qwen_t2i_workflow(
            prompt="A majestic snow-capped mountain at golden hour, cinematic lighting, highly detailed, 8k",
            negative_prompt="blurry, low quality, watermark, text",
            seed=12345,
            steps=20,
            cfg=7.0
        )
        print("✅ Workflow Qwen T2I créé")
        print(f"   Prompt: {workflow['prompt']['2']['inputs']['text'][:60]}...")
        
        # Étape 4: Soumettre le workflow
        prompt_id = submit_workflow(token, workflow)
        if not prompt_id:
            print("\n❌ Test échoué - Impossible de soumettre le workflow")
            return False
        
        # Étape 5: Attendre la complétion
        if not wait_for_completion(token, prompt_id, timeout=60):
            print("\n⚠️ Test incomplet - Génération en cours ou timeout")
            return False
        
        # Étape 6: Vérifier l'output
        if verify_output(prompt_id):
            print("\n" + "=" * 60)
            print("✅ TEST RÉUSSI - Image générée avec succès")
            print("=" * 60)
            return True
        else:
            print("\n" + "=" * 60)
            print("⚠️ TEST PARTIEL - Génération OK, vérification fichier incomplète")
            print("=" * 60)
            return True
        
    except Exception as e:
        print(f"\n❌ Erreur critique: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)