#!/usr/bin/env python3
"""
Test Génération Image Qwen - Phase 29
=====================================
Date: 2025-11-02 09:38:00 UTC+1
Objectif: Générer UNE image pour valider installation end-to-end

Workflow Source: CORRIGÉ après diagnostic nodes disponibles
Document: docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/diagnostic-nodes-qwen-20251102-095800.json

CORRECTION MAJEURE:
- QwenVLCLIPLoader ne produit QU'UNE sortie (index 0: clip)
- Utilisation de QwenModelManagerWrapper qui produit 4 sorties:
  [0] dit: MODEL
  [1] text_encoder: QWEN_TEXT_ENCODER
  [2] vae: VAE
  [3] processor: QWEN_PROCESSOR
"""

import requests
import json
import time
import sys
from pathlib import Path
from datetime import datetime

# ============================================================================
# CONFIGURATION
# ============================================================================

COMFYUI_URL = "http://localhost:8188"
HASH_FILE = Path(".secrets/qwen-api-user.token")
TIMEOUT = 300  # 5 minutes max pour génération

# ============================================================================
# WORKFLOW JSON CORRIGÉ (QwenModelManagerWrapper)
# ============================================================================

WORKFLOW_TEXT_TO_IMAGE = {
    "1": {
        "class_type": "QwenModelManagerWrapper",
        "inputs": {"model_path": "Qwen-Image-Edit-2509-FP8"}
    },
    "2": {
        "class_type": "TextEncodeQwenImageEdit",
        "inputs": {
            "text": "A beautiful mountain landscape at sunset, highly detailed, 8k",
            "clip": ["1", 1]  # text_encoder est à l'index 1
        }
    },
    "3": {
        "class_type": "TextEncodeQwenImageEdit",
        "inputs": {
            "text": "blurry, low quality, watermark",
            "clip": ["1", 1]  # text_encoder est à l'index 1
        }
    },
    "4": {
        "class_type": "QwenVLEmptyLatent",
        "inputs": {"width": 512, "height": 512, "batch_size": 1}
    },
    "5": {
        "class_type": "QwenImageSamplerNode",
        "inputs": {
            "seed": 42,
            "steps": 20,
            "cfg": 7.0,
            "sampler_name": "euler_ancestral",
            "scheduler": "normal",
            "transformer": ["1", 0],  # dit (MODEL) est à l'index 0
            "positive": ["2", 0],
            "negative": ["3", 0],
            "latent_image": ["4", 0]
        }
    },
    "6": {
        "class_type": "VAEDecode",
        "inputs": {
            "samples": ["5", 0],
            "vae": ["1", 2]  # vae est à l'index 2
        }
    },
    "7": {
        "class_type": "SaveImage",
        "inputs": {
            "filename_prefix": "Qwen_Phase29_Test",
            "images": ["6", 0]
        }
    }
}

# ============================================================================
# FONCTIONS UTILITAIRES
# ============================================================================

def print_section(title: str):
    """Affiche section formatée"""
    print(f"\n{'=' * 60}")
    print(f"  {title}")
    print(f"{'=' * 60}\n")

def load_token() -> str:
    """Charge token depuis fichier .secrets"""
    if not HASH_FILE.exists():
        raise FileNotFoundError(
            f"❌ Token non trouvé: {HASH_FILE}\n"
            "   Exécutez d'abord: python scripts/genai-auth/resync-credentials-complete.py"
        )
    
    token = HASH_FILE.read_text().strip()
    if not token:
        raise ValueError("❌ Token vide dans le fichier")
    
    return token

def submit_workflow(workflow: dict, token: str) -> str:
    """
    Soumet workflow à ComfyUI et retourne prompt_id
    
    Args:
        workflow: Workflow JSON au format ComfyUI
        token: Token d'authentification
        
    Returns:
        str: prompt_id de la tâche
        
    Raises:
        RuntimeError: Si soumission échoue
    """
    print("📤 Soumission du workflow...")
    print(f"   Nodes: {len(workflow)} nodes")
    print(f"   Architecture: QwenModelManagerWrapper → TextEncode → QwenImageSamplerNode → VAEDecode → SaveImage")
    
    headers = {
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/json"
    }
    
    payload = {"prompt": workflow}
    
    try:
        response = requests.post(
            f"{COMFYUI_URL}/prompt",
            json=payload,
            headers=headers,
            timeout=30
        )
        
        if response.status_code == 200:
            result = response.json()
            prompt_id = result.get('prompt_id')
            
            if not prompt_id:
                raise RuntimeError("❌ Réponse sans prompt_id")
            
            print(f"✅ Workflow soumis avec succès!")
            print(f"   Prompt ID: {prompt_id}")
            return prompt_id
        else:
            error_detail = response.text
            print(f"❌ Échec soumission (HTTP {response.status_code})")
            print(f"   Erreur: {error_detail}")
            
            # Parser erreur si JSON
            try:
                error_json = response.json()
                if 'error' in error_json:
                    print(f"\n📋 Détails de l'erreur:")
                    print(json.dumps(error_json['error'], indent=2))
            except:
                pass
            
            raise RuntimeError(f"Échec soumission: HTTP {response.status_code}")
            
    except requests.exceptions.RequestException as e:
        raise RuntimeError(f"❌ Erreur connexion API: {e}")

def wait_for_completion(prompt_id: str, token: str, timeout: int = 300) -> dict:
    """
    Attend fin génération via polling /history
    
    Args:
        prompt_id: ID du prompt soumis
        token: Token d'authentification
        timeout: Timeout max en secondes
        
    Returns:
        dict: Historique complet du job
        
    Raises:
        TimeoutError: Si timeout dépassé
        RuntimeError: Si génération échoue
    """
    print(f"\n⏳ Attente génération (max {timeout}s)...")
    
    headers = {"Authorization": f"Bearer {token}"}
    start_time = time.time()
    last_progress = None
    
    while time.time() - start_time < timeout:
        try:
            response = requests.get(
                f"{COMFYUI_URL}/history/{prompt_id}",
                headers=headers,
                timeout=10
            )
            
            if response.status_code == 200:
                history = response.json()
                
                if prompt_id in history:
                    job = history[prompt_id]
                    status = job.get('status', {})
                    
                    # Afficher progression
                    if 'status_str' in status:
                        current_progress = status['status_str']
                        if current_progress != last_progress:
                            print(f"   Status: {current_progress}")
                            last_progress = current_progress
                    
                    # Vérifier complétion
                    if status.get('completed', False):
                        elapsed = time.time() - start_time
                        print(f"\n✅ Génération terminée! (durée: {elapsed:.1f}s)")
                        return job
                    
                    # Vérifier erreur
                    if 'error' in status:
                        error_msg = status['error']
                        print(f"\n❌ Génération échouée: {error_msg}")
                        raise RuntimeError(f"Génération échouée: {error_msg}")
            
            # Polling interval
            time.sleep(2)
            
        except requests.exceptions.RequestException as e:
            print(f"⚠️ Erreur polling: {e}")
            time.sleep(2)
            continue
    
    # Timeout
    raise TimeoutError(f"❌ Génération timeout après {timeout}s")

def extract_image_info(job_result: dict) -> dict:
    """
    Extrait informations image depuis résultat job
    
    Args:
        job_result: Résultat complet du job
        
    Returns:
        dict: Informations image (filename, path, metadata)
    """
    outputs = job_result.get('outputs', {})
    
    if not outputs:
        raise ValueError("❌ Aucun output trouvé dans résultat")
    
    # Chercher node SaveImage (node 7)
    save_node = outputs.get('7')
    
    if not save_node:
        raise ValueError("❌ Node SaveImage (7) non trouvé dans outputs")
    
    images = save_node.get('images', [])
    
    if not images:
        raise ValueError("❌ Aucune image dans SaveImage node")
    
    # Première image
    image_info = images[0]
    
    return {
        'filename': image_info.get('filename'),
        'subfolder': image_info.get('subfolder', ''),
        'type': image_info.get('type', 'output'),
        'format': image_info.get('format', 'png')
    }

# ============================================================================
# FONCTION PRINCIPALE
# ============================================================================

def main():
    """Fonction principale de test"""
    
    print_section("Test Génération Image Qwen - Phase 29")
    
    start_time = datetime.now()
    print(f"🕒 Démarrage: {start_time.strftime('%Y-%m-%d %H:%M:%S')}")
    
    try:
        # ÉTAPE 1: Chargement token
        print_section("1️⃣ Chargement Token Authentification")
        token = load_token()
        print(f"✅ Token chargé depuis {HASH_FILE}")
        print(f"   Longueur: {len(token)} caractères")
        
        # ÉTAPE 2: Soumission workflow
        print_section("2️⃣ Soumission Workflow Text-to-Image")
        prompt_id = submit_workflow(WORKFLOW_TEXT_TO_IMAGE, token)
        
        # ÉTAPE 3: Attente génération
        print_section("3️⃣ Attente Génération Image")
        job_result = wait_for_completion(prompt_id, token, TIMEOUT)
        
        # ÉTAPE 4: Extraction informations image
        print_section("4️⃣ Extraction Informations Image")
        image_info = extract_image_info(job_result)
        
        print("📸 Image générée:")
        print(f"   Filename: {image_info['filename']}")
        print(f"   Subfolder: {image_info['subfolder']}")
        print(f"   Type: {image_info['type']}")
        print(f"   Format: {image_info['format']}")
        
        # ÉTAPE 5: Résumé final
        print_section("✅ TEST GÉNÉRATION IMAGE RÉUSSI!")
        
        end_time = datetime.now()
        duration = (end_time - start_time).total_seconds()
        
        print(f"🕒 Fin: {end_time.strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"⏱️ Durée totale: {duration:.1f}s")
        print(f"\n📁 Localisation image:")
        print(f"   Container: /workspace/ComfyUI/output/{image_info['filename']}")
        print(f"   WSL: /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/output/{image_info['filename']}")
        print(f"\n🎉 Phase 29 - VALIDATION END-TO-END COMPLÈTE!")
        
        return 0
        
    except FileNotFoundError as e:
        print(f"\n❌ ERREUR FICHIER: {e}")
        return 1
        
    except RuntimeError as e:
        print(f"\n❌ ERREUR EXÉCUTION: {e}")
        return 1
        
    except TimeoutError as e:
        print(f"\n❌ ERREUR TIMEOUT: {e}")
        return 1
        
    except Exception as e:
        print(f"\n❌ ERREUR INATTENDUE: {type(e).__name__}: {e}")
        import traceback
        traceback.print_exc()
        return 1

# ============================================================================
# POINT D'ENTRÉE
# ============================================================================

if __name__ == '__main__':
    sys.exit(main())