#!/usr/bin/env python3
"""
Script de test isolé pour valider le workflow ComfyUI Qwen WanBridge.
Adapté pour utiliser la nouvelle API ComfyUIClientHelper et les modèles officiels Qwen.

Mission: Correction Workflow ComfyUI Qwen - Restauration Méthode WanBridge
Date: 2025-11-30
"""

import sys
import json
import time
import os
import random
from pathlib import Path

# Ajouter le répertoire parent au PYTHONPATH pour import comfyui_client
sys.path.insert(0, str(Path(__file__).parent / ".." / "utils"))

from comfyui_client_helper import ComfyUIClient, ComfyUIConfig
from token_manager import token_manager

def test_qwen_workflow():
    """
    Test de validation du workflow WanBridge avec la nouvelle API.
    """
    print("=" * 80)
    print("TEST WORKFLOW COMFYUI QWEN WANBRIDGE (NOUVELLE API)")
    print("=" * 80)
    
    # Récupération du token via TokenManager
    try:
        # Essai avec le token brut d'abord (souvent requis pour l'API)
        try:
            raw_token = token_manager.get_raw_token()
            print("🔑 Token brut récupéré via TokenManager")
            
            # Construction de l'authentification Bearer avec le hash bcrypt
            # ComfyUI-Login attend le hash bcrypt complet comme token Bearer
            # Voir password.py: if auth_type == 'Bearer' and token_from_header == TOKEN:
            # où TOKEN est lu depuis le fichier PASSWORD (qui contient le hash)
            
            # On récupère le hash bcrypt (qui est le contenu du fichier token)
            bcrypt_hash = token_manager.get_bcrypt_hash()
            
            # On utilise ce hash comme token Bearer
            api_key = bcrypt_hash
            print(f"🔑 Authentification Bearer configurée avec le hash bcrypt")
            
        except Exception as e:
            print(f"⚠️ Erreur lors de la configuration de l'auth: {e}")
            api_key = None
            
    except Exception as e:
        print(f"⚠️ Impossible de récupérer le token via TokenManager: {e}")
        api_key = None

    # Configuration
    config = ComfyUIConfig(
        host="localhost",
        port=8188,
        api_key=api_key
    )
    
    print(f"\n📡 Configuration:")
    print(f"   - URL: {config.protocol}://{config.host}:{config.port}")
    print(f"   - Token: {config.api_key[:20]}...")
    
    try:
        # Créer client ComfyUI
        client = ComfyUIClient(config)
        
        # Pas de login explicite nécessaire si on utilise le bon token Bearer
        # Le middleware check_login_status vérifie le header Authorization

        # Test de connectivité
        if not client.test_connectivity():
            print("❌ Impossible de se connecter au serveur ComfyUI")
            return False
            
        print("✅ Connectivité OK")
        
        # Définition du workflow Qwen (Format API)
        # Utilisation des loaders séparés pour l'architecture Qwen officielle
        
        workflow_api = {
            "3": {
                "class_type": "KSampler",
                "inputs": {
                    "cfg": 8,
                    "denoise": 1,
                    "latent_image": [
                        "5",
                        0
                    ],
                    "model": [
                        "4",
                        0
                    ],
                    "negative": [
                        "7",
                        0
                    ],
                    "positive": [
                        "6",
                        0
                    ],
                    "sampler_name": "euler",
                    "scheduler": "normal",
                    "seed": random.randint(1, 1000000000),
                    "steps": 20
                }
            },
            "4": {
                "class_type": "UNETLoader",
                "inputs": {
                    "unet_name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
                    "weight_dtype": "fp8_e4m3fn"
                }
            },
            "5": {
                "class_type": "EmptyLatentImage",
                "inputs": {
                    "batch_size": 1,
                    "height": 512,
                    "width": 512
                }
            },
            "6": {
                "class_type": "CLIPTextEncode",
                "inputs": {
                    "clip": [
                        "10",
                        0
                    ],
                    "text": "beautiful scenery nature glass bottle landscape, , purple galaxy bottle,"
                }
            },
            "7": {
                "class_type": "CLIPTextEncode",
                "inputs": {
                    "clip": [
                        "10",
                        0
                    ],
                    "text": "text, watermark"
                }
            },
            "8": {
                "class_type": "VAEDecode",
                "inputs": {
                    "samples": [
                        "3",
                        0
                    ],
                    "vae": [
                        "11",
                        0
                    ]
                }
            },
            "9": {
                "class_type": "SaveImage",
                "inputs": {
                    "filename_prefix": "ComfyUI",
                    "images": [
                        "8",
                        0
                    ]
                }
            },
            "10": {
                "class_type": "CLIPLoader",
                "inputs": {
                    "clip_name": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
                    "type": "sd3"
                }
            },
            "11": {
                "class_type": "VAELoader",
                "inputs": {
                    "vae_name": "qwen_image_vae.safetensors"
                }
            }
        }

        print(f"\n🚀 Soumission du workflow...")
        # Note: submit_workflow attend un dict 'prompt' au format API
        prompt_id = client.submit_workflow(workflow_api)
        
        if not prompt_id:
            print("❌ Échec de la soumission du workflow")
            return False
            
        print(f"✅ Workflow soumis avec ID: {prompt_id}")
        
        # Attente du résultat
        print(f"\n⏳ Attente de l'exécution...")
        result = client.get_result(prompt_id, wait_completion=True, timeout=300)
        
        if result and result.get('status', {}).get('completed', False):
            print(f"\n✅ SUCCÈS: Workflow terminé")
            outputs = result.get('outputs', {})
            print(f"📊 Outputs: {len(outputs)}")
            
            # Téléchargement des résultats
            # Définition du dossier de sortie à la racine du projet
            project_root = Path(__file__).parent.parent.parent.parent
            output_dir = os.path.join(project_root, "outputs")
            
            # Création du dossier s'il n'existe pas
            os.makedirs(output_dir, exist_ok=True)
            
            print(f"📂 Dossier de sortie: {output_dir}")
            client.download_result(prompt_id, output_dir)
            return True
        else:
            print(f"\n❌ ÉCHEC: Workflow non terminé ou erreur")
            return False

    except Exception as e:
        error_str = str(e)
        print(f"\n❌ ERREUR CRITIQUE: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    success = test_qwen_workflow()
    sys.exit(0 if success else 1)