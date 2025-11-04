#!/usr/bin/env python3
"""
Test Simple de Génération d'Image ComfyUI Qwen
============================================
Script consolidé pour tester la génération d'images avec Qwen
Utilise les credentials dynamiques et workflow simplifié
"""

import sys
import os
import json
import time
import requests
from pathlib import Path

# Ajout du chemin utils
sys.path.insert(0, str(Path(__file__).parent))

from comfyui_client_helper import ComfyUIClient, ComfyUIConfig

def load_credentials():
    """Charge les credentials depuis le fichier token"""
    token_file = Path(".secrets/qwen-api-user.token")
    
    if not token_file.exists():
        print("❌ Fichier de token non trouvé")
        return None
    
    with open(token_file, 'r') as f:
        token = f.read().strip()
    
    print(f"✅ Token chargé : {token[:20]}...")
    return token

def create_simple_workflow():
    """Crée un workflow simple pour tester la génération - Basé sur script qui fonctionne"""
    return {
        "1": {
            "inputs": {
                "unet_name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
                "weight_dtype": "fp8_e4m3fn"
            },
            "class_type": "UNETLoader",
            "_meta": {
                "title": "Load Diffusion Model"
            }
        },
        "2": {
            "inputs": {
                "clip_name": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
                "type": "sd3"
            },
            "class_type": "CLIPLoader",
            "_meta": {
                "title": "Load CLIP"
            }
        },
        "3": {
            "inputs": {
                "vae_name": "qwen_image_vae.safetensors"
            },
            "class_type": "VAELoader",
            "_meta": {
                "title": "Load VAE"
            }
        },
        "4": {
            "inputs": {
                "width": 1024,
                "height": 1024,
                "batch_size": 1
            },
            "class_type": "EmptySD3LatentImage",
            "_meta": {
                "title": "Empty SD3 Latent Image"
            }
        },
        "5": {
            "inputs": {
                "text": "A serene mountain landscape at sunset with a lake reflecting orange sky",
                "clip": ["2", 0]
            },
            "class_type": "CLIPTextEncode",
            "_meta": {
                "title": "CLIP Text Encode (Positive)"
            }
        },
        "6": {
            "inputs": {
                "text": "ugly, blurry, low quality, distorted, watermark, text",
                "clip": ["2", 0]
            },
            "class_type": "CLIPTextEncode",
            "_meta": {
                "title": "CLIP Text Encode (Negative)"
            }
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
            "_meta": {
                "title": "KSampler"
            }
        },
        "8": {
            "inputs": {
                "samples": ["7", 0],
                "vae": ["3", 0]
            },
            "class_type": "VAEDecode",
            "_meta": {
                "title": "VAE Decode"
            }
        },
        "9": {
            "inputs": {
                "filename_prefix": "test_qwen_simple",
                "images": ["8", 0]
            },
            "class_type": "SaveImage",
            "_meta": {
                "title": "Save Image"
            }
        }
    }

def test_image_generation():
    """Test principal de génération d'image"""
    print("=" * 70)
    print("TEST GÉNÉRATION IMAGE COMFYUI QWEN - VERSION CONSOLIDÉE")
    print("=" * 70)
    
    # Chargement credentials
    token = load_credentials()
    if not token:
        return False
    
    # Initialisation client
    # Configuration du client ComfyUI
    config = ComfyUIConfig(
        host="localhost",
        port=8188,
        protocol="http",
        api_key=token
    )
    client = ComfyUIClient(config)
    
    print("\n📤 Soumission du workflow...")
    try:
        workflow = create_simple_workflow()
        prompt_id = client.submit_workflow(workflow)
        
        if prompt_id:
            print(f"✅ Workflow soumis avec ID: {prompt_id}")
            
            # Attente du résultat avec la méthode du helper
            print("⏳ Attente de la génération...")
            start_time = time.time()
            
            result = client.get_result(prompt_id, wait_completion=True, timeout=120)
            
            if result:
                elapsed = time.time() - start_time
                print(f"✅ Image générée en {elapsed:.1f}s")
                
                # Vérification des outputs
                outputs = result.get('outputs', {})
                if outputs:
                    print(f"📸 {len(outputs)} output(s) trouvé(s)")
                    for node_id, node_output in outputs.items():
                        if isinstance(node_output, dict) and 'images' in node_output:
                            images = node_output['images']
                            for img in images:
                                print(f"   • {img.get('filename', 'unknown')}")
                            return True
                
                print("❌ Aucune image trouvée dans les résultats")
                return False
            else:
                print("❌ Échec ou timeout de la génération")
                return False
        else:
            print("❌ Échec de la soumission du workflow")
            return False
            
    except Exception as e:
        print(f"❌ Erreur lors de la génération: {e}")
        return False

def main():
    """Fonction principale"""
    print("🎯 Test de génération d'image avec Qwen")
    print("📍 Container: comfyui-qwen")
    print("🌐 API: http://localhost:8188")
    
    success = test_image_generation()
    
    print("\n" + "=" * 70)
    if success:
        print("✅ TEST RÉUSSI - Génération d'image fonctionnelle")
    else:
        print("❌ TEST ÉCHOUÉ - Problème de génération")
    print("=" * 70)
    
    return 0 if success else 1

if __name__ == "__main__":
    sys.exit(main())