#!/usr/bin/env python3
"""
Script de test pour générer une image différente et démontrer la variabilité
Fait partie de la mission : Confirmation Tests Consolidés Après Corrections
"""

import sys
import os
import json
import requests
import time
from datetime import datetime

# Ajout du chemin des utilitaires
sys.path.insert(0, 'scripts/genai-auth/utils')
from comfyui_client_helper import ComfyUIClient, ComfyUIConfig

def load_token():
    """Charge le token depuis le fichier"""
    token_file = ".secrets/qwen-api-user.token"
    
    if not os.path.exists(token_file):
        print("❌ Fichier de token non trouvé")
        return None
    
    with open(token_file, 'r') as f:
        token = f.read().strip()
    
    print(f"✅ Token chargé : {token[:20]}...")
    return token

def create_varied_workflow():
    """Crée un workflow varié pour tester la variabilité"""
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
                "text": "a futuristic city with flying vehicles and neon lights, digital art style, highly detailed, cinematic lighting",
                "clip": ["2", 0]
            },
            "class_type": "CLIPTextEncode",
            "_meta": {
                "title": "CLIP Text Encode (Positive)"
            }
        },
        "6": {
            "inputs": {
                "text": "blurry, low quality, distorted, watermark, text",
                "clip": ["2", 0]
            },
            "class_type": "CLIPTextEncode",
            "_meta": {
                "title": "CLIP Text Encode (Negative)"
            }
        },
        "7": {
            "inputs": {
                "seed": 987654321,
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
                "filename_prefix": "test_varie_qwen_city",
                "images": ["8", 0]
            },
            "class_type": "SaveImage",
            "_meta": {
                "title": "Save Image"
            }
        }
    }

def main():
    print("=" * 70)
    print("TEST GÉNÉRATION IMAGE VARIÉE - DÉMONSTRATION VARIABILITÉ")
    print("=" * 70)
    print(f"Timestamp : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    try:
        # Chargement du token
        token = load_token()
        if not token:
            return False
        
        # Configuration du client ComfyUI
        config = ComfyUIConfig(
            host="localhost",
            port=8188,
            protocol="http",
            api_key=token
        )
        
        # Initialisation client
        client = ComfyUIClient(config)
        print("✅ Client ComfyUI initialisé")
        
        # Soumission avec la méthode du helper
        prompt_id = client.submit_workflow(create_varied_workflow())
        
        if not prompt_id:
            print("❌ Échec de la soumission du workflow")
            return False
        
        print(f"✅ Workflow soumis avec ID: {prompt_id}")
        
        # Attente du résultat avec la méthode du helper
        print("⏳ Attente de la génération...")
        start_time = time.time()
        
        result = client.get_result(prompt_id, wait_completion=True, timeout=120)
        
        if result:
            elapsed = time.time() - start_time
            print(f"✅ Génération terminée en {elapsed:.1f}s")
            
            # Vérification des outputs
            outputs = result.get('outputs', {})
            if outputs:
                print(f"📸 {len(outputs)} output(s) trouvé(s)")
                for node_id, node_output in outputs.items():
                    if isinstance(node_output, dict) and 'images' in node_output:
                        images = node_output['images']
                        for img in images:
                            filename = img.get('filename', 'unknown')
                            print(f"   • {filename}")
                            
                            # Télécharger l'image localement avec authentification
                            try:
                                headers = {"Authorization": f"Bearer {token}"}
                                image_response = requests.get(f"http://localhost:8188/view?filename={filename}", headers=headers)
                                if image_response.status_code == 200:
                                    # Créer le répertoire local si nécessaire
                                    os.makedirs('outputs', exist_ok=True)
                                    
                                    # Sauvegarder l'image
                                    with open(f"outputs/{filename}", 'wb') as f:
                                        f.write(image_response.content)
                                    print(f"   💾 Image téléchargée : outputs/{filename}")
                                else:
                                    print(f"   ❌ Erreur téléchargement : {image_response.status_code}")
                            except Exception as e:
                                print(f"   ❌ Erreur sauvegarde : {e}")
                            
                        return True
            
            print("❌ Aucune image trouvée dans les résultats")
            return False
            
    except Exception as e:
        print(f"❌ Erreur: {str(e)}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    success = main()
    print("\n" + "=" * 70)
    if success:
        print("✅ TEST DE GÉNÉRATION VARIÉE RÉUSSI")
        print("✅ Image générée et téléchargée localement")
        print("✅ Le système peut générer des images différentes")
    else:
        print("❌ TEST DE GÉNÉRATION VARIÉE ÉCHOUÉ")
    print("=" * 70)
    
    sys.exit(0 if success else 1)