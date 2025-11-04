#!/usr/bin/env python3
"""
Script Simple - Test Génération d'Image ComfyUI

Ce script teste la génération d'image avec ComfyUI Qwen
en utilisant le workflow minimal.

Auteur: Consolidation Phase 29
Date: 2025-11-01
Version: 1.0.0
"""

import sys
import json
import time
import requests
from pathlib import Path

# Configuration
COMFYUI_URL = "http://localhost:8188"
BCRYPT_HASH = "$2b$12$2jPJrb7dmsM7fw0..PoEqu8nmGarw0vnYYdGw5BFmcZ52bGfwf5M2"

# Workflow minimal pour test
WORKFLOW = {
    "3": {
        "inputs": {
            "seed": 42,
            "steps": 20,
            "cfg": 7.0,
            "sampler_name": "euler",
            "scheduler": "normal",
            "denoise": 1.0,
            "model": ["4", 0],
            "positive": ["6", 0],
            "negative": ["7", 0],
            "latent_image": ["5", 0]
        },
        "class_type": "KSampler"
    },
    "4": {
        "inputs": {
            "ckpt_name": "qwen_vl_v1.safetensors"
        },
        "class_type": "CheckpointLoaderSimple"
    },
    "5": {
        "inputs": {
            "width": 512,
            "height": 512,
            "batch_size": 1
        },
        "class_type": "EmptyLatentImage"
    },
    "6": {
        "inputs": {
            "text": "a beautiful landscape",
            "clip": ["4", 1]
        },
        "class_type": "CLIPTextEncode"
    },
    "7": {
        "inputs": {
            "text": "text, watermark",
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
            "filename_prefix": "ComfyUI_Test",
            "images": ["8", 0]
        },
        "class_type": "SaveImage"
    }
}

def test_image_generation():
    """Test la génération d'image avec authentification"""
    
    print("=" * 60)
    print("Test de Génération d'Image ComfyUI Qwen")
    print("=" * 60)
    
    headers = {
        "Authorization": f"Bearer {BCRYPT_HASH}",
        "Content-Type": "application/json"
    }
    
    print(f"\n1️⃣ Soumission du workflow...")
    
    try:
        # Soumettre le prompt
        response = requests.post(
            f"{COMFYUI_URL}/prompt",
            headers=headers,
            json={"prompt": WORKFLOW},
            timeout=30
        )
        
        if response.status_code != 200:
            print(f"❌ ÉCHEC - Code HTTP {response.status_code}")
            print(f"   Réponse: {response.text}")
            return False
        
        result = response.json()
        prompt_id = result.get("prompt_id")
        
        if not prompt_id:
            print(f"❌ ÉCHEC - Pas de prompt_id dans la réponse")
            print(f"   Réponse: {result}")
            return False
        
        print(f"✅ Workflow soumis - Prompt ID: {prompt_id}")
        
        # Attendre la fin de génération
        print(f"\n2️⃣ Attente de génération...")
        max_wait = 120  # 2 minutes max
        start_time = time.time()
        
        while time.time() - start_time < max_wait:
            history_response = requests.get(
                f"{COMFYUI_URL}/history/{prompt_id}",
                headers=headers,
                timeout=10
            )
            
            if history_response.status_code == 200:
                history = history_response.json()
                
                if prompt_id in history:
                    prompt_info = history[prompt_id]
                    
                    # Vérifier si terminé
                    if "outputs" in prompt_info:
                        print(f"✅ Génération terminée!")
                        
                        # Extraire les informations d'image
                        outputs = prompt_info["outputs"]
                        print(f"\n📸 Images générées:")
                        
                        for node_id, node_output in outputs.items():
                            if "images" in node_output:
                                for img in node_output["images"]:
                                    filename = img.get("filename", "unknown")
                                    subfolder = img.get("subfolder", "")
                                    print(f"   • {filename}")
                                    if subfolder:
                                        print(f"     Dossier: {subfolder}")
                        
                        return True
            
            time.sleep(2)
            print(".", end="", flush=True)
        
        print(f"\n⏱️ TIMEOUT - Génération n'a pas terminé en {max_wait}s")
        return False
        
    except requests.exceptions.ConnectionError:
        print("\n❌ ÉCHEC - Impossible de se connecter au serveur ComfyUI")
        return False
    except Exception as e:
        print(f"\n❌ ERREUR - {type(e).__name__}: {e}")
        import traceback
        traceback.print_exc()
        return False

def main():
    """Point d'entrée principal"""
    success = test_image_generation()
    
    print("\n" + "=" * 60)
    if success:
        print("✅ Test réussi - Image générée avec succès")
        print("\n💡 L'authentification ComfyUI-Login fonctionne parfaitement")
        return 0
    else:
        print("❌ Test échoué - Vérifiez les logs du container")
        return 1

if __name__ == "__main__":
    sys.exit(main())