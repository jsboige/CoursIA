#!/usr/bin/env python3
"""
Test minimal du workflow Qwen WanBridge pour isoler l'erreur
"""

import os
import json
import random
from dotenv import load_dotenv
from utils.comfyui_client_helper import ComfyUIClient

# Charger configuration
load_dotenv()
COMFYUI_BASE_URL = os.getenv("COMFYUI_BASE_URL", "http://localhost:8188")
COMFYUI_API_TOKEN = os.getenv("COMFYUI_API_TOKEN")

print("=== TEST MINIMAL WORKFLOW QWEN ===")
print(f"URL: {COMFYUI_BASE_URL}")
print(f"Token configuré: {'OUI' if COMFYUI_API_TOKEN else 'NON'}")
print()

# Workflow minimal pour isoler le problème
minimal_workflow = {
    "1": {
        "class_type": "QwenVLCLIPLoader",
        "inputs": {
            "model_path": "Qwen-Image-Edit-2509-FP8"
        }
    },
    "2": {
        "class_type": "TextEncodeQwenImageEdit",
        "inputs": {
            "text": "test simple",
            "clip": ["1", 0]
        }
    },
    "3": {
        "class_type": "QwenVLEmptyLatent",
        "inputs": {
            "width": 512,
            "height": 512,
            "batch_size": 1
        }
    },
    "4": {
        "class_type": "QwenImageSamplerNode",
        "inputs": {
            "seed": 42,
            "steps": 5,
            "cfg": 3.0,
            "transformer": ["1", 1],
            "positive": ["2", 0],
            "latent_image": ["3", 0]
        }
    },
    "5": {
        "class_type": "VAEDecode",
        "inputs": {
            "samples": ["4", 0],
            "vae": ["1", 2]
        }
    }
}

print("🔧 WORKFLOW MINIMAL:")
print(json.dumps(minimal_workflow, indent=2))
print()

# Test avec client ComfyUI
try:
    client = ComfyUIClient(
        base_url=COMFYUI_BASE_URL,
        api_token=COMFYUI_API_TOKEN
    )
    
    print("🚀 LANCEMENT DU TEST...")
    result = client._execute_workflow(minimal_workflow)
    
    if result and len(result) > 0:
        print("✅ SUCCÈS: Workflow exécuté")
        print(f"📊 Résultat: {len(result)} outputs générés")
        
        # Analyser la structure du résultat
        for i, output in enumerate(result):
            print(f"  Output {i}: {type(output)} - {str(output)[:100]}...")
    else:
        print("❌ ÉCHEC: Aucun résultat retourné")
        
except Exception as e:
    print(f"❌ ERREUR: {e}")
    print(f"Type: {type(e)}")
    
    # Si erreur HTTP 400, analyser plus en détail
    if "400" in str(e):
        print("\n🔍 ANALYSE ERREUR 400:")
        print("L'erreur vient probablement du serveur ComfyUI")
        print("Le node VAEDecode n'arrive pas à traiter l'entrée du QwenImageSamplerNode")
        print("\n💡 SOLUTIONS POSSIBLES:")
        print("1. Vérifier la documentation du custom node WanBridge")
        print("2. Consulter les exemples de workflows fournis avec le node")
        print("3. Vérifier si le format de sortie du QwenImageSamplerNode a changé")
        print("4. Tester avec une version plus ancienne/stable du custom node")

print("\n📋 CONCLUSION:")
print("Ce test minimal permet d'isoler le problème exact")
print("Si l'erreur persiste, le problème est dans le workflow lui-même")
print("Si le test réussit, ajouter progressivement les autres nodes")