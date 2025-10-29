#!/usr/bin/env python3
"""
Script de diagnostic pour l'erreur HTTP 400 dans le workflow Qwen WanBridge
"""

import os
import json
from dotenv import load_dotenv

# Charger configuration
load_dotenv()
COMFYUI_BASE_URL = os.getenv("COMFYUI_BASE_URL", "http://localhost:8188")
COMFYUI_API_TOKEN = os.getenv("COMFYUI_API_TOKEN")

print("=== DIAGNOSTIC WORKFLOW QWEN WANBRIDGE ===")
print(f"URL: {COMFYUI_BASE_URL}")
print(f"Token: {'***' + COMFYUI_API_TOKEN[-10:] if COMFYUI_API_TOKEN else 'MISSING'}")
print()

# Analyser l'erreur du test précédent
error_details = {
    "error_type": "prompt_outputs_failed_validation",
    "node_id": "66",
    "exception_type": "IndexError",
    "exception_message": "tuple index out of range",
    "input_name": "images",
    "input_config": ["IMAGE", {"tooltip": "The images to save."}]
}

print("🔍 ANALYSE DE L'ERREUR:")
print(f"Type: {error_details['error_type']}")
print(f"Node: {error_details['node_id']}")
print(f"Exception: {error_details['exception_type']}")
print(f"Message: {error_details['exception_message']}")
print(f"Input: {error_details['input_name']}")
print()

print("🎯 HYPOTHÈSES:")
print("1. Le node VAEDecode attend un format d'images différent")
print("2. Le node QwenImageSamplerNode retourne un format incompatible")
print("3. Problème de connexion entre nodes (format latent vs images)")
print("4. Version incompatible du custom node ComfyUI-QwenImageWanBridge")
print()

print("🔧 ACTIONS RECOMMANDÉES:")
print("1. Vérifier la signature exacte du node VAEDecode")
print("2. Vérifier la sortie du node QwenImageSamplerNode")
print("3. Consulter la documentation du custom node WanBridge")
print("4. Tester avec un workflow minimal (2 nodes seulement)")
print()

# Workflow minimal pour test
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
            "text": "test prompt",
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
            "steps": 10,
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

print("📋 WORKFLOW MINIMAL CRÉÉ:")
print(json.dumps(minimal_workflow, indent=2))
print()

print("💡 PROCHAINE ÉTAPE:")
print("Exécuter ce workflow minimal pour isoler le problème")
print("Si succès: ajouter progressivement les autres nodes")
print("Si échec: identifier le node exact qui cause l'erreur")