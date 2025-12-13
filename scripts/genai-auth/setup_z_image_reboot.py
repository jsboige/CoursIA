#!/usr/bin/env python3
"""
Script de configuration pour le reboot de Z-Image Turbo (Phase 37).
Ce script génère le workflow JSON corrigé pour utiliser Z-Image Turbo avec
les bons modèles (SDXL VAE au lieu de Qwen Video VAE, suppression de LatentUnsqueeze).
"""

import json
import os
from pathlib import Path

def main():
    print("🚀 Démarrage de la configuration Z-Image Turbo Reboot...")

    # Chemins
    workspace_dir = Path("docker-configurations/services/comfyui-qwen/workspace")
    output_workflow_path = workspace_dir / "workflow_z_image_reboot.json"
    
    # Vérification des modèles pré-requis (juste pour information, on suppose qu'ils sont là d'après l'analyse précédente)
    models_dir = Path("docker-configurations/shared/models")
    unet_path = models_dir / "unet" / "z_image_turbo-Q5_K_M.gguf"
    clip_path = models_dir / "clip" / "gemma-2-2b-it-Q4_K_M.gguf"
    vae_path = models_dir / "vae" / "sdxl_vae.safetensors"

    print(f"📦 Vérification des fichiers modèles...")
    if unet_path.exists():
        print(f"  ✅ UNET: {unet_path.name} trouvé.")
    else:
        print(f"  ❌ UNET: {unet_path.name} MANQUANT !")
    
    if clip_path.exists():
        print(f"  ✅ CLIP: {clip_path.name} trouvé.")
    else:
        print(f"  ❌ CLIP: {clip_path.name} MANQUANT !")

    if vae_path.exists():
        print(f"  ✅ VAE: {vae_path.name} trouvé.")
    else:
        print(f"  ❌ VAE: {vae_path.name} MANQUANT !")

    # Définition du Workflow Corrigé
    # Basé sur workflow_z_image.json mais avec :
    # - VAE: sdxl_vae.safetensors
    # - Suppression de LatentUnsqueeze (Node 12)
    # - Connection directe KSampler -> VAEDecode
    
    workflow = {
        "3": {
            "inputs": {
                "seed": 42,
                "steps": 20,
                "cfg": 3.0,
                "sampler_name": "euler",
                "scheduler": "normal",
                "denoise": 1,
                "model": ["4", 0],
                "positive": ["6", 0],
                "negative": ["7", 0],
                "latent_image": ["5", 0]
            },
            "class_type": "KSampler",
            "_meta": {
                "title": "KSampler"
            }
        },
        "4": {
            "inputs": {
                "unet_name": "z_image_turbo-Q5_K_M.gguf"
            },
            "class_type": "UnetLoaderGGUF",
            "_meta": {
                "title": "Unet Loader (GGUF)"
            }
        },
        "5": {
            "inputs": {
                "width": 1024,
                "height": 1024,
                "batch_size": 1
            },
            "class_type": "EmptyLatentImage",
            "_meta": {
                "title": "Empty Latent Image"
            }
        },
        "6": {
            "inputs": {
                "text": "A cinematic shot of a cyberpunk samurai in a neon city, raining, reflections, 8k, highly detailed, photorealistic",
                "clip": ["10", 0]
            },
            "class_type": "CLIPTextEncode",
            "_meta": {
                "title": "CLIP Text Encode (Positive)"
            }
        },
        "7": {
            "inputs": {
                "text": "blur, low quality, watermark, text, logo, bad anatomy, deformed",
                "clip": ["10", 0]
            },
            "class_type": "CLIPTextEncode",
            "_meta": {
                "title": "CLIP Text Encode (Negative)"
            }
        },
        "8": {
            "inputs": {
                "samples": ["3", 0],  # DIRECTEMENT connecté au KSampler (plus de LatentUnsqueeze)
                "vae": ["9", 0]
            },
            "class_type": "VAEDecode",
            "_meta": {
                "title": "VAE Decode"
            }
        },
        "9": {
            "inputs": {
                "vae_name": "sdxl_vae.safetensors" # UTILISATION DU VAE SDXL STANDARD
            },
            "class_type": "VAELoader",
            "_meta": {
                "title": "VAE Loader"
            }
        },
        "10": {
            "inputs": {
                "clip_name": "gemma-2-2b-it-Q4_K_M.gguf",
                "type": "lumina2"
            },
            "class_type": "CLIPLoaderGGUF",
            "_meta": {
                "title": "CLIP Loader (GGUF)"
            }
        },
        "11": {
            "inputs": {
                "filename_prefix": "Z-Image-Reboot",
                "images": ["8", 0]
            },
            "class_type": "SaveImage",
            "_meta": {
                "title": "Save Image"
            }
        }
    }

    print(f"📝 Génération du workflow corrigé...")
    try:
        with open(output_workflow_path, "w", encoding="utf-8") as f:
            json.dump(workflow, f, indent=2)
        print(f"✅ Workflow sauvegardé : {output_workflow_path}")
    except Exception as e:
        print(f"❌ Erreur lors de la sauvegarde du workflow : {e}")

    print("🏁 Configuration terminée.")

if __name__ == "__main__":
    main()