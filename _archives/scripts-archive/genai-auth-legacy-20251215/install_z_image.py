#!/usr/bin/env python3
"""
Script de configuration pour le reboot de Z-Image Turbo (Phase 37).
Télécharge les modèles requis et génère le workflow ComfyUI.
"""

import json
import os
import sys
import time
from pathlib import Path
import urllib.request
import ssl

# Désactiver la vérification SSL pour éviter les erreurs de certificat dans certains environnements
ssl._create_default_https_context = ssl._create_unverified_context

MODELS_CONFIG = {
    # "unet": {
    #     "url": "https://huggingface.co/city96/Lumina-Next-SFT-gguf/resolve/main/lumina-next-sft-Q5_K_M.gguf",
    #     "filename": "z_image_turbo-Q5_K_M.gguf", # Renommé pour clarté locale
    #     "subfolder": "unet"
    # },
    # "clip": {
    #     "url": "https://huggingface.co/bartowski/gemma-1.1-2b-it-GGUF/resolve/main/gemma-1.1-2b-it-Q4_K_M.gguf",
    #     "filename": "gemma-1.1-2b-it-Q4_K_M.gguf",
    #     "subfolder": "clip"
    # },
    "vae": {
        "url": "https://huggingface.co/madebyollin/sdxl-vae-fp16-fix/resolve/main/sdxl_vae.safetensors",
        "filename": "sdxl_vae.safetensors",
        "subfolder": "vae"
    }
}

def download_file(url, dest_path):
    """Télécharge un fichier avec une barre de progression simple."""
    print(f"⬇️ Téléchargement de {dest_path.name}...")
    print(f"   Source : {url}")
    
    try:
        with urllib.request.urlopen(url) as response:
            total_size = int(response.info().get('Content-Length', 0))
            block_size = 8192
            downloaded = 0
            start_time = time.time()
            
            with open(dest_path, 'wb') as f:
                while True:
                    buffer = response.read(block_size)
                    if not buffer:
                        break
                    downloaded += len(buffer)
                    f.write(buffer)
                    
                    # Progression
                    if total_size > 0:
                        percent = downloaded * 100 / total_size
                        mb_downloaded = downloaded / (1024 * 1024)
                        mb_total = total_size / (1024 * 1024)
                        sys.stdout.write(f"\r   ⏳ {percent:.1f}% ({mb_downloaded:.1f}/{mb_total:.1f} MB)")
                        sys.stdout.flush()
            
            print(f"\n   ✅ Téléchargement terminé en {time.time() - start_time:.1f}s.")
            return True
            
    except Exception as e:
        print(f"\n   ❌ Erreur de téléchargement : {e}")
        if dest_path.exists():
            os.remove(dest_path) # Nettoyage du fichier partiel
        return False

def generate_workflow(workspace_dir):
    """Génère le fichier workflow JSON."""
    output_workflow_path = workspace_dir / "workflow_z_image_reboot.json"
    
    workflow = {
        "1": {
            "inputs": {
                "model_path": "Alpha-VLLM/Lumina-Next-SFT-diffusers",
                "prompt": "A cinematic shot of a cyberpunk samurai in a neon city, raining, reflections, 8k, highly detailed, photorealistic",
                "negative_prompt": "blur, low quality, watermark, text, logo, bad anatomy, deformed",
                "num_inference_steps": 20,
                "guidance_scale": 4.0,
                "seed": 42,
                "batch_size": 1,
                "scaling_watershed": 0.3,
                "proportional_attn": True,
                "clean_caption": True,
                "max_sequence_length": 256,
                "use_time_shift": False,
                "t_shift": 4,
                "strength": 1.0
            },
            "class_type": "LuminaDiffusersNode",
            "_meta": {
                "title": "Lumina-Next-SFT Diffusers"
            }
        },
        "8": {
            "inputs": {
                "samples": ["1", 0],
                "vae": ["9", 0]
            },
            "class_type": "VAEDecode",
            "_meta": {
                "title": "VAE Decode"
            }
        },
        "9": {
            "inputs": {
                "vae_name": MODELS_CONFIG["vae"]["filename"]
            },
            "class_type": "VAELoader",
            "_meta": {
                "title": "VAE Loader"
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
        # Assurer que le dossier workspace existe
        workspace_dir.mkdir(parents=True, exist_ok=True)
        
        with open(output_workflow_path, "w", encoding="utf-8") as f:
            json.dump(workflow, f, indent=2)
        print(f"✅ Workflow sauvegardé : {output_workflow_path}")
        return True
    except Exception as e:
        print(f"❌ Erreur lors de la sauvegarde du workflow : {e}")
        return False

def main():
    print("🚀 Démarrage de l'installation Z-Image Turbo Reboot (Phase 37)...")

    # Chemins de base
    base_dir = Path("docker-configurations")
    models_dir = base_dir / "shared/models"
    workspace_dir = base_dir / "services/comfyui-qwen/workspace"

    # 1. Vérification et téléchargement des modèles
    print("\n📦 Gestion des modèles...")
    for model_key, config in MODELS_CONFIG.items():
        if model_key == "clip": continue # Skip clip download (handled manually/via huggingface-cli)
        
        target_dir = models_dir / config["subfolder"]
        target_dir.mkdir(parents=True, exist_ok=True)
        
        target_file = target_dir / config["filename"]
        
        if target_file.exists():
            print(f"  ✅ {model_key.upper()}: {target_file.name} déjà présent.")
        else:
            print(f"  📥 {model_key.upper()}: {target_file.name} manquant.")
            success = download_file(config["url"], target_file)
            if not success:
                print("🚨 Arrêt critique : impossible de récupérer tous les modèles.")
                return

    # 2. Génération du workflow
    print("\n⚙️  Configuration du workflow...")
    if generate_workflow(workspace_dir):
        print("\n✨ Installation terminée avec succès !")
        print("👉 Vous pouvez maintenant lancer le test de validation.")
    else:
        print("\n❌ L'installation a rencontré des problèmes.")

if __name__ == "__main__":
    main()