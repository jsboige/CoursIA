#!/usr/bin/env python3
"""
Script de diagnostic pour vérifier les modèles et nodes Qwen dans ComfyUI.
Vérifie la présence des fichiers requis par le workflow corrigé.
"""

import subprocess
import sys
from pathlib import Path

def run_wsl_command(command: str) -> tuple[int, str, str]:
    """Exécute une commande WSL et retourne (code, stdout, stderr)."""
    full_cmd = f'wsl -d Ubuntu -e bash -c "{command}"'
    result = subprocess.run(
        full_cmd,
        shell=True,
        capture_output=True,
        text=True
    )
    return result.returncode, result.stdout, result.stderr

def check_model_files():
    """Vérifie la présence des fichiers modèles requis."""
    print("=" * 80)
    print("VÉRIFICATION DES FICHIERS MODÈLES QWEN")
    print("=" * 80)
    print()
    
    required_files = {
        "CLIP": "qwen_2.5_vl_7b.safetensors",
        "VAE": "qwen_image_vae.safetensors",
        "UNET": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "LoRA": "Qwen-Image-Edit-Lightning-8steps-V1.0.safetensors"
    }
    
    base_paths = [
        "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models",
        "/home/jesse/SD/workspace/comfyui-qwen/models"
    ]
    
    for model_type, filename in required_files.items():
        print(f"\n🔍 Recherche {model_type}: {filename}")
        found = False
        
        for base_path in base_paths:
            # Recherche récursive dans tous les sous-dossiers de models/
            cmd = f"find {base_path} -type f -name '{filename}' 2>/dev/null"
            code, stdout, stderr = run_wsl_command(cmd)
            
            if stdout.strip():
                print(f"   ✅ TROUVÉ: {stdout.strip()}")
                found = True
                break
        
        if not found:
            print(f"   ❌ NON TROUVÉ: {filename}")
            print(f"      Chemins recherchés: {', '.join(base_paths)}")

def check_custom_nodes():
    """Vérifie la présence des custom nodes requis."""
    print("\n" + "=" * 80)
    print("VÉRIFICATION DES CUSTOM NODES QWEN")
    print("=" * 80)
    print()
    
    required_nodes = [
        "QwenVLCLIPLoader",
        "QwenVLTextEncoder",
        "QwenVLEmptyLatent",
        "QwenTemplateBuilder"
    ]
    
    node_pack_path = "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/custom_nodes/ComfyUI-QwenImageWanBridge"
    
    for node_name in required_nodes:
        print(f"\n🔍 Vérification {node_name}:")
        cmd = f"grep -r '{node_name}' {node_pack_path}/__init__.py 2>/dev/null"
        code, stdout, stderr = run_wsl_command(cmd)
        
        if stdout.strip():
            print(f"   ✅ TROUVÉ dans __init__.py")
        else:
            print(f"   ❌ NON TROUVÉ dans __init__.py")

def check_comfyui_api():
    """Vérifie si l'API ComfyUI est accessible."""
    print("\n" + "=" * 80)
    print("VÉRIFICATION API COMFYUI")
    print("=" * 80)
    print()
    
    # Vérifier si le container est up
    cmd = "docker ps --filter 'name=comfyui-qwen' --format '{{.Names}}\\t{{.Status}}'"
    code, stdout, stderr = run_wsl_command(cmd)
    
    if stdout.strip():
        print(f"✅ Container actif:\n{stdout}")
    else:
        print("❌ Container ComfyUI non trouvé ou arrêté")
        print("   Vérifiez avec: docker ps -a | grep comfyui")

def main():
    """Fonction principale."""
    print("\n🔍 DIAGNOSTIC COMPLET COMFYUI QWEN\n")
    
    check_model_files()
    check_custom_nodes()
    check_comfyui_api()
    
    print("\n" + "=" * 80)
    print("DIAGNOSTIC TERMINÉ")
    print("=" * 80)
    print()
    print("Si des fichiers sont manquants, téléchargez-les depuis:")
    print("- CLIP/VAE/UNET: https://huggingface.co/Qwen/Qwen-Image-Edit-2509")
    print("- LoRA: https://huggingface.co/Qwen/Qwen-Image-Edit-2509/tree/main")
    print()

if __name__ == "__main__":
    main()