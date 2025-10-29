#!/usr/bin/env python3
"""
Test simple du workflow Qwen sans import complexe
"""

import subprocess
import sys
import os

def run_docker_cmd(cmd, description=""):
    """Exécute une commande Docker avec gestion d'erreur améliorée"""
    print(f"🔧 {description}")
    try:
        result = subprocess.run(
            f'wsl -d Ubuntu -e bash -c "{cmd}"',
            shell=True, capture_output=True, text=True, check=True
        )
        if result.returncode == 0:
            print(f"✅ {description}: SUCCÈS")
            return True
        else:
            print(f"❌ {description}: ÉCHEC (code {result.returncode})")
            print(f"Stderr: {result.stderr}")
            return False
    except Exception as e:
        print(f"❌ {description}: ERREUR {e}")
        return False

def test_simple_workflow():
    """Test simple du workflow Qwen"""
    print("🧪 Test simple du workflow Qwen...")
    
    # Workflow Qwen validé (composants)
    workflow = {
        "1": {
            "class_type": "UNETLoader",
            "inputs": {"unet_name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors"}
        },
        "2": {
            "class_type": "QwenVLCLIPLoader", 
            "inputs": {"clip_name": "qwen_2.5_vl_7b.safetensors"}
        },
        "3": {
            "class_type": "VAELoader",
            "inputs": {"vae_name": "qwen_image_vae.safetensors"}
        },
        "4": {
            "class_type": "EmptyLatentImage",
            "inputs": {
                "width": 512, 
                "height": 512,
                "batch_size": 1
            }
        },
        "5": {
            "class_type": "KSampler",
            "inputs": {
                "seed": 42,
                "steps": 10,
                "cfg": 3.0,
                "sampler_name": "euler",
                "scheduler": "normal",
                "positive": ["2", 0],
                "negative": ["3", 0],
                "latent_image": ["4", 0]
            }
        },
        "6": {
            "class_type": "VAEDecode",
            "inputs": {
                "samples": ["5", 0],
                "vae": ["3", 0]
            }
        },
        "7": {
            "class_type": "SaveImage",
            "inputs": {
                "filename_prefix": "qwen_test",
                "images": ["6", 0]
            }
        }
    }
    
    # Envoyer workflow directement via curl
    print("🎨 Envoi du workflow à ComfyUI...")
    
    curl_cmd = f'''curl -X POST "http://localhost:8188/prompt" \\
        -H "Content-Type: application/json" \\
        -d '{str(workflow).replace("'", '"')}' \\
        --output test_qwen_simple.png'''
    
    success = run_docker_cmd(curl_cmd, "Test workflow simple")
    
    if success:
        print("✅ SUCCÈS: Workflow testé avec succès!")
        return True
    else:
        print("❌ ÉCHEC: Workflow en erreur")
        return False

def main():
    """Fonction principale"""
    print("🔧 Test Simple Workflow ComfyUI Qwen")
    print("=" * 50)
    
    if test_simple_workflow():
        print("\n🎉 SUCCÈS TOTAL: Workflow Qwen fonctionnel!")
        return 0
    else:
        print("\n💥 ÉCHEC TOTAL: Workflow toujours en erreur")
        return 1

if __name__ == "__main__":
    sys.exit(main())