#!/usr/bin/env python3
"""
Script pour corriger les chemins des modèles Qwen format Diffusers dans ComfyUI
Crée les liens symboliques nécessaires pour que les loaders standards trouvent les fichiers
"""

import subprocess
import sys
import os

def run_command(cmd, description=""):
    """Exécute une commande Docker et retourne le résultat"""
    print(f"🔧 {description}")
    try:
        result = subprocess.run(
            cmd, shell=True, capture_output=True, text=True, check=True
        )
        if result.returncode == 0:
            print(f"✅ {description}: SUCCÈS")
            return result.stdout
        else:
            print(f"❌ {description}: ÉCHEC (code {result.returncode})")
            print(f"Stderr: {result.stderr}")
            return None
    except Exception as e:
        print(f"❌ {description}: ERREUR {e}")
        return None

def create_model_symlinks():
    """Crée les liens symboliques pour les modèles Qwen format Diffusers"""
    
    print("🚀 Création des liens symboliques pour modèles Qwen...")
    
    # Vérifier que le modèle Diffusers existe
    model_check = run_command(
        'docker exec comfyui-qwen test -d /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8',
        "Vérification modèle Diffusers"
    )
    
    if not model_check:
        print("❌ Modèle Diffusers non trouvé")
        return False
    
    # Créer répertoires standards s'ils n'existent pas
    print("📁 Création répertoires standards...")
    run_command('docker exec comfyui-qwen mkdir -p /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/vae', "Répertoire VAE")
    run_command('docker exec comfyui-qwen mkdir -p /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/unet', "Répertoire UNET")
    run_command('docker exec comfyui-qwen mkdir -p /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/text_encoders', "Répertoire Text Encoders")
    
    # Supprimer anciens liens symboliques
    print("🗑️ Nettoyage anciens liens...")
    run_command('docker exec comfyui-qwen rm -f /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/vae/qwen_image_vae.safetensors', "Suppression VAE")
    run_command('docker exec comfyui-qwen rm -f /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/unet/qwen_image_edit_2509_fp8_e4m3fn.safetensors', "Suppression UNET")
    run_command('docker exec comfyui-qwen rm -f /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/text_encoders/qwen_2.5_vl_7b.safetensors', "Suppression CLIP")
    
    # Créer nouveaux liens symboliques
    print("🔗 Création nouveaux liens symboliques...")
    
    # VAE: lien direct vers fichier unique
    vae_cmd = ('docker exec comfyui-qwen ln -sf '
                 '/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8/vae/diffusion_pytorch_model.safetensors '
                 '/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/vae/qwen_image_vae.safetensors')
    run_command(vae_cmd, "Création lien VAE")
    
    # UNET: lien vers répertoire transformer (shardé)
    unet_cmd = ('docker exec comfyui-qwen ln -sf '
                 '/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8/transformer '
                 '/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/unet/qwen_image_edit_2509_fp8_e4m3fn.safetensors')
    run_command(unet_cmd, "Création lien UNET")
    
    # CLIP: lien vers répertoire text_encoder (shardé)
    clip_cmd = ('docker exec comfyui-qwen ln -sf '
                 '/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8/text_encoder '
                 '/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/text_encoders/qwen_2.5_vl_7b.safetensors')
    run_command(clip_cmd, "Création lien CLIP")
    
    # Vérifier les liens créés
    print("🔍 Vérification des liens créés...")
    run_command('docker exec comfyui-qwen ls -lh /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/vae/', "Vérification VAE")
    run_command('docker exec comfyui-qwen ls -lh /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/unet/', "Vérification UNET")
    run_command('docker exec comfyui-qwen ls -lh /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/text_encoders/', "Vérification CLIP")
    
    return True

def test_workflow():
    """Test le workflow Qwen avec les nouveaux liens"""
    print("🧪 Test du workflow Qwen...")
    
    # Importer le client ComfyUI
    sys.path.append('/home/jesse/SD/workspace/comfyui-qwen/ComfyUI')
    
    try:
        from MyIA.AI.Notebooks.GenAI.shared.helpers.comfyui_client import ComfyUIClient
        
        # Créer le client
        client = ComfyUIClient(
            base_url="http://localhost:8188",
            api_token=None  # Sera lu depuis .env
        )
        
        # Test simple
        print("🎨 Génération image test...")
        image_bytes = client.generate_text2image(
            "A beautiful mountain landscape at sunset",
            width=512,
            height=512,
            steps=10,
            seed=42
        )
        
        if image_bytes:
            # Sauvegarder l'image
            output_path = "/home/jesse/SD/workspace/comfyui-qwen/test_qwen_fixed.png"
            with open(output_path, "wb") as f:
                f.write(image_bytes)
           
            print(f"✅ SUCCÈS: Image générée ({len(image_bytes)} bytes)")
            print(f"📁 Sauvegardée dans: {output_path}")
            return True
        else:
            print("❌ ÉCHEC: Aucune image générée")
            return False
            
    except ImportError as e:
        print(f"❌ Erreur import: {e}")
        return False
    except Exception as e:
        print(f"❌ Erreur test: {e}")
        return False

def main():
    """Fonction principale"""
    print("🔧 Correction Workflow ComfyUI Qwen - Format Diffusers")
    print("=" * 60)
    
    # Étape 1: Créer les liens symboliques
    if not create_model_symlinks():
        print("❌ Échec création liens symboliques")
        return 1
    
    print("\n" + "=" * 60)
    
    # Étape 2: Tester le workflow
    if test_workflow():
        print("\n🎉 SUCCÈS TOTAL: Workflow Qwen corrigé et fonctionnel!")
        return 0
    else:
        print("\n💥 ÉCHEC TOTAL: Workflow toujours en erreur")
        return 2

if __name__ == "__main__":
    sys.exit(main())