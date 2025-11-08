#!/usr/bin/env python3
"""
Script de validation GPU et CUDA pour ComfyUI Docker
Créé pour la validation du démarrage ComfyUI - 2025-11-06
"""

import subprocess
import json
import sys

def run_command(cmd):
    """Exécute une commande et retourne le résultat"""
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        return result.returncode == 0, result.stdout, result.stderr
    except Exception as e:
        return False, "", str(e)

def validate_docker_container():
    """Vérifie que le container ComfyUI est en cours d'exécution"""
    print("🔍 Validation du container Docker ComfyUI...")
    success, stdout, stderr = run_command("cd docker-configurations/comfyui-qwen && docker-compose ps")
    
    if success and "comfyui-qwen" in stdout and "Up" in stdout:
        print("✅ Container ComfyUI est bien démarré")
        return True
    else:
        print("❌ Container ComfyUI n'est pas correctement démarré")
        print(f"Erreur: {stderr}")
        return False

def validate_gpu_detection():
    """Valide la détection GPU via nvidia-smi"""
    print("\n🎮 Validation GPU avec nvidia-smi...")
    success, stdout, stderr = run_command("docker exec comfyui-qwen nvidia-smi")
    
    if success:
        if "RTX 3090" in stdout and "24576MiB" in stdout:
            print("✅ GPU RTX 3090 avec 24GB VRAM détecté")
            return True
        else:
            print("⚠️ GPU détecté mais configuration inattendue")
            print(stdout)
            return False
    else:
        print("❌ Impossible d'exécuter nvidia-smi dans le container")
        print(f"Erreur: {stderr}")
        return False

def validate_pytorch_cuda():
    """Valide PyTorch et CUDA à l'intérieur du container"""
    print("\n🔥 Validation PyTorch et CUDA...")
    
    # Création du script de test temporaire
    test_script = '''
import torch
print("PyTorch version:", torch.__version__)
print("CUDA available:", torch.cuda.is_available())
print("CUDA version:", torch.version.cuda)
print("GPU count:", torch.cuda.device_count())
print("Current device:", torch.cuda.current_device())
print("Device name:", torch.cuda.get_device_name(0))
print("VRAM total:", torch.cuda.get_device_properties(0).total_memory / 1024**3, "GB")
'''
    
    cmd = f'''docker exec comfyui-qwen bash -c "cd /workspace/ComfyUI && . venv/bin/activate && python -c '{test_script}'"'''
    
    success, stdout, stderr = run_command(cmd)
    
    if success:
        print("✅ Configuration PyTorch/CUDA validée:")
        for line in stdout.strip().split('\n'):
            print(f"   {line}")
        return True
    else:
        print("❌ Erreur lors de la validation PyTorch/CUDA")
        print(f"Erreur: {stderr}")
        return False

def validate_comfyui_api():
    """Valide l'API ComfyUI"""
    print("\n🌐 Validation API ComfyUI...")
    success, stdout, stderr = run_command("curl -f http://localhost:8188/system_stats")
    
    if success:
        try:
            data = json.loads(stdout)
            system = data.get('system', {})
            devices = data.get('devices', [])
            
            print("✅ API ComfyUI accessible")
            print(f"   Version ComfyUI: {system.get('comfyui_version', 'N/A')}")
            print(f"   Version PyTorch: {system.get('pytorch_version', 'N/A')}")
            
            if devices:
                device = devices[0]
                vram_total = device.get('vram_total', 0) / (1024**3)
                vram_free = device.get('vram_free', 0) / (1024**3)
                print(f"   GPU: {device.get('name', 'N/A')}")
                print(f"   VRAM: {vram_free:.1f}GB libre / {vram_total:.1f}GB total")
            
            return True
        except json.JSONDecodeError:
            print("❌ Réponse API invalide")
            return False
    else:
        print("❌ API ComfyUI inaccessible")
        print(f"Erreur: {stderr}")
        return False

def main():
    """Fonction principale de validation"""
    print("🚀 VALIDATION GPU ET CUDA - COMFYUI DOCKER")
    print("=" * 50)
    
    validations = [
        ("Container Docker", validate_docker_container),
        ("Détection GPU", validate_gpu_detection),
        ("PyTorch/CUDA", validate_pytorch_cuda),
        ("API ComfyUI", validate_comfyui_api),
    ]
    
    results = {}
    for name, validator in validations:
        results[name] = validator()
    
    print("\n" + "=" * 50)
    print("📊 RÉSUMÉ DE VALIDATION")
    print("=" * 50)
    
    all_passed = True
    for name, result in results.items():
        status = "✅ VALIDÉ" if result else "❌ ÉCHEC"
        print(f"{name:20} : {status}")
        if not result:
            all_passed = False
    
    print("\n" + "=" * 50)
    if all_passed:
        print("🎉 TOUTES LES VALIDATIONS RÉUSSIES !")
        print("ComfyUI est prêt pour la génération d'images.")
        return 0
    else:
        print("⚠️ CERTAINES VALIDATIONS ONT ÉCHOUÉ")
        print("Veuillez corriger les problèmes avant de continuer.")
        return 1

if __name__ == "__main__":
    sys.exit(main())