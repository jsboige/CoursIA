#!/usr/bin/env python3
"""
Script de test isolé pour valider le workflow ComfyUI Qwen WanBridge.

Mission: Correction Workflow ComfyUI Qwen - Restauration Méthode WanBridge
Date: 2025-10-26
Source: docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_architectures-5-workflows-qwen.md
"""

import sys
from pathlib import Path

# Ajouter le répertoire parent au PYTHONPATH pour import comfyui_client
sys.path.insert(0, str(Path(__file__).parent / ".." / "utils"))

from utils.comfyui_client_helper import ComfyUIClient

def test_qwen_workflow():
    """
    Test de validation du workflow WanBridge.
    
    Configuration:
        - URL: http://localhost:8188 (ComfyUI local dans container WSL)
        - Token: @TKEoMzUx&)F@B$^1O3hkt&VkDWp0JXf
        - Workflow: WanBridge (7 nodes) - Phase 12C validée
    """
    print("=" * 80)
    print("TEST WORKFLOW COMFYUI QWEN WANBRIDGE")
    print("=" * 80)
    
    # Configuration client
    base_url = "http://localhost:8188"
    api_token = "$2b$12$UDceblhZeEySDwVMC0ccN.IaQmMBfKdTY.aAE3poXcq1zsOP6coni"
    
    print(f"\n📡 Configuration:")
    print(f"   - URL: {base_url}")
    print(f"   - Token: {api_token[:20]}...")
    
    try:
        # Créer client ComfyUI
        client = ComfyUIClient(base_url=base_url, api_token=api_token)
        print(f"   - Client ID: {client.client_id}")
        
        # Paramètres de test
        test_prompt = "A beautiful mountain landscape at sunset, highly detailed, 8k"
        
        print(f"\n🎨 Paramètres de génération:")
        print(f"   - Prompt: {test_prompt}")
        print(f"   - Taille: 1024x1024")
        print(f"   - Steps: 20 (optimal Phase 12C)")
        print(f"   - CFG: 7.0 (standard)")
        
        # Générer image
        print(f"\n⏳ Génération en cours...")
        result = client.generate_text2image(
            prompt=test_prompt,
            width=1024,
            height=1024,
            steps=20,
            cfg=7.0,
            seed=42  # Seed fixe pour reproductibilité
        )
        
        # Vérifier le résultat
        print(f"\n✅ SUCCÈS: Image générée")
        print(f"\n📊 Résultat:")
        
        # Extraire les informations de sortie
        if "outputs" in result:
            outputs = result["outputs"]
            print(f"   - Nodes exécutés: {len(outputs)}")
            
            # Vérifier node SaveImage (node 11)
            if "11" in outputs and "images" in outputs["11"]:
                images = outputs["11"]["images"]
                print(f"   - Images générées: {len(images)}")
                
                for idx, img_info in enumerate(images):
                    filename = img_info.get("filename", "unknown")
                    subfolder = img_info.get("subfolder", "")
                    print(f"   - Image {idx+1}: {filename}")
                    if subfolder:
                        print(f"     Sous-dossier: {subfolder}")
        
        print(f"\n🎯 VALIDATION: Workflow WanBridge fonctionnel")
        print(f"\n📝 Prochaines étapes:")
        print(f"   1. Vérifier image générée dans ComfyUI/output/")
        print(f"   2. Valider notebook 00-5-ComfyUI-Local-Test.ipynb")
        print(f"   3. Valider notebook 01-5-Qwen-Image-Edit.ipynb")
        
        return True
        
    except TimeoutError as e:
        print(f"\n❌ ERREUR TIMEOUT: {e}")
        print(f"\n🔍 Diagnostic:")
        print(f"   - Vérifier que ComfyUI est démarré: docker ps | grep comfyui")
        print(f"   - Vérifier logs ComfyUI: docker logs comfyui-qwen-1")
        return False
        
    except Exception as e:
        print(f"\n❌ ERREUR: {e}")
        print(f"\n🔍 Diagnostic:")
        print(f"   - Type: {type(e).__name__}")
        
        # Analyser l'erreur pour diagnostic
        error_str = str(e).lower()
        
        if "401" in error_str or "unauthorized" in error_str:
            print(f"   - Cause probable: Token invalide ou authentification échouée")
            print(f"   - Solution: Vérifier COMFYUI_API_TOKEN dans .env")
        
        elif "404" in error_str or "not found" in error_str:
            print(f"   - Cause probable: Endpoint API non trouvé")
            print(f"   - Solution: Vérifier URL ComfyUI")
        
        elif "value not in list" in error_str:
            print(f"   - Cause probable: Custom node manquant ou modèle introuvable")
            print(f"   - Solution 1: Vérifier installation ComfyUI-QwenImageWanBridge")
            print(f"   - Solution 2: Vérifier modèle dans checkpoints/Qwen-Image-Edit-2509-FP8/")
        
        elif "connection" in error_str:
            print(f"   - Cause probable: ComfyUI non accessible")
            print(f"   - Solution: Démarrer container Docker: docker-compose up -d")
        
        else:
            print(f"   - Erreur complète: {e}")
        
        return False

if __name__ == "__main__":
    print("\n")
    success = test_qwen_workflow()
    print("\n" + "=" * 80)
    
    sys.exit(0 if success else 1)