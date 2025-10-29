#!/usr/bin/env python3
"""
Script d'inspection détaillée du workflow Qwen WanBridge
Pour analyser les connexions et identifier les problèmes de type
"""

import sys
import os
sys.path.append('shared/helpers')
from comfyui_client import ComfyUIClient

def inspect_workflow():
    """Inspecte le workflow Qwen WanBridge en détail"""
    
    client = ComfyUIClient('http://localhost:8188', 'dummy_token')
    
    # Obtenir le workflow en utilisant la méthode correcte
    workflow = client.generate_text2image(
        'test prompt',
        width=1024,
        height=1024,
        steps=20,
        cfg=7.0,
        seed=12345,
        save_prefix='test_output'
    )
    
    print("🔍 INSPECTION DÉTAILLÉE WORKFLOW QWEN WANBRIDGE")
    print("=" * 60)
    
    # Analyse du QwenImageSamplerNode (ID 5)
    print("\n📊 QwenImageSamplerNode (ID 5):")
    sampler_node = workflow['5']
    print(f"  Class: {sampler_node['class_type']}")
    print("  Inputs:")
    for key, value in sampler_node['inputs'].items():
        print(f"    {key}: {value}")
    
    # Analyse des sorties potentielles du sampler
    print("  Sorties attendues:")
    print("    - output 0: LATENT (échantillonnage latent)")
    
    # Analyse du VAEDecode (ID 6)
    print("\n🎨 VAEDecode (ID 6):")
    vae_node = workflow['6']
    print(f"  Class: {vae_node['class_type']}")
    print("  Inputs:")
    for key, value in vae_node['inputs'].items():
        print(f"    {key}: {value}")
    
    # Analyse des entrées attendues du VAEDecode
    print("  Entrées attendues:")
    print("    - samples: LATENT (obligatoire)")
    print("    - vae: VAE (optionnel)")
    
    # Analyse de la connexion problématique
    print("\n🔗 ANALYSE DE LA CONNEXION PROBLÉMATIQUE:")
    print("  Connexion actuelle: [\"5\", 0] -> samples")
    print("  ❌ PROBLÈME: Le QwenImageSamplerNode sort peut-être autre chose que LATENT")
    print("  💡 HYPOTHÈSE: Il faut vérifier la sortie réelle du sampler")
    
    # Analyse du SaveImage (ID 7)
    print("\n💾 SaveImage (ID 7):")
    save_node = workflow['7']
    print(f"  Class: {save_node['class_type']}")
    print("  Inputs:")
    for key, value in save_node['inputs'].items():
        print(f"    {key}: {value}")
    
    print("\n🎯 DIAGNOSTIC:")
    print("  Le VAEDecode échoue car il reçoit un type invalide")
    print("  Solution: Identifier la sortie correcte du QwenImageSamplerNode")
    
    return workflow

if __name__ == "__main__":
    workflow = inspect_workflow()