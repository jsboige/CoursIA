#!/usr/bin/env python3
"""
Script de test pour valider le chargement des modèles Qwen - exécuté dans le conteneur Docker
"""

import requests
import json
import sys
import subprocess

def test_qwen_models():
    """Test si les modèles Qwen sont accessibles via l'API ComfyUI"""
    
    # URL de base de l'API ComfyUI
    base_url = "http://localhost:8188"
    
    print("🔍 Test d'accès à l'API ComfyUI...")
    
    # Test 1: Vérifier l'état du système
    try:
        response = requests.get(f"{base_url}/system_stats", timeout=10)
        if response.status_code == 200:
            print("✅ API ComfyUI accessible")
            print(f"📊 Stats: {response.json()}")
        else:
            print(f"❌ Erreur API system_stats: {response.status_code}")
            return False
    except Exception as e:
        print(f"❌ Erreur connexion API: {e}")
        return False
    
    # Test 2: Lister les modèles disponibles
    try:
        response = requests.get(f"{base_url}/object_info", timeout=10)
        if response.status_code == 200:
            models_info = response.json()
            print("📋 Modèles disponibles:")
            
            # Chercher les modèles Qwen
            qwen_models = []
            for model_name, model_info in models_info.items():
                if "qwen" in model_name.lower():
                    qwen_models.append((model_name, model_info))
                    print(f"  - {model_name}: {model_info}")
            
            if qwen_models:
                print(f"✅ {len(qwen_models)} modèle(s) Qwen trouvé(s)")
            else:
                print("❌ Aucun modèle Qwen trouvé dans l'API")
                
        else:
            print(f"❌ Erreur API object_info: {response.status_code}")
            return False
    except Exception as e:
        print(f"❌ Erreur récupération modèles: {e}")
        return False
    
    # Test 3: Vérifier les nodes Qwen
    try:
        response = requests.get(f"{base_url}/object_info", timeout=10)
        if response.status_code == 200:
            nodes_info = response.json()
            print("🔧 Nodes Qwen disponibles:")
            
            qwen_nodes = []
            for node_name, node_info in nodes_info.items():
                if "qwen" in node_name.lower():
                    qwen_nodes.append((node_name, node_info))
                    print(f"  - {node_name}: {node_info}")
            
            if qwen_nodes:
                print(f"✅ {len(qwen_nodes)} node(s) Qwen trouvé(s)")
            else:
                print("❌ Aucun node Qwen trouvé dans l'API")
                
        else:
            print(f"❌ Erreur API nodes: {response.status_code}")
            return False
    except Exception as e:
        print(f"❌ Erreur récupération nodes: {e}")
        return False

if __name__ == "__main__":
    print("🚀 Démarrage du test de validation des modèles Qwen...")
    success = test_qwen_models()
    
    if success:
        print("✅ Test terminé avec succès")
        sys.exit(0)
    else:
        print("❌ Test échoué")
        sys.exit(1)