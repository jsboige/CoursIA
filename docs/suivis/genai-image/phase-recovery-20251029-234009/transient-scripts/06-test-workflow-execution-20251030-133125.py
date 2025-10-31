#!/usr/bin/env python3
"""
Script de test d'exécution du workflow Qwen avec ComfyUI
Phase de validation finale - Test d'intégration complète
"""

import json
import sys
import os
from datetime import datetime

# Ajout du chemin racine pour les imports
sys.path.insert(0, 'd:/Dev/CoursIA')

try:
    from scripts.genai_auth.comfyui_client_helper import ComfyUIClient, ComfyUIConfig
except ImportError as e:
    print(f"❌ Erreur d'import: {e}")
    print("🔍 Vérification des chemins d'import:")
    print(f"   sys.path[0]: {sys.path[0]}")
    print(f"   Répertoire courant: {os.getcwd()}")
    sys.exit(1)

def test_workflow_execution():
    """Teste l'exécution complète du workflow Qwen"""
    
    print("🧪 TEST D'EXÉCUTION WORKFLOW QWEN")
    print("=" * 50)
    print(f"⏰ Heure de début: {datetime.now().isoformat()}")
    
    # Configuration du client ComfyUI
    config = ComfyUIConfig(
        host="localhost", 
        port=8188, 
        protocol="http"
    )
    client = ComfyUIClient(config)
    
    # Chemin du workflow corrigé
    workflow_path = "d:/Dev/CoursIA/temp_official_workflow_qwen_t2i_fixed.json"
    
    print(f"📂 Fichier workflow: {workflow_path}")
    
    # Vérification de l'existence du fichier
    if not os.path.exists(workflow_path):
        print(f"❌ Fichier workflow introuvable: {workflow_path}")
        return False
    
    try:
        # Chargement du workflow
        print("📥 Chargement du workflow...")
        workflow = client.load_workflow(workflow_path)
        print("✅ Workflow chargé avec succès")
        
        # Validation basique du workflow
        if not isinstance(workflow, dict):
            print("❌ Format de workflow invalide")
            return False
            
        print(f"📊 Nombre de nodes: {len(workflow.get('nodes', []))}")
        
        # Test de connexion à l'API ComfyUI
        print("🔗 Test de connexion à l'API ComfyUI...")
        try:
            # Tentative de récupération des infos système
            system_info = client.get_system_info()
            print("✅ Connexion API réussie")
            print(f"📋 Infos système: {system_info}")
        except Exception as api_error:
            print(f"❌ Erreur de connexion API: {api_error}")
            print("💡 Vérifiez que ComfyUI est démarré sur localhost:8188")
            return False
        
        # Exécution du workflow
        print("🚀 Lancement de l'exécution du workflow...")
        result = client.submit_workflow(workflow)
        
        if result:
            print("✅ Workflow exécuté avec succès")
            print(f"📤 Résultat: {result}")
            return True
        else:
            print("❌ Échec de l'exécution du workflow")
            return False
            
    except Exception as e:
        print(f"❌ Erreur lors de l'exécution: {e}")
        return False

def main():
    """Point d'entrée principal"""
    print("🎯 SCRIPT DE TEST WORKFLOW QWEN - VALIDATION FINALE")
    print(f"📅 Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    success = test_workflow_execution()
    
    print()
    print("📊 RÉSULTAT DU TEST:")
    if success:
        print("✅ SUCCÈS - Le workflow Qwen fonctionne correctement")
        print("🎯 Système prêt pour la production")
    else:
        print("❌ ÉCHEC - Problèmes détectés dans l'exécution")
        print("🔧 Actions correctives nécessaires")
    
    print(f"⏰ Heure de fin: {datetime.now().isoformat()}")
    return 0 if success else 1

if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)