#!/usr/bin/env python3
"""
Script de test d'authentification ComfyUI Qwen - Phase 29
Utilise les scripts d'authentification existants pour diagnostiquer les problèmes

Date: 2025-11-13
Objectif: Analyser et utiliser les scripts d'authentification existants
"""

import sys
import os
import json
import requests
from pathlib import Path
from datetime import datetime

# Ajouter le chemin des scripts d'authentification
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent / "scripts" / "genai-auth" / "utils"))

try:
    from token_manager import TokenManager
    from genai_auth_manager import GenAIAuthManager
    from comfyui_client_helper import ComfyUIConfig, ComfyUIClient
except ImportError as e:
    print(f"❌ Erreur import scripts auth: {e}")
    sys.exit(1)

def test_token_manager():
    """Test le TokenManager existant"""
    print("🔧 Test TokenManager...")
    
    try:
        tm = TokenManager()
        
        # Validation des tokens
        print("  📋 Validation des tokens...")
        if tm.validate_tokens():
            print("  ✅ Tokens valides")
        else:
            print("  ❌ Tokens invalides")
            return False
        
        # Récupération du hash
        print("  🔑 Récupération du hash bcrypt...")
        hash_token = tm.get_bcrypt_hash()
        print(f"  ✅ Hash: {hash_token[:30]}...")
        
        # Récupération du token brut
        print("  🔓 Récupération du token brut...")
        raw_token = tm.get_raw_token()
        print(f"  ✅ Token brut: {raw_token[:15]}...")
        
        # Génération des headers
        print("  📝 Génération des headers...")
        headers = tm.get_auth_headers()
        print(f"  ✅ Headers: {headers}")
        
        return True
        
    except Exception as e:
        print(f"  ❌ Erreur TokenManager: {e}")
        return False

def test_genai_auth_manager():
    """Test le GenAIAuthManager existant"""
    print("\n🔧 Test GenAIAuthManager...")
    
    try:
        manager = GenAIAuthManager()
        
        # Validation des tokens
        print("  📋 Validation tokens ComfyUI Qwen...")
        validation = manager.validate_tokens("comfyui-qwen")
        print(f"  📊 Résultat validation: {json.dumps(validation, indent=4)}")
        
        # Diagnostic des problèmes
        print("  🔍 Diagnostic authentification...")
        diagnostic = manager.diagnose_auth_issues("comfyui-qwen")
        print(f"  📊 Résultat diagnostic: {json.dumps(diagnostic, indent=4)}")
        
        return validation.get("token_exists", False) and len(diagnostic.get("issues", [])) == 0
        
    except Exception as e:
        print(f"  ❌ Erreur GenAIAuthManager: {e}")
        return False

def test_comfyui_client():
    """Test le client ComfyUI avec authentification"""
    print("\n🔧 Test ComfyUI Client...")
    
    try:
        # Utiliser le TokenManager pour obtenir le hash
        tm = TokenManager()
        hash_token = tm.get_bcrypt_hash()
        
        # Configuration du client
        config = ComfyUIConfig(
            host="localhost",
            port=8188,
            protocol="http",
            api_key=hash_token,
            timeout=30
        )
        
        # Création du client
        client = ComfyUIClient(config)
        
        # Test de connectivité
        print("  🌐 Test connectivité...")
        if client.test_connectivity():
            print("  ✅ Connectivité OK")
            
            # Test des infos système
            print("  📊 Test infos système...")
            system_info = client.get_system_stats()
            if system_info:
                print(f"  ✅ Infos système récupérées: {len(system_info)} champs")
            else:
                print("  ❌ Impossible récupérer les infos système")
                return False
            
            # Test des objets/nodes
            print("  🧩 Test objets/nodes...")
            object_info = client.get_object_info()
            if object_info:
                print(f"  ✅ Objets récupérés: {len(object_info)} nodes")
                
                # Compter les nodes Qwen
                qwen_nodes = [name for name in object_info.keys() if 'qwen' in name.lower()]
                print(f"  🎯 Nodes Qwen détectés: {len(qwen_nodes)}")
                
                if qwen_nodes:
                    print("  📋 Liste des nodes Qwen:")
                    for node in sorted(qwen_nodes)[:10]:  # Limiter à 10 pour la lisibilité
                        print(f"    - {node}")
                    if len(qwen_nodes) > 10:
                        print(f"    ... et {len(qwen_nodes) - 10} autres")
                else:
                    print("  ⚠️ Aucun node Qwen détecté")
            else:
                print("  ❌ Impossible récupérer les objets/nodes")
                return False
            
            return True
        else:
            print("  ❌ Échec connectivité")
            return False
            
    except Exception as e:
        print(f"  ❌ Erreur client ComfyUI: {e}")
        return False

def test_direct_api():
    """Test direct de l'API avec différents tokens"""
    print("\n🔧 Test API Direct...")
    
    try:
        # Test avec le hash bcrypt (méthode correcte selon README)
        print("  🔑 Test avec hash bcrypt...")
        tm = TokenManager()
        hash_token = tm.get_bcrypt_hash()
        
        response = requests.get(
            "http://localhost:8188/system_stats",
            headers={"Authorization": f"Bearer {hash_token}"},
            timeout=10
        )
        print(f"  📊 Status hash bcrypt: {response.status_code}")
        if response.status_code == 200:
            print("  ✅ Authentification réussie avec hash bcrypt!")
            return True
        else:
            print(f"  ❌ Échec: {response.text[:200]}")
        
        # Test avec le token brut (pour comparaison)
        print("  🔓 Test avec token brut...")
        raw_token = tm.get_raw_token()
        
        response = requests.get(
            "http://localhost:8188/system_stats",
            headers={"Authorization": f"Bearer {raw_token}"},
            timeout=10
        )
        print(f"  📊 Status token brut: {response.status_code}")
        if response.status_code == 200:
            print("  ✅ Authentification réussie avec token brut!")
            return True
        else:
            print(f"  ❌ Échec: {response.text[:200]}")
        
        # Test sans authentification
        print("  🌐 Test sans authentification...")
        response = requests.get(
            "http://localhost:8188/system_stats",
            timeout=10
        )
        print(f"  📊 Status sans auth: {response.status_code}")
        if response.status_code == 200:
            print("  ⚠️ Accès sans authentification possible!")
        else:
            print(f"  ❌ Échec: {response.text[:200]}")
        
        return False
        
    except Exception as e:
        print(f"  ❌ Erreur test API direct: {e}")
        return False

def main():
    """Fonction principale"""
    print("╔═══════════════════════════════════════════════════════╗")
    print("║  TEST D'AUTHENTIFICATION COMFYUI QWEN - SCRIPTS EXISTANTS ║")
    print("║                    Phase 29 - Analyse               ║")
    print("╚═══════════════════════════════════════════════════════╝")
    print(f"📅 Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    results = {
        "timestamp": datetime.now().isoformat(),
        "tests": {}
    }
    
    # Test 1: TokenManager
    results["tests"]["token_manager"] = test_token_manager()
    
    # Test 2: GenAIAuthManager
    results["tests"]["genai_auth_manager"] = test_genai_auth_manager()
    
    # Test 3: ComfyUI Client
    results["tests"]["comfyui_client"] = test_comfyui_client()
    
    # Test 4: API Direct
    results["tests"]["direct_api"] = test_direct_api()
    
    # Résultat global
    print("\n" + "="*60)
    print("📊 RÉSULTATS GLOBAUX")
    print("="*60)
    
    success_count = sum(1 for result in results["tests"].values() if result)
    total_tests = len(results["tests"])
    
    for test_name, test_result in results["tests"].items():
        status = "✅ SUCCÈS" if test_result else "❌ ÉCHEC"
        print(f"  {test_name}: {status}")
    
    print(f"\n📈 Score: {success_count}/{total_tests} tests réussis")
    
    if success_count == total_tests:
        print("🎉 TOUS LES TESTS RÉUSSIS - Authentification fonctionnelle!")
        return 0
    elif success_count > 0:
        print("⚠️ CERTAINS TESTS RÉUSSIS - Authentification partielle!")
        return 1
    else:
        print("❌ TOUS LES TESTS ÉCHOUÉS - Authentification en échec!")
        return 2

if __name__ == "__main__":
    sys.exit(main())