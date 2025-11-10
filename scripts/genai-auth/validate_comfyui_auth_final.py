#!/usr/bin/env python3
"""
Script de validation finale de l'authentification ComfyUI
Confirme que l'interface web et l'API sont bien protégées
"""

import sys
import requests
import json
from datetime import datetime

def test_web_auth():
    """Teste l'authentification sur l'interface web principale"""
    print("🌐 Test de l'authentification web...")
    
    try:
        response = requests.get("http://localhost:8188/", timeout=10)
        
        if response.status_code == 401:
            print("✅ Interface web PROTÉGÉE (401 Unauthorized)")
            return True
        elif response.status_code == 200:
            if "login" in response.text.lower() or "auth" in response.text.lower():
                print("✅ Interface web PROTÉGÉE (page de login détectée)")
                return True
            else:
                print("❌ Interface web NON PROTÉGÉE (accès direct)")
                return False
        else:
            print(f"⚠️ Réponse inattendue: {response.status_code}")
            return None
            
    except Exception as e:
        print(f"❌ Erreur test web: {e}")
        return False

def test_api_auth():
    """Teste l'authentification sur les endpoints API"""
    print("🔌 Test de l'authentification API...")
    
    try:
        # Test de l'endpoint /prompt
        response = requests.post(
            "http://localhost:8188/prompt",
            json={"prompt": {}},
            headers={"Content-Type": "application/json"},
            timeout=10
        )
        
        if response.status_code == 401:
            print("✅ API PROTÉGÉE (401 Unauthorized sur /prompt)")
            return True
        elif response.status_code == 200:
            print("❌ API NON PROTÉGÉE (accès sans authentification)")
            return False
        else:
            print(f"⚠️ Réponse API inattendue: {response.status_code}")
            return None
            
    except Exception as e:
        print(f"❌ Erreur test API: {e}")
        return False

def test_server_connectivity():
    """Teste la connectivité générale du serveur"""
    print("🔗 Test de connectivité serveur...")
    
    try:
        response = requests.get("http://localhost:8188/system_stats", timeout=5)
        
        if response.status_code == 200:
            print("✅ Serveur ComfyUI accessible")
            return True
        else:
            print(f"⚠️ Serveur répond avec: {response.status_code}")
            return False
            
    except Exception as e:
        print(f"❌ Erreur connectivité: {e}")
        return False

def generate_report(web_auth, api_auth, connectivity):
    """Génère un rapport de validation"""
    print("\n" + "="*60)
    print("📊 RAPPORT DE VALIDATION D'AUTHENTIFICATION COMFYUI")
    print("="*60)
    
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"📅 Date/Heure: {timestamp}")
    
    print(f"\n🔍 RÉSULTATS DES TESTS:")
    print(f"  • Connectivité serveur: {'✅' if connectivity else '❌'}")
    print(f"  • Authentification web: {'✅' if web_auth else '❌'}")
    print(f"  • Authentification API: {'✅' if api_auth else '❌'}")
    
    # Évaluation globale
    if connectivity and web_auth and api_auth:
        status = "🎉 SUCCÈS COMPLET"
        message = "L'authentification ComfyUI est fonctionnelle sur tous les fronts"
        print(f"\n{status}")
        print(f"✨ {message}")
        
        # Recommandations
        print(f"\n📋 RECOMMANDATIONS:")
        print("  • L'interface web est maintenant protégée")
        print("  • Les endpoints API nécessitent une authentification")
        print("  • ComfyUI-Login est correctement installé et configuré")
        print("  • Le système est prêt pour une utilisation sécurisée")
        
        return True
    else:
        status = "⚠️ VALIDATION PARTIELLE"
        print(f"\n{status}")
        
        if not connectivity:
            print("  • Le serveur ComfyUI n'est pas accessible")
        if not web_auth:
            print("  • L'interface web n'est pas protégée")
        if not api_auth:
            print("  • Les endpoints API ne sont pas protégés")
            
        return False

def save_report(validation_success):
    """Sauvegarde le rapport de validation"""
    report = {
        "timestamp": datetime.now().isoformat(),
        "validation_success": validation_success,
        "tests_performed": ["connectivity", "web_auth", "api_auth"],
        "comfyui_url": "http://localhost:8188",
        "comfyui_container": "comfyui-qwen"
    }
    
    try:
        with open("scripts/genai-auth/validation_auth_report.json", "w") as f:
            json.dump(report, f, indent=2)
        print(f"\n💾 Rapport sauvegardé: scripts/genai-auth/validation_auth_report.json")
    except Exception as e:
        print(f"❌ Erreur sauvegarde rapport: {e}")

def main():
    """Point d'entrée principal"""
    print("🚀 VALIDATION FINALE D'AUTHENTIFICATION COMFYUI")
    print("="*60)
    
    # Tests de validation
    connectivity = test_server_connectivity()
    web_auth = test_web_auth()
    api_auth = test_api_auth()
    
    # Génération du rapport
    validation_success = generate_report(web_auth, api_auth, connectivity)
    
    # Sauvegarde du rapport
    save_report(validation_success)
    
    # Code de sortie
    sys.exit(0 if validation_success else 1)

if __name__ == "__main__":
    main()