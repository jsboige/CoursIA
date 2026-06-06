#!/usr/bin/env python3
"""
Script de validation post-correction pour ComfyUI Qwen
Teste l'accès web, API et GPU après corrections structurelles
"""

import requests
import json
import time
import sys
from pathlib import Path

def test_web_interface():
    """Teste l'accès à l'interface web ComfyUI"""
    print("🌐 Test de l'interface web ComfyUI...")
    
    try:
        response = requests.get("http://localhost:8188/", timeout=10)
        
        if response.status_code == 200:
            print("✅ Interface web accessible (HTTP 200)")
            print(f"   Content-Type: {response.headers.get('content-type', 'N/A')}")
            print(f"   Content-Length: {len(response.content)} octets")
            return True
        else:
            print(f"❌ Interface web inaccessible (HTTP {response.status_code})")
            print(f"   Message: {response.text}")
            return False
            
    except requests.exceptions.ConnectionError as e:
        print(f"❌ Erreur de connexion: {str(e)}")
        return False
    except requests.exceptions.Timeout:
        print("❌ Timeout: l'interface ne répond pas dans les 10 secondes")
        return False
    except Exception as e:
        print(f"❌ Erreur inattendue: {str(e)}")
        return False

def test_api_endpoints():
    """Teste les endpoints API critiques"""
    print("\n🔌 Test des endpoints API...")
    
    endpoints = [
        ("/system_stats", "Statistiques système"),
        ("/object_info", "Informations objets"),
        ("/prompt", "Génération prompt"),
        ("/queue", "File d'attente")
    ]
    
    success_count = 0
    
    for endpoint, description in endpoints:
        try:
            url = f"http://localhost:8188{endpoint}"
            response = requests.get(url, timeout=5)
            
            if response.status_code == 200:
                print(f"✅ {description}: OK (200)")
                success_count += 1
            elif response.status_code == 401:
                print(f"❌ {description}: Erreur 401 (authentification)")
            else:
                print(f"❌ {description}: Erreur {response.status_code}")
                
        except requests.exceptions.ConnectionError:
            print(f"❌ {description}: Erreur de connexion")
        except requests.exceptions.Timeout:
            print(f"❌ {description}: Timeout")
        except Exception as e:
            print(f"❌ {description}: Erreur {str(e)}")
    
    print(f"\n📊 Résultats API: {success_count}/{len(endpoints)} endpoints fonctionnels")
    return success_count == len(endpoints)

def test_gpu_access():
    """Teste l'accès GPU via l'API"""
    print("\n🎮 Test d'accès GPU...")
    
    try:
        response = requests.get("http://localhost:8188/system_stats", timeout=10)
        
        if response.status_code == 200:
            try:
                data = response.json()
                
                # Vérifier les informations GPU
                if "device" in data:
                    print("✅ GPU détecté via API")
                    print(f"   Device: {data.get('device', 'N/A')}")
                    return True
                else:
                    print("⚠️ GPU non détecté dans les stats système")
                    return False
                    
            except json.JSONDecodeError:
                print("❌ Réponse API non-JSON valide")
                return False
                
        else:
            print(f"❌ Impossible d'accéder aux stats système (HTTP {response.status_code})")
            return False
            
    except Exception as e:
        print(f"❌ Erreur lors du test GPU: {str(e)}")
        return False

def test_comfyui_login():
    """Teste spécifiquement ComfyUI-Login"""
    print("\n🔐 Test de ComfyUI-Login...")
    
    try:
        # Test du login avec les identifiants du .env
        login_data = {
            "username": "admin",
            "password": "rZDS3XQa/8!v9L"
        }
        
        response = requests.post(
            "http://localhost:8188/login",
            json=login_data,
            timeout=10,
            headers={"Content-Type": "application/json"}
        )
        
        if response.status_code == 200:
            print("✅ Login ComfyUI-Login réussi")
            try:
                token_data = response.json()
                if "access_token" in token_data:
                    print("✅ Token d'accès obtenu")
                    return True
                else:
                    print("⚠️ Login réussi mais pas de token")
                    return False
            except json.JSONDecodeError:
                print("⚠️ Login réussi mais réponse non-JSON")
                return False
                
        elif response.status_code == 401:
            print("❌ Login ComfyUI-Login échoué (401)")
            print("   Vérifier les identifiants dans le .env")
            return False
        else:
            print(f"❌ Login ComfyUI-Login erreur {response.status_code}")
            print(f"   Response: {response.text}")
            return False
            
    except requests.exceptions.ConnectionError:
        print("❌ ComfyUI-Login inaccessible (connexion refusée)")
        return False
    except Exception as e:
        print(f"❌ Erreur test ComfyUI-Login: {str(e)}")
        return False

def main():
    print("🔧 Validation Post-Correction ComfyUI Qwen")
    print("=" * 50)
    
    # Attendre un peu que le conteneur soit complètement démarré
    print("⏳ Attente du démarrage complet du conteneur...")
    time.sleep(10)
    
    # Tests de validation
    web_ok = test_web_interface()
    api_ok = test_api_endpoints()
    gpu_ok = test_gpu_access()
    login_ok = test_comfyui_login()
    
    # Résumé des résultats
    print("\n📋 RÉSUMÉ DE VALIDATION")
    print("=" * 30)
    
    results = [
        ("Interface Web", web_ok),
        ("API Endpoints", api_ok),
        ("Accès GPU", gpu_ok),
        ("ComfyUI-Login", login_ok)
    ]
    
    success_count = 0
    for test_name, success in results:
        status = "✅ SUCCÈS" if success else "❌ ÉCHEC"
        print(f"{test_name:<15} : {status}")
        if success:
            success_count += 1
    
    print("=" * 30)
    print(f"📊 Taux de réussite: {success_count}/{len(results)} ({success_count/len(results)*100:.1f}%)")
    
    # Évaluation globale
    if success_count == len(results):
        print("\n🎉 SYSTÈME FONCTIONNEL - Corrections réussies !")
        print("   ✅ Tous les composants opérationnels")
        print("   ✅ Prêt pour les tests de génération")
        return True
    elif success_count >= 3:
        print("\n⚠️ SYSTÈME PARTIEL - Corrections partielles")
        print("   ✅ Infrastructure de base fonctionnelle")
        print("   ❌ Quelques composants nécessitent attention")
        return False
    else:
        print("\n❌ SYSTÈME DÉFAILLANT - Corrections insuffisantes")
        print("   ❌ Problèmes structurels persistants")
        print("   ❌ Nouvelle intervention requise")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)