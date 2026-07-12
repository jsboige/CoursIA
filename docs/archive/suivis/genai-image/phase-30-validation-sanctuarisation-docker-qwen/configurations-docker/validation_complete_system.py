#!/usr/bin/env python3
"""
Script de validation complète du système ComfyUI Qwen
Test exhaustif de l'interface web, API, conteneur et GPU
"""

import requests
import json
import time
import sys
import os
from datetime import datetime

# Configuration
COMFYUI_URL = "http://localhost:8188"
USERNAME = "admin"
PASSWORD = "rZDS3XQa/8!v9L"
BEARER_TOKEN = "$2b$12$NErya5UooY9bJnscVc/ec.hpVDX.nYM86/88bXIkF/hh2VeKRvU5ka"

class Colors:
    """Codes couleurs pour le terminal"""
    GREEN = '\033[92m'
    RED = '\033[91m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    BOLD = '\033[1m'
    END = '\033[0m'

def print_status(test_name, status, details=""):
    """Affiche le statut d'un test avec couleur"""
    if status == "SUCCESS":
        color = Colors.GREEN
        symbol = "✅"
    elif status == "FAILED":
        color = Colors.RED
        symbol = "❌"
    elif status == "WARNING":
        color = Colors.YELLOW
        symbol = "⚠️"
    else:
        color = Colors.BLUE
        symbol = "ℹ️"
    
    print(f"{color}{Colors.BOLD}{symbol} {test_name}{Colors.END}")
    if details:
        print(f"   {details}")

def test_web_interface_access():
    """Test 1: Accès à l'interface web"""
    print(f"\n{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}TEST 1: ACCÈS À L'INTERFACE WEB{Colors.END}")
    print(f"{Colors.BLUE}{'='*60}{Colors.END}")
    
    try:
        response = requests.get(COMFYUI_URL, timeout=10)
        if response.status_code == 200:
            print_status("Accès HTTP", "SUCCESS", f"Status code: {response.status_code}")
            
            # Vérifier si c'est la page de login ou ComfyUI
            if "login" in response.text.lower() or "password" in response.text.lower():
                print_status("Page de login détectée", "SUCCESS", "L'interface redirige vers l'authentification")
                return True
            elif "comfyui" in response.text.lower():
                print_status("Interface ComfyUI accessible", "WARNING", "Possiblement déjà authentifié ou guest mode")
                return True
            else:
                print_status("Contenu de page inattendu", "FAILED", f"Contenu: {response.text[:200]}...")
                return False
        else:
            print_status("Accès HTTP", "FAILED", f"Status code: {response.status_code}")
            return False
    except Exception as e:
        print_status("Accès HTTP", "FAILED", f"Exception: {str(e)}")
        return False

def test_web_login():
    """Test 2: Login via formulaire web"""
    print(f"\n{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}TEST 2: LOGIN VIA FORMULAIRE WEB{Colors.END}")
    print(f"{Colors.BLUE}{'='*60}{Colors.END}")
    
    session = requests.Session()
    
    try:
        # Premier accès pour obtenir les cookies
        response = session.get(COMFYUI_URL, timeout=10)
        
        # Tentative de login avec form-data
        login_data = {
            'username': USERNAME,
            'password': PASSWORD
        }
        
        response = session.post(
            COMFYUI_URL + "/login",
            data=login_data,
            headers={'Content-Type': 'application/x-www-form-urlencoded'},
            timeout=10,
            allow_redirects=False
        )
        
        if response.status_code in [302, 303]:
            print_status("Login web", "SUCCESS", f"Redirection (status {response.status_code})")
            
            # Suivre la redirection pour vérifier l'accès
            location = response.headers.get('Location', '')
            if location:
                redirect_response = session.get(COMFYUI_URL + location, timeout=10)
                if redirect_response.status_code == 200:
                    if "comfyui" in redirect_response.text.lower():
                        print_status("Interface ComfyUI après login", "SUCCESS", "Interface chargée avec succès")
                        return session
                    else:
                        print_status("Contenu après login", "WARNING", "Réponse inattendue après redirection")
                else:
                    print_status("Accès après redirection", "FAILED", f"Status: {redirect_response.status_code}")
            else:
                print_status("Redirection", "WARNING", "Pas de header Location trouvé")
                return session
                
        elif response.status_code == 200:
            if "invalid" in response.text.lower() or "error" in response.text.lower():
                print_status("Login web", "FAILED", "Identifiants invalides")
            else:
                print_status("Login web", "SUCCESS", "Login direct réussi")
                return session
        else:
            print_status("Login web", "FAILED", f"Status code: {response.status_code}")
            print(f"Response: {response.text[:500]}...")
            
    except Exception as e:
        print_status("Login web", "FAILED", f"Exception: {str(e)}")
    
    return None

def test_api_authentication():
    """Test 3: Authentification API"""
    print(f"\n{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}TEST 3: AUTHENTIFICATION API{Colors.END}")
    print(f"{Colors.BLUE}{'='*60}{Colors.END}")
    
    headers = {
        'Authorization': f'Bearer {BEARER_TOKEN}',
        'Content-Type': 'application/json'
    }
    
    # Test endpoint system_stats
    try:
        response = requests.get(
            COMFYUI_URL + "/system_stats",
            headers=headers,
            timeout=10
        )
        
        if response.status_code == 200:
            try:
                data = response.json()
                print_status("API system_stats", "SUCCESS", f"Retourne des données JSON valides")
                print(f"   Données: {json.dumps(data, indent=2)[:300]}...")
                return True
            except json.JSONDecodeError:
                print_status("API system_stats", "FAILED", "Réponse non-JSON")
                print(f"   Réponse: {response.text[:300]}...")
                return False
        elif response.status_code == 401:
            print_status("API system_stats", "FAILED", "Erreur 401 - Token non reconnu")
            print(f"   Token utilisé: {BEARER_TOKEN[:50]}...")
            return False
        elif response.status_code == 500:
            print_status("API system_stats", "FAILED", "Erreur 500 - Erreur serveur")
            print(f"   Réponse: {response.text[:300]}...")
            return False
        else:
            print_status("API system_stats", "FAILED", f"Status inattendu: {response.status_code}")
            return False
            
    except Exception as e:
        print_status("API system_stats", "FAILED", f"Exception: {str(e)}")
        return False

def test_api_endpoints():
    """Test 4: Autres endpoints API"""
    print(f"\n{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}TEST 4: AUTRES ENDPOINTS API{Colors.END}")
    print(f"{Colors.BLUE}{'='*60}{Colors.END}")
    
    headers = {
        'Authorization': f'Bearer {BEARER_TOKEN}',
        'Content-Type': 'application/json'
    }
    
    endpoints = [
        "/prompt",
        "/queue",
        "/history",
        "/object_info"
    ]
    
    success_count = 0
    for endpoint in endpoints:
        try:
            response = requests.get(
                COMFYUI_URL + endpoint,
                headers=headers,
                timeout=10
            )
            
            if response.status_code == 200:
                print_status(f"API {endpoint}", "SUCCESS", f"Status: {response.status_code}")
                success_count += 1
            elif response.status_code == 401:
                print_status(f"API {endpoint}", "FAILED", "Erreur 401 - Authentification requise")
            else:
                print_status(f"API {endpoint}", "WARNING", f"Status: {response.status_code}")
                
        except Exception as e:
            print_status(f"API {endpoint}", "FAILED", f"Exception: {str(e)}")
    
    print(f"\n   Endpoints API fonctionnels: {success_count}/{len(endpoints)}")
    return success_count == len(endpoints)

def test_gpu_access():
    """Test 5: Accès GPU via API"""
    print(f"\n{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}TEST 5: VALIDATION GPU{Colors.END}")
    print(f"{Colors.BLUE}{'='*60}{Colors.END}")
    
    headers = {
        'Authorization': f'Bearer {BEARER_TOKEN}',
        'Content-Type': 'application/json'
    }
    
    try:
        response = requests.get(
            COMFYUI_URL + "/system_stats",
            headers=headers,
            timeout=10
        )
        
        if response.status_code == 200:
            data = response.json()
            
            # Vérifier les informations GPU dans les données système
            if 'devices' in data:
                devices = data['devices']
                if devices:
                    device = devices[0]  # Premier GPU
                    if 'name' in device and 'RTX' in device['name']:
                        print_status("Détection GPU RTX", "SUCCESS", f"GPU: {device['name']}")
                    else:
                        print_status("Détection GPU", "WARNING", f"GPU détecté: {device.get('name', 'Inconnu')}")
                    
                    if 'vram_total' in device:
                        vram_gb = device['vram_total'] / (1024**3)
                        print_status("VRAM GPU", "SUCCESS", f"VRAM totale: {vram_gb:.1f} GB")
                    
                    return True
                else:
                    print_status("Détection GPU", "FAILED", "Aucun périphérique GPU détecté")
            else:
                print_status("Informations GPU", "WARNING", "Données GPU non disponibles dans system_stats")
                
        else:
            print_status("Accès infos GPU", "FAILED", f"Status: {response.status_code}")
            
    except Exception as e:
        print_status("Accès infos GPU", "FAILED", f"Exception: {str(e)}")
    
    return False

def test_comfyui_functionality():
    """Test 6: Fonctionnalités ComfyUI"""
    print(f"\n{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}TEST 6: FONCTIONNALITÉS COMFYUI{Colors.END}")
    print(f"{Colors.BLUE}{'='*60}{Colors.END}")
    
    headers = {
        'Authorization': f'Bearer {BEARER_TOKEN}',
        'Content-Type': 'application/json'
    }
    
    # Test 1: Obtenir les informations des objets (nodes disponibles)
    try:
        response = requests.get(
            COMFYUI_URL + "/object_info",
            headers=headers,
            timeout=10
        )
        
        if response.status_code == 200:
            object_info = response.json()
            
            # Vérifier les custom nodes Qwen
            qwen_nodes = [key for key in object_info.keys() if 'qwen' in key.lower()]
            if qwen_nodes:
                print_status("Custom nodes Qwen", "SUCCESS", f"{len(qwen_nodes)} nodes Qwen détectés")
                for node in qwen_nodes[:5]:  # Afficher les 5 premiers
                    print(f"   - {node}")
            else:
                print_status("Custom nodes Qwen", "WARNING", "Aucun node Qwen détecté")
            
            # Vérifier les modèles
            model_count = 0
            for key, value in object_info.items():
                if 'model' in key.lower() or 'checkpoint' in key.lower():
                    model_count += 1
            
            if model_count > 0:
                print_status("Modèles détectés", "SUCCESS", f"{model_count} modèles/checkpoints trouvés")
            else:
                print_status("Modèles détectés", "WARNING", "Aucun modèle détecté")
            
            return True
        else:
            print_status("Informations objets", "FAILED", f"Status: {response.status_code}")
            
    except Exception as e:
        print_status("Informations objets", "FAILED", f"Exception: {str(e)}")
    
    return False

def generate_summary_report(results):
    """Génère le rapport de synthèse"""
    print(f"\n{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}RAPPORT DE VALIDATION FINALE{Colors.END}")
    print(f"{Colors.BLUE}{'='*60}{Colors.END}")
    
    print(f"\n{Colors.BOLD}Date de validation:{Colors.END} {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{Colors.BOLD}URL ComfyUI:{Colors.END} {COMFYUI_URL}")
    
    print(f"\n{Colors.BOLD}RÉSULTATS DES TESTS:{Colors.END}")
    
    test_names = [
        "Accès interface web",
        "Login formulaire web", 
        "Authentification API",
        "Endpoints API",
        "Accès GPU",
        "Fonctionnalités ComfyUI"
    ]
    
    for i, (test_name, result) in enumerate(zip(test_names, results), 1):
        status_icon = "✅" if result else "❌"
        status_text = "SUCCÈS" if result else "ÉCHEC"
        color = Colors.GREEN if result else Colors.RED
        
        print(f"{color}{i}. {test_name}: {status_icon} {status_text}{Colors.END}")
    
    success_count = sum(results)
    total_count = len(results)
    success_rate = (success_count / total_count) * 100
    
    print(f"\n{Colors.BOLD}TAUX DE RÉUSSITE:{Colors.END} {success_count}/{total_count} ({success_rate:.1f}%)")
    
    if success_rate >= 80:
        print(f"\n{Colors.GREEN}{Colors.BOLD}🎯 SYSTÈME PRÊT POUR LA PRODUCTION{Colors.END}")
        print(f"{Colors.GREEN}Le système ComfyUI Qwen est fonctionnel et peut être utilisé pour la génération d'images.{Colors.END}")
    elif success_rate >= 60:
        print(f"\n{Colors.YELLOW}{Colors.BOLD}⚠️ SYSTÈME PARTIELLEMENT FONCTIONNEL{Colors.END}")
        print(f"{Colors.YELLOW}Des ajustements sont nécessaires avant la production.{Colors.END}")
    else:
        print(f"\n{Colors.RED}{Colors.BOLD}❌ SYSTÈME NON FONCTIONNEL{Colors.END}")
        print(f"{Colors.RED}Des corrections critiques sont requises.{Colors.END}")
    
    return success_rate >= 80

def main():
    """Fonction principale de validation"""
    print(f"{Colors.BOLD}{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}VALIDATION COMPLÈTE DU SYSTÈME COMFYUI QWEN{Colors.END}")
    print(f"{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}Début:{Colors.END} {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    
    # Exécuter tous les tests
    results = []
    
    # Test 1: Accès web
    results.append(test_web_interface_access())
    
    # Test 2: Login web
    session = test_web_login()
    results.append(session is not None)
    
    # Test 3: Authentification API
    results.append(test_api_authentication())
    
    # Test 4: Autres endpoints API
    results.append(test_api_endpoints())
    
    # Test 5: Accès GPU
    results.append(test_gpu_access())
    
    # Test 6: Fonctionnalités ComfyUI
    results.append(test_comfyui_functionality())
    
    # Générer le rapport final
    is_ready = generate_summary_report(results)
    
    return 0 if is_ready else 1

if __name__ == "__main__":
    sys.exit(main())