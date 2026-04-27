#!/usr/bin/env python3
"""
Script de diagnostic complet pour l'authentification ComfyUI
Utilise les utilitaires consolidés pour analyser et corriger les problèmes d'authentification
"""

import sys
import os
import subprocess
import json
import time
from pathlib import Path

# Ajout du chemin des utilitaires
sys.path.append(str(Path(__file__).parent.parent / "utils"))

try:
    from docker_qwen_manager import DockerQwenManager
    from diagnostic_utils import DiagnosticUtils
    from comfyui_client_helper import ComfyUIClient, ComfyUIConfig
except ImportError as e:
    print(f"ERREUR: Impossible d'importer les utilitaires: {e}")
    sys.exit(1)

class ComfyUIAuthDiagnostic:
    def __init__(self):
        self.docker_manager = DockerQwenManager()
        self.diagnostic_utils = DiagnosticUtils()
        # Configuration par défaut pour ComfyUI
        config = ComfyUIConfig(
            host="localhost",
            port=8188,
            protocol="http",
            timeout=30
        )
        self.client = ComfyUIClient(config)
        
    def check_container_status(self):
        """Vérifie le statut du conteneur ComfyUI"""
        print("🔍 Vérification du statut du conteneur...")
        
        try:
            result = subprocess.run(
                ["docker", "ps", "--filter", "name=comfyui-qwen", "--format", "json"],
                capture_output=True, text=True
            )
            
            if result.returncode == 0 and result.stdout.strip():
                containers = json.loads(result.stdout)
                if containers:
                    container = containers[0]
                    status = container.get("State", "Unknown")
                    print(f"✅ Conteneur trouvé - Statut: {status}")
                    return True, status
                else:
                    print("❌ Conteneur comfyui-qwen non trouvé")
                    return False, "Not found"
            else:
                print("❌ Erreur lors de la vérification du conteneur")
                return False, "Error"
        except Exception as e:
            print(f"❌ Exception lors de la vérification: {e}")
            return False, "Exception"
    
    def check_comfyui_login_installation(self):
        """Vérifie l'installation de ComfyUI-Login"""
        print("\n🔍 Vérification de ComfyUI-Login...")
        
        try:
            # Vérification dans le conteneur
            cmd = "docker exec comfyui-qwen find /workspace/ComfyUI/custom_nodes -name '*login*' -type d"
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
            
            if result.returncode == 0 and result.stdout.strip():
                print("✅ ComfyUI-Login trouvé dans custom_nodes")
                print(f"📍 Chemin: {result.stdout.strip()}")
                return True
            else:
                print("❌ ComfyUI-Login non trouvé dans custom_nodes")
                return False
        except Exception as e:
            print(f"❌ Erreur lors de la vérification: {e}")
            return False
    
    def check_dependencies(self):
        """Vérifie les dépendances Python requises"""
        print("\n🔍 Vérification des dépendances Python...")
        
        required_deps = [
            "pycryptodome",
            "aiohttp-session", 
            "cryptography"
        ]
        
        missing_deps = []
        
        for dep in required_deps:
            try:
                cmd = f"docker exec comfyui-qwen python -c \"import {dep.replace('-', '_')}\""
                result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
                
                if result.returncode == 0:
                    print(f"✅ {dep} - OK")
                else:
                    print(f"❌ {dep} - MANQUANT")
                    missing_deps.append(dep)
            except Exception as e:
                print(f"❌ Erreur vérification {dep}: {e}")
                missing_deps.append(dep)
        
        return missing_deps
    
    def check_startup_arguments(self):
        """Vérifie les arguments de démarrage"""
        print("\n🔍 Vérification des arguments de démarrage...")
        
        try:
            # Vérification du docker-compose.yml
            with open("docker-configurations/comfyui-qwen/docker-compose.yml", 'r') as f:
                compose_content = f.read()
                
            if "--enable-cors-header" in compose_content:
                print("✅ --enable-cors-header trouvé dans docker-compose.yml")
                return True
            else:
                print("❌ --enable-cors-header MANQUANT dans docker-compose.yml")
                return False
        except Exception as e:
            print(f"❌ Erreur lecture docker-compose.yml: {e}")
            return False
    
    def check_web_auth_status(self):
        """Teste l'authentification sur l'interface web"""
        print("\n🔍 Test de l'authentification web...")
        
        try:
            import requests
            
            # Test de l'interface principale
            response = requests.get("http://localhost:8188/", timeout=10)
            
            if response.status_code == 200:
                if "login" in response.text.lower() or "auth" in response.text.lower():
                    print("✅ Interface web protégée (page de login détectée)")
                    return True
                else:
                    print("❌ Interface web NON PROTÉGÉE (pas de page de login)")
                    return False
            else:
                print(f"❌ Erreur HTTP: {response.status_code}")
                return False
                
        except Exception as e:
            print(f"❌ Erreur test web: {e}")
            return False
    
    def check_api_auth_status(self):
        """Teste l'authentification sur les endpoints API"""
        print("\n🔍 Test de l'authentification API...")
        
        try:
            import requests
            
            # Test de l'endpoint /prompt
            response = requests.post(
                "http://localhost:8188/prompt",
                json={"prompt": {}},
                timeout=10
            )
            
            if response.status_code == 401 or response.status_code == 403:
                print("✅ API protégée (authentification requise)")
                return True
            elif response.status_code == 200:
                print("❌ API NON PROTÉGÉE (accès sans authentification)")
                return False
            else:
                print(f"⚠️ Réponse inattendue: {response.status_code}")
                return None
                
        except Exception as e:
            print(f"❌ Erreur test API: {e}")
            return False
    
    def get_recent_logs(self, lines=50):
        """Récupère les logs récents du conteneur"""
        print(f"\n🔍 Récupération des {lines} dernières lignes de logs...")
        
        try:
            result = subprocess.run(
                ["docker", "logs", "comfyui-qwen", "--tail", str(lines)],
                capture_output=True, text=True
            )
            
            if result.returncode == 0:
                return result.stdout
            else:
                print(f"❌ Erreur récupération logs: {result.stderr}")
                return None
        except Exception as e:
            print(f"❌ Exception logs: {e}")
            return None
    
    def analyze_logs_for_errors(self, logs):
        """Analyse les logs à la recherche d'erreurs"""
        if not logs:
            return []
        
        error_patterns = [
            "ImportError",
            "ModuleNotFoundError", 
            "Error loading custom node",
            "Failed to load",
            "Exception"
        ]
        
        errors = []
        lines = logs.split('\n')
        
        for i, line in enumerate(lines):
            for pattern in error_patterns:
                if pattern in line:
                    errors.append({
                        'line': i + 1,
                        'pattern': pattern,
                        'content': line.strip()
                    })
        
        return errors
    
    def fix_missing_dependencies(self, missing_deps):
        """Corrige les dépendances manquantes"""
        if not missing_deps:
            return True
            
        print(f"\n🔧 Correction des dépendances manquantes: {missing_deps}")
        
        try:
            # Ajout au requirements.txt dans le conteneur
            for dep in missing_deps:
                cmd = f"docker exec comfyui-qwen sh -c \"echo '{dep}' >> /workspace/ComfyUI/requirements.txt\""
                result = subprocess.run(cmd, shell=True, capture_output=True)
                
                if result.returncode == 0:
                    print(f"✅ {dep} ajouté à requirements.txt")
                else:
                    print(f"❌ Erreur ajout {dep}: {result.stderr}")
                    return False
            
            # Redémarrage du conteneur
            print("🔄 Redémarrage du conteneur pour appliquer les corrections...")
            result = subprocess.run(
                ["docker-compose", "-f", "docker-configurations/comfyui-qwen/docker-compose.yml", "restart"],
                capture_output=True
            )
            
            if result.returncode == 0:
                print("✅ Conteneur redémarré")
                return True
            else:
                print(f"❌ Erreur redémarrage: {result.stderr}")
                return False
                
        except Exception as e:
            print(f"❌ Exception correction: {e}")
            return False
    
    def run_full_diagnostic(self):
        """Exécute le diagnostic complet"""
        print("🚀 DÉMARRAGE DU DIAGNOSTIC COMPLET COMFYUI AUTH\n")
        
        # 1. Vérification du conteneur
        container_ok, status = self.check_container_status()
        if not container_ok:
            print("\n❌ Le conteneur n'est pas en cours d'exécution. Diagnostic arrêté.")
            return False
        
        # 2. Vérification de ComfyUI-Login
        login_installed = self.check_comfyui_login_installation()
        
        # 3. Vérification des arguments de démarrage
        args_ok = self.check_startup_arguments()
        
        # 4. Vérification des dépendances
        missing_deps = self.check_dependencies()
        
        # 5. Correction automatique si nécessaire
        if missing_deps:
            if not self.fix_missing_dependencies(missing_deps):
                print("\n❌ Échec de la correction des dépendances")
                return False
            
            print("⏳ Attente de 30s pour le redémarrage...")
            time.sleep(30)
        
        # 6. Analyse des logs
        logs = self.get_recent_logs()
        if logs:
            errors = self.analyze_logs_for_errors(logs)
            if errors:
                print(f"\n⚠️ {len(errors)} erreurs trouvées dans les logs:")
                for error in errors[:5]:  # Limite à 5 erreurs
                    print(f"   Ligne {error['line']}: {error['content']}")
            else:
                print("\n✅ Aucune erreur critique dans les logs récents")
        
        # 7. Tests d'authentification
        web_auth_ok = self.check_web_auth_status()
        api_auth_ok = self.check_api_auth_status()
        
        # 8. Synthèse
        print("\n" + "="*60)
        print("📊 SYNTHÈSE DU DIAGNOSTIC")
        print("="*60)
        print(f"Conteneur: {'✅' if container_ok else '❌'} ({status})")
        print(f"ComfyUI-Login: {'✅' if login_installed else '❌'}")
        print(f"Arguments démarrage: {'✅' if args_ok else '❌'}")
        print(f"Dépendances: {'✅' if not missing_deps else '❌'} ({len(missing_deps)} manquantes)")
        print(f"Auth web: {'✅' if web_auth_ok else '❌'}")
        print(f"Auth API: {'✅' if api_auth_ok else '❌'}")
        
        # 9. Recommandations
        print("\n📋 RECOMMANDATIONS:")
        if not login_installed:
            print("- Installer ComfyUI-Login dans custom_nodes")
        if not args_ok:
            print("- Ajouter --enable-cors-header au démarrage")
        if missing_deps:
            print("- Installer les dépendances manquantes")
        if not web_auth_ok:
            print("- Vérifier la configuration de ComfyUI-Login")
        if not api_auth_ok:
            print("- Activer la protection des endpoints API")
        
        success = all([container_ok, login_installed, args_ok, not missing_deps, web_auth_ok, api_auth_ok])
        
        if success:
            print("\n🎉 L'AUTHENTIFICATION COMFYUI EST FONCTIONNELLE!")
        else:
            print("\n⚠️ DES CORRECTIONS SONT NÉCESSAIRES")
        
        return success

def main():
    """Point d'entrée principal"""
    diagnostic = ComfyUIAuthDiagnostic()
    success = diagnostic.run_full_diagnostic()
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()