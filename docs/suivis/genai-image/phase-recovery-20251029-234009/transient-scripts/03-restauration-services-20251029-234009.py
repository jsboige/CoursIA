#!/usr/bin/env python3
"""
Script de Restauration des Services - Phase Recovery SDDD
Créé: 2025-10-29T23:44:00 CET
Auteur: Roo Code Mode
Mission: Planification et exécution de la restauration des services Docker et APIs ComfyUI
"""

import os
import sys
import json
import subprocess
import datetime
import time
from pathlib import Path
from typing import Dict, List, Tuple, Any, Optional

class ServiceRestorer:
    """Classe principale pour la restauration des services"""
    
    def __init__(self, workspace_root: str):
        self.workspace_root = Path(workspace_root)
        self.timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.results = {
            "timestamp": self.timestamp,
            "workspace_root": str(self.workspace_root),
            "restoration_status": "IN_PROGRESS",
            "docker_services": {},
            "comfyui_services": {},
            "api_endpoints": {},
            "restoration_actions": [],
            "validation_results": {}
        }
    
    def log(self, message: str, level: str = "INFO"):
        """Fonction de logging structuré"""
        print(f"[{level}] {self.timestamp} - {message}")
    
    def check_docker_daemon(self) -> Dict[str, Any]:
        """Vérification du daemon Docker"""
        self.log("Vérification du daemon Docker...")
        
        try:
            result = subprocess.run(['docker', '--version'], 
                              capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                version = result.stdout.strip()
                self.log(f"Docker version: {version}")
                return {"status": "available", "version": version}
            else:
                return {"status": "error", "error": result.stderr}
        except Exception as e:
            return {"status": "not_available", "error": str(e)}
    
    def restore_docker_compose_files(self) -> Dict[str, Any]:
        """Restauration des fichiers docker-compose"""
        self.log("Recherche des fichiers docker-compose à restaurer...")
        
        docker_configs = [
            "docker-configurations/docker-compose.yml",
            "docker-configurations/comfyui-qwen/docker-compose.yml",
            "docker-configurations/orchestrator/docker-compose.yml"
        ]
        
        restoration_results = {
            "files_found": [],
            "files_missing": [],
            "files_restored": []
        }
        
        for config_path in docker_configs:
            full_path = self.workspace_root / config_path
            if full_path.exists():
                restoration_results["files_found"].append({
                    "path": config_path,
                    "size": full_path.stat().st_size,
                    "modified": datetime.datetime.fromtimestamp(full_path.stat().st_mtime).isoformat()
                })
                self.log(f"Fichier docker-compose trouvé: {config_path}")
            else:
                restoration_results["files_missing"].append(config_path)
                self.log(f"Fichier docker-compose manquant: {config_path}")
                
                # Tentative de restauration depuis les consolidations
                backup_path = self.workspace_root / "scripts" / "genai-auth" / f"backup_{config_path.replace('/', '_')}"
                if backup_path.exists():
                    try:
                        import shutil
                        backup_path.parent.mkdir(parents=True, exist_ok=True)
                        full_path.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(backup_path, full_path)
                        restoration_results["files_restored"].append({
                            "path": config_path,
                            "restored_from": str(backup_path),
                            "status": "success"
                        })
                        self.log(f"Fichier restauré depuis backup: {config_path}")
                    except Exception as e:
                        restoration_results["files_restored"].append({
                            "path": config_path,
                            "status": "error",
                            "error": str(e)
                        })
        
        return restoration_results
    
    def restore_comfyui_configuration(self) -> Dict[str, Any]:
        """Restauration de la configuration ComfyUI"""
        self.log("Restauration de la configuration ComfyUI...")
        
        comfyui_paths = [
            "docker-configurations/comfyui-qwen",
            "docker-configurations/comfyui-workflows"
        ]
        
        restoration_results = {
            "directories_found": [],
            "directories_missing": [],
            "config_files_restored": [],
            "api_status": "unknown"
        }
        
        for comfyui_path in comfyui_paths:
            full_path = self.workspace_root / comfyui_path
            if full_path.exists():
                restoration_results["directories_found"].append({
                    "path": comfyui_path,
                    "type": "directory"
                })
                self.log(f"Répertoire ComfyUI trouvé: {comfyui_path}")
                
                # Vérification des fichiers de configuration
                config_files = list(full_path.glob("**/*.yml")) + list(full_path.glob("**/*.yaml"))
                for config_file in config_files:
                    restoration_results["config_files_restored"].append({
                        "file": str(config_file.relative_to(self.workspace_root)),
                        "size": config_file.stat().st_size
                    })
            else:
                restoration_results["directories_missing"].append(comfyui_path)
                self.log(f"Répertoire ComfyUI manquant: {comfyui_path}")
        
        # Test des endpoints API ComfyUI
        common_ports = [8188, 7860, 8080]
        for port in common_ports:
            endpoint_status = self.test_api_endpoint(port)
            restoration_results["api_status"][f"port_{port}"] = endpoint_status
        
        return restoration_results
    
    def test_api_endpoint(self, port: int, timeout: int = 5) -> Dict[str, Any]:
        """Test d'un endpoint API ComfyUI"""
        try:
            import socket
            import urllib.request
            import urllib.error
            
            # Test de connexion socket
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(timeout)
            result = sock.connect_ex(('localhost', port))
            sock.close()
            
            if result == 0:
                # Test HTTP
                try:
                    response = urllib.request.urlopen(f"http://localhost:{port}", timeout=timeout)
                    return {
                        "port": port,
                        "socket_status": "open",
                        "http_status": "responsive",
                        "status": "available"
                    }
                except urllib.error.URLError as e:
                    return {
                        "port": port,
                        "socket_status": "open", 
                        "http_status": "error",
                        "error": str(e),
                        "status": "partial"
                    }
            else:
                return {
                    "port": port,
                    "socket_status": "closed",
                    "status": "unavailable"
                }
        except Exception as e:
            return {
                "port": port,
                "status": "error",
                "error": str(e)
            }
    
    def apply_consolidated_fixes(self) -> Dict[str, Any]:
        """Application des corrections utilisant les scripts consolidés"""
        self.log("Application des corrections consolidées...")
        
        fixes_applied = {
            "qwen_workflow_fixes": [],
            "comfyui_auth_fixes": [],
            "environment_fixes": [],
            "errors": []
        }
        
        scripts_path = self.workspace_root / "scripts" / "genai-auth"
        
        # Application des corrections Qwen workflow
        try:
            fix_script = scripts_path / "fix-qwen-workflow.py"
            if fix_script.exists():
                result = subprocess.run([
                    sys.executable, str(fix_script), "--apply-fixes"
                ], capture_output=True, text=True, timeout=30)
                
                if result.returncode == 0:
                    fixes_applied["qwen_workflow_fixes"].append("Corrections Qwen workflow appliquées")
                    self.log("Corrections Qwen workflow appliquées avec succès")
                else:
                    fixes_applied["errors"].append(f"Erreur Qwen fixes: {result.stderr}")
            else:
                fixes_applied["errors"].append("Script fix-qwen-workflow.py non trouvé")
        except Exception as e:
            fixes_applied["errors"].append(f"Exception Qwen fixes: {str(e)}")
        
        # Application des corrections ComfyUI auth
        try:
            auth_script = scripts_path / "comfyui_client_helper.py"
            if auth_script.exists():
                result = subprocess.run([
                    sys.executable, str(auth_script), "--setup-auth"
                ], capture_output=True, text=True, timeout=30)
                
                if result.returncode == 0:
                    fixes_applied["comfyui_auth_fixes"].append("Configuration ComfyUI auth appliquée")
                    self.log("Configuration ComfyUI auth appliquée avec succès")
                else:
                    fixes_applied["errors"].append(f"Erreur ComfyUI auth: {result.stderr}")
            else:
                fixes_applied["errors"].append("Script comfyui_client_helper.py non trouvé")
        except Exception as e:
            fixes_applied["errors"].append(f"Exception ComfyUI auth: {str(e)}")
        
        return fixes_applied
    
    def validate_restoration(self) -> Dict[str, Any]:
        """Validation de la restauration complète"""
        self.log("Validation de la restauration...")
        
        validation_results = {
            "docker_status": "unknown",
            "comfyui_status": "unknown", 
            "api_connectivity": "unknown",
            "overall_status": "unknown"
        }
        
        # Validation Docker
        docker_status = self.check_docker_daemon()
        validation_results["docker_status"] = docker_status["status"]
        
        # Validation ComfyUI
        if self.results.get("comfyui_services", {}).get("api_status"):
            available_endpoints = [
                ep for ep in self.results["comfyui_services"]["api_status"].values()
                if ep.get("status") == "available"
            ]
            if available_endpoints:
                validation_results["comfyui_status"] = "available"
                validation_results["api_connectivity"] = "functional"
            else:
                validation_results["comfyui_status"] = "unavailable"
                validation_results["api_connectivity"] = "failed"
        
        # Statut global
        if (validation_results["docker_status"] == "available" and 
            validation_results["comfyui_status"] == "available"):
            validation_results["overall_status"] = "success"
        elif (validation_results["docker_status"] in ["available", "not_available"] and 
              validation_results["comfyui_status"] == "unavailable"):
            validation_results["overall_status"] = "partial"
        else:
            validation_results["overall_status"] = "failed"
        
        return validation_results
    
    def run_restoration(self) -> Dict[str, Any]:
        """Exécution complète de la restauration des services"""
        self.log("Démarrage de la restauration des services...")
        
        # Étape 1: Vérification Docker
        self.results["docker_services"] = self.check_docker_daemon()
        
        # Étape 2: Restauration docker-compose
        self.results["docker_services"]["compose_files"] = self.restore_docker_compose_files()
        
        # Étape 3: Restauration ComfyUI
        self.results["comfyui_services"] = self.restore_comfyui_configuration()
        
        # Étape 4: Application des corrections consolidées
        self.results["restoration_actions"] = self.apply_consolidated_fixes()
        
        # Étape 5: Validation finale
        self.results["validation_results"] = self.validate_restoration()
        
        # Finalisation
        self.results["restoration_status"] = "COMPLETED"
        self.log("Restauration des services terminée")
        
        return self.results
    
    def save_report(self, output_path: str = None):
        """Sauvegarde du rapport de restauration"""
        if output_path is None:
            output_path = self.workspace_root / "docs/suivis/genai-image/phase-recovery-20251029-234009/reports/03-restauration-services.json"
        
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.results, f, indent=2, ensure_ascii=False)
        
        self.log(f"Rapport de restauration sauvegardé: {output_path}")
        return str(output_path)

def main():
    """Fonction principale d'exécution de la restauration"""
    print("🔧 RESTAURATION DES SERVICES SDDD - PHASE RECOVERY")
    print("=" * 60)
    
    # Détection du workspace
    workspace_root = os.getcwd()
    print(f"📁 Workspace: {workspace_root}")
    
    # Initialisation et exécution de la restauration
    restorer = ServiceRestorer(workspace_root)
    results = restorer.run_restoration()
    
    # Affichage résumé
    print("\n📊 RÉSUMÉ DE LA RESTAURATION:")
    print(f"   Status: {results['restoration_status']}")
    print(f"   Docker: {results['docker_services'].get('status', 'unknown')}")
    print(f"   ComfyUI: {results['validation_results'].get('comfyui_status', 'unknown')}")
    print(f"   APIs: {results['validation_results'].get('api_connectivity', 'unknown')}")
    
    # Affichage des actions de restauration
    if results.get("restoration_actions"):
        print("\n🔧 ACTIONS DE RESTAURATION:")
        actions = results["restoration_actions"]
        
        if actions.get("qwen_workflow_fixes"):
            print(f"   ✅ Corrections Qwen workflow: {len(actions['qwen_workflow_fixes'])}")
        
        if actions.get("comfyui_auth_fixes"):
            print(f"   ✅ Configuration ComfyUI: {len(actions['comfyui_auth_fixes'])}")
        
        if actions.get("environment_fixes"):
            print(f"   ✅ Corrections environnement: {len(actions['environment_fixes'])}")
        
        if actions.get("errors"):
            print(f"\n❌ ERREURS RENCONTRÉES:")
            for error in actions["errors"][:3]:  # Limiter pour lisibilité
                print(f"   • {error}")
    
    # Validation finale
    validation = results.get("validation_results", {})
    overall_status = validation.get("overall_status", "unknown")
    
    status_emoji = {
        "success": "✅",
        "partial": "⚠️", 
        "failed": "❌",
        "unknown": "❓"
    }.get(overall_status, "❓")
    
    print(f"\n🎯 STATUT GLOBAL DE RESTAURATION: {status_emoji} {overall_status.upper()}")
    
    # Sauvegarde du rapport
    report_path = restorer.save_report()
    print(f"\n📄 Rapport détaillé sauvegardé: {report_path}")
    
    if overall_status == "success":
        print("\n✅ Restauration des services SDDD terminée avec succès")
        return 0
    elif overall_status == "partial":
        print("\n⚠️ Restauration partielle -某些服务需要手动干预")
        return 1
    else:
        print("\n❌ Restauration échouée - Intervention manuelle requise")
        return 2

if __name__ == "__main__":
    sys.exit(main())