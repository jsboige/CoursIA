#!/usr/bin/env python3
"""
Utilitaire consolidé pour le diagnostic de l'environnement ComfyUI

Ce script fusionne les fonctionnalités de :
- diagnostic-qwen-complete.py
- Autres scripts de diagnostic

FONCTIONNALITÉS PRINCIPALES :
1. Diagnostic complet de l'environnement ComfyUI
2. Validation des dépendances Python
3. Diagnostic des conteneurs Docker
4. Vérification des services ComfyUI
5. Génération de rapports détaillés
"""

import os
import sys
import json
import subprocess
import logging
import requests
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Any

# Configuration du logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class DiagnosticUtils:
    """
    Classe utilitaire consolidée pour le diagnostic de l'environnement ComfyUI
    """
    
    def __init__(self, workspace_path: str = None, backup_enabled: bool = True):
        self.workspace_path = Path(workspace_path) if workspace_path else Path.cwd()
        self.backup_dir = self.workspace_path / "backups"
        self.backup_enabled = backup_enabled
        
        # Créer le répertoire de backup si nécessaire
        if self.backup_enabled:
            self.backup_dir.mkdir(parents=True, exist_ok=True)
    
    def check_python_environment(self) -> Dict[str, Any]:
        """
        Vérifie l'environnement Python et les dépendances
        
        Returns:
            Dictionnaire avec les résultats du diagnostic
        """
        logger.info("🔍 Diagnostic de l'environnement Python...")
        
        diagnostic_results = {
            "python_version": sys.version,
            "python_path": sys.executable,
            "python_paths": sys.path,
            "installed_packages": {},
            "missing_packages": [],
            "issues": [],
            "comfyui_accessible": False
        }
        
        # Vérifier les packages essentiels
        essential_packages = [
            "torch", "torchvision", "numpy", "PIL", "Pillow",
            "comfy", "comfy.model_management", "folder_paths"
        ]
        
        try:
            # Vérifier les packages installés
            import importlib.util
            
            for package in essential_packages:
                try:
                    importlib.util.find_spec(package)
                    diagnostic_results["installed_packages"][package] = {
                        "version": self._get_package_version(package),
                        "status": "installed"
                    }
                except ImportError:
                    diagnostic_results["missing_packages"].append(package)
                    diagnostic_results["issues"].append(f"Package manquant: {package}")
                except Exception as e:
                    diagnostic_results["issues"].append(f"Erreur vérification {package}: {e}")
            
            # Vérifier l'accès à ComfyUI
            try:
                response = requests.get('http://localhost:8188/system_stats', timeout=5)
                if response.status_code == 200:
                    diagnostic_results["comfyui_accessible"] = True
                    logger.info("✅ ComfyUI accessible")
                else:
                    diagnostic_results["issues"].append(f"ComfyUI inaccessible (HTTP {response.status_code})")
            except Exception as e:
                diagnostic_results["issues"].append(f"Erreur test ComfyUI: {e}")
            
            logger.info(f"📊 Packages installés: {len(diagnostic_results['installed_packages'])}")
            logger.info(f"⚠️ Packages manquants: {len(diagnostic_results['missing_packages'])}")
            logger.info(f"❌ Problèmes détectés: {len(diagnostic_results['issues'])}")
            
            return diagnostic_results
            
        except Exception as e:
            logger.error(f"❌ Erreur diagnostic Python: {e}")
            diagnostic_results["issues"].append(f"Erreur diagnostic: {e}")
            return diagnostic_results
    
    def _get_package_version(self, package_name: str) -> str:
        """
        Récupère la version d'un package installé
        """
        try:
            import importlib.metadata
            return importlib.metadata.version(package_name)
        except Exception:
            return "Inconnue"
    
    def check_docker_containers(self) -> Dict[str, Any]:
        """
        Vérifie l'état des conteneurs Docker ComfyUI
        
        Returns:
            Dictionnaire avec les résultats du diagnostic
        """
        logger.info("🐳 Diagnostic des conteneurs Docker...")
        
        diagnostic_results = {
            "containers": [],
            "images": [],
            "volumes": [],
            "networks": [],
            "issues": [],
            "comfyui_running": False
        }
        
        try:
            # Lister les conteneurs
            result = subprocess.run([
                'docker', 'ps', '-a', '--filter', 'name=comfyui'
            ], capture_output=True, text=True, timeout=10)
            
            if result.returncode == 0:
                lines = result.stdout.strip().split('\n')
                for line in lines:
                    if 'comfyui' in line.lower():
                        container_info = self._parse_container_line(line)
                        if container_info:
                            diagnostic_results["containers"].append(container_info)
                            diagnostic_results["comfyui_running"] = True
            
            # Lister les images
            result = subprocess.run([
                'docker', 'images', '--filter', 'comfyui'
            ], capture_output=True, text=True, timeout=10)
            
            if result.returncode == 0:
                lines = result.stdout.strip().split('\n')
                for line in lines:
                    if 'comfyui' in line.lower():
                        image_info = self._parse_image_line(line)
                        if image_info:
                            diagnostic_results["images"].append(image_info)
            
            logger.info(f"📊 Conteneurs ComfyUI: {len(diagnostic_results['containers'])}")
            logger.info(f"📊 Images ComfyUI: {len(diagnostic_results['images'])}")
            
        except Exception as e:
            diagnostic_results["issues"].append(f"Erreur diagnostic Docker: {e}")
        
        return diagnostic_results
    
    def _parse_container_line(self, line: str) -> Optional[Dict[str, str]]:
        """
        Extrait les informations d'une ligne de conteneur Docker
        """
        try:
            parts = line.split()
            if len(parts) >= 2:
                return {
                    "id": parts[0],
                    "image": parts[1],
                    "status": parts[2] if len(parts) > 2 else "unknown",
                    "created": parts[3] if len(parts) > 3 else "unknown"
                }
        except Exception:
            return None
    
    def _parse_image_line(self, line: str) -> Optional[Dict[str, str]]:
        """
        Extrait les informations d'une ligne d'image Docker
        """
        try:
            parts = line.split()
            if len(parts) >= 2:
                return {
                    "repository": parts[0],
                    "tag": parts[1],
                    "image_id": parts[2] if len(parts) > 2 else "unknown",
                    "created": parts[3] if len(parts) > 3 else "unknown"
                }
        except Exception:
            return None
    
    def check_comfyui_services(self) -> Dict[str, Any]:
        """
        Vérifie l'état des services ComfyUI
        
        Returns:
            Dictionnaire avec les résultats du diagnostic
        """
        logger.info("🔧 Diagnostic des services ComfyUI...")
        
        diagnostic_results = {
            "api_endpoint": "http://localhost:8188",
            "api_status": False,
            "api_response": None,
            "web_ui": "http://localhost:8188",
            "web_ui_status": False,
            "services": {},
            "issues": []
        }
        
        try:
            # Tester l'endpoint API
            try:
                response = requests.get(diagnostic_results["api_endpoint"], timeout=5)
                diagnostic_results["api_status"] = response.status_code == 200
                diagnostic_results["api_response"] = response.json() if response.headers.get('content-type', '').startswith('application/json') else response.text
                logger.info("✅ API endpoint accessible")
            except Exception as e:
                diagnostic_results["issues"].append(f"Erreur API endpoint: {e}")
            
            # Tester l'interface web
            try:
                response = requests.get(diagnostic_results["web_ui"], timeout=5)
                diagnostic_results["web_ui_status"] = response.status_code == 200
                logger.info("✅ Web UI accessible")
            except Exception as e:
                diagnostic_results["issues"].append(f"Erreur Web UI: {e}")
            
            # Vérifier les services spécifiques
            services_to_check = [
                {"name": "QwenCustomNodes", "endpoint": "/custom_nodes"},
                {"name": "ModelManager", "endpoint": "/model"},
                {"name": "ImageProcessor", "endpoint": "/image"},
                {"name": "WorkflowManager", "endpoint": "/workflow"}
            ]
            
            for service in services_to_check:
                service_url = f"{diagnostic_results['api_endpoint']}{service['endpoint']}"
                try:
                    response = requests.get(service_url, timeout=5)
                    service_status = response.status_code == 200
                    diagnostic_results["services"][service["name"]] = {
                        "status": "available" if service_status else "unavailable",
                        "response_code": response.status_code,
                        "response_time": response.elapsed.total_seconds() if hasattr(response, 'elapsed') else None
                    }
                    logger.info(f"✅ Service {service['name']}: {service_status}")
                except Exception as e:
                    diagnostic_results["services"][service["name"]] = {
                        "status": "error",
                        "error": str(e)
                    }
                    diagnostic_results["issues"].append(f"Erreur service {service['name']}: {e}")
            
        except Exception as e:
            diagnostic_results["issues"].append(f"Erreur diagnostic services: {e}")
        
        return diagnostic_results
    
    def generate_diagnostic_report(self, results: Dict[str, Any]) -> str:
        """
        Génère un rapport de diagnostic formaté
        
        Args:
            results: Résultats du diagnostic
            
        Returns:
            Rapport formaté en Markdown
        """
        report_lines = [
            "# RAPPORT DE DIAGNOSTIC COMFYUI",
            f"Généré le {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            "",
            "## 📊 ENVIRONNEMENT PYTHON",
            f"**Version Python**: {results.get('python_version', 'Inconnue')}",
            f"**Chemin**: {results.get('python_path', 'Inconnu')}",
            f"**Packages installés**: {len(results.get('installed_packages', {}))}",
            f"**Packages manquants**: {len(results.get('missing_packages', []))}",
            ""
            "## 🐳 ÉTAT DOCKER",
            f"**Conteneurs ComfyUI**: {len(results.get('containers', []))}",
            f"**Images ComfyUI**: {len(results.get('images', []))}",
            f"**ComfyUI en cours**: {results.get('comfyui_running', False)}",
            "",
            "## 🔧 SERVICES COMFYUI",
            f"**API Endpoint**: {results.get('api_endpoint', 'Inconnu')}",
            f"**API Status**: {'✅ Accessible' if results.get('api_status') else '❌ Inaccessible'}",
            f"**Web UI**: {results.get('web_ui', 'Inconnu')}",
            f"**Web UI Status**: {'✅ Accessible' if results.get('web_ui_status') else '❌ Inaccessible'}",
            ""
        ]
        
        # Ajouter les services
        services = results.get('services', {})
        if services:
            report_lines.append("### Services détectés:")
            for service_name, service_info in services.items():
                status_icon = "✅" if service_info.get("status") == "available" else "❌"
                report_lines.append(f"- **{service_name}**: {status_icon} {service_info.get('status')}")
                if service_info.get("response_time"):
                    report_lines.append(f"  - Temps de réponse: {service_info.get('response_time'):.2f}s")
                if service_info.get("error"):
                    report_lines.append(f"  - Erreur: {service_info.get('error')}")
        
        # Ajouter les problèmes
        issues = results.get('issues', [])
        if issues:
            report_lines.append("")
            report_lines.append("### ⚠️ PROBLÈMES DÉTECTÉS:")
            for issue in issues:
                report_lines.append(f"- {issue}")
        
        return "\n".join(report_lines)

def main():
    """Fonction principale de l'utilitaire"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Utilitaire consolidé pour le diagnostic de l'environnement ComfyUI",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument(
        "--python-env",
        action="store_true",
        help="Vérifier l'environnement Python"
    )
    
    parser.add_argument(
        "--docker",
        action="store_true",
        help="Vérifier les conteneurs Docker ComfyUI"
    )
    
    parser.add_argument(
        "--services",
        action="store_true",
        help="Vérifier l'état des services ComfyUI"
    )
    
    parser.add_argument(
        "--full",
        action="store_true",
        help="Diagnostic complet (Python + Docker + Services)"
    )
    
    parser.add_argument(
        "--workspace",
        help="Chemin vers le workspace (défaut: répertoire courant)"
    )
    
    parser.add_argument(
        "--no-backup",
        action="store_true",
        help="Désactiver la création de backups"
    )
    
    args = parser.parse_args()
    
    # Initialiser l'utilitaire
    utils = DiagnosticUtils(
        workspace_path=args.workspace,
        backup_enabled=not args.no_backup
    )
    
    success = True
    
    try:
        if args.full:
            # Diagnostic complet
            python_results = utils.check_python_environment()
            docker_results = utils.check_docker_containers()
            services_results = utils.check_comfyui_services()
            
            # Combiner les résultats
            combined_results = {
                **python_results,
                **docker_results,
                **services_results
            }
            
            report = utils.generate_diagnostic_report(combined_results)
            print(report)
            
        elif args.python_env:
            python_results = utils.check_python_environment()
            report = utils.generate_diagnostic_report(python_results)
            print(report)
            
        elif args.docker:
            docker_results = utils.check_docker_containers()
            report = utils.generate_diagnostic_report(docker_results)
            print(report)
            
        elif args.services:
            services_results = utils.check_comfyui_services()
            report = utils.generate_diagnostic_report(services_results)
            print(report)
            
        else:
            parser.print_help()
            return 0
    
    except KeyboardInterrupt:
        print("\n⏹️ Opération interrompue par l'utilisateur")
        return 130
    except Exception as e:
        print(f"\n❌ Erreur: {e}")
        return 1

if __name__ == "__main__":
    sys.exit(main())