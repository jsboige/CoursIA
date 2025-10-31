#!/usr/bin/env python3
"""
Script de Diagnostic Environnemental - Phase Recovery SDDD
Créé: 2025-10-29T23:42:00 CET
Auteur: Roo Code Mode
Mission: Diagnostic complet de l'environnement GenAI après sécurisation Git
"""

import os
import sys
import json
import subprocess
import datetime
from pathlib import Path
from typing import Dict, List, Tuple, Any

class EnvironmentDiagnostic:
    """Classe principale pour le diagnostic environnemental SDDD"""
    
    def __init__(self, workspace_root: str):
        self.workspace_root = Path(workspace_root)
        self.timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.results = {
            "timestamp": self.timestamp,
            "workspace_root": str(self.workspace_root),
            "diagnostic_status": "IN_PROGRESS",
            "components": {},
            "issues": [],
            "recommendations": []
        }
    
    def log(self, message: str, level: str = "INFO"):
        """Fonction de logging structuré"""
        print(f"[{level}] {self.timestamp} - {message}")
    
    def check_docker_services(self) -> Dict[str, Any]:
        """Vérification des services Docker"""
        self.log("Vérification des services Docker...")
        
        docker_configs = [
            "docker-configurations/docker-compose.yml",
            "docker-configurations/comfyui-qwen/docker-compose.yml",
            "docker-configurations/orchestrator/docker-compose.yml"
        ]
        
        docker_status = {
            "docker_compose_files": [],
            "running_containers": [],
            "docker_daemon_status": "unknown",
            "issues": []
        }
        
        # Vérification des fichiers docker-compose
        for config_path in docker_configs:
            full_path = self.workspace_root / config_path
            if full_path.exists():
                docker_status["docker_compose_files"].append({
                    "path": config_path,
                    "exists": True,
                    "size": full_path.stat().st_size if full_path.is_file() else 0
                })
                self.log(f"Fichier docker-compose trouvé: {config_path}")
            else:
                docker_status["docker_compose_files"].append({
                    "path": config_path,
                    "exists": False
                })
                docker_status["issues"].append(f"Fichier manquant: {config_path}")
        
        # Vérification des conteneurs Docker actifs
        try:
            result = subprocess.run(['docker', 'ps', '--format', 'json'], 
                              capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                containers = json.loads(result.stdout)
                docker_status["running_containers"] = containers
                docker_status["docker_daemon_status"] = "running"
                self.log(f"Docker daemon actif avec {len(containers)} conteneurs")
            else:
                docker_status["docker_daemon_status"] = "error"
                docker_status["issues"].append(f"Erreur docker ps: {result.stderr}")
        except Exception as e:
            docker_status["docker_daemon_status"] = "not_available"
            docker_status["issues"].append(f"Docker non disponible: {str(e)}")
        
        return docker_status
    
    def check_consolidated_scripts(self) -> Dict[str, Any]:
        """Analyse des scripts consolidés existants"""
        self.log("Analyse des scripts consolidés...")
        
        scripts_path = self.workspace_root / "scripts" / "genai-auth"
        consolidated_scripts = [
            "diagnostic-qwen-complete.py",
            "fix-qwen-workflow.py", 
            "validate-qwen-solution.py",
            "comfyui_client_helper.py"
        ]
        
        scripts_status = {
            "scripts_directory": str(scripts_path),
            "consolidated_scripts": [],
            "missing_scripts": [],
            "script_analysis": {}
        }
        
        if not scripts_path.exists():
            scripts_status["issues"].append("Répertoire scripts/genai-auth non trouvé")
            return scripts_status
        
        for script_name in consolidated_scripts:
            script_path = scripts_path / script_name
            if script_path.exists():
                script_info = {
                    "name": script_name,
                    "path": f"scripts/genai-auth/{script_name}",
                    "exists": True,
                    "size": script_path.stat().st_size,
                    "modified": datetime.datetime.fromtimestamp(script_path.stat().st_mtime).isoformat()
                }
                scripts_status["consolidated_scripts"].append(script_info)
                
                # Analyse basique du script
                try:
                    with open(script_path, 'r', encoding='utf-8') as f:
                        content = f.read()
                        script_info["lines_count"] = len(content.splitlines())
                        script_info["has_main_function"] = "def main(" in content or "if __name__" in content
                except Exception as e:
                    script_info["analysis_error"] = str(e)
                    scripts_status["issues"].append(f"Erreur analyse {script_name}: {str(e)}")
            else:
                scripts_status["missing_scripts"].append(script_name)
                scripts_status["issues"].append(f"Script consolidé manquant: {script_name}")
        
        return scripts_status
    
    def check_genai_notebooks(self) -> Dict[str, Any]:
        """Vérification des notebooks GenAI"""
        self.log("Vérification des notebooks GenAI...")
        
        notebooks_path = self.workspace_root / "MyIA.AI.Notebooks" / "GenAI"
        notebooks_status = {
            "notebooks_directory": str(notebooks_path),
            "notebooks_count": 0,
            "key_files": {},
            "issues": []
        }
        
        if not notebooks_path.exists():
            notebooks_status["issues"].append("Répertoire GenAI non trouvé")
            return notebooks_status
        
        # Fichiers clés à vérifier
        key_files = [
            ".env.template",
            "README.md", 
            "requirements.txt",
            "DEPLOYMENT.md",
            "TROUBLESHOOTING.md"
        ]
        
        for key_file in key_files:
            file_path = notebooks_path / key_file
            notebooks_status["key_files"][key_file] = {
                "exists": file_path.exists(),
                "path": f"MyIA.AI.Notebooks/GenAI/{key_file}"
            }
            if file_path.exists():
                self.log(f"Fichier clé trouvé: {key_file}")
        
        # Compter les notebooks .ipynb
        try:
            notebooks_count = len(list(notebooks_path.glob("**/*.ipynb")))
            notebooks_status["notebooks_count"] = notebooks_count
            self.log(f"{notebooks_count} notebooks .ipynb trouvés")
        except Exception as e:
            notebooks_status["issues"].append(f"Erreur comptage notebooks: {str(e)}")
        
        return notebooks_status
    
    def check_comfyui_services(self) -> Dict[str, Any]:
        """Vérification des services ComfyUI"""
        self.log("Vérification des services ComfyUI...")
        
        comfyui_status = {
            "comfyui_directories": [],
            "api_endpoints": [],
            "authentication_status": "unknown",
            "issues": []
        }
        
        # Vérification des répertoires ComfyUI
        comfyui_paths = [
            "docker-configurations/comfyui-qwen",
            "docker-configurations/comfyui-workflows"
        ]
        
        for comfyui_path in comfyui_paths:
            full_path = self.workspace_root / comfyui_path
            if full_path.exists():
                comfyui_status["comfyui_directories"].append({
                    "path": comfyui_path,
                    "exists": True,
                    "type": "directory"
                })
                self.log(f"Répertoire ComfyUI trouvé: {comfyui_path}")
            else:
                comfyui_status["comfyui_directories"].append({
                    "path": comfyui_path,
                    "exists": False
                })
                comfyui_status["issues"].append(f"Répertoire ComfyUI manquant: {comfyui_path}")
        
        # Vérification des endpoints API ComfyUI (ports courants)
        common_ports = [8188, 7860, 8080]
        for port in common_ports:
            comfyui_status["api_endpoints"].append({
                "port": port,
                "status": "untested",
                "url": f"http://localhost:{port}"
            })
        
        return comfyui_status
    
    def generate_recommendations(self, diagnostic_results: Dict[str, Any]) -> List[str]:
        """Génération des recommandations basées sur le diagnostic"""
        recommendations = []
        
        # Recommandations Docker
        docker_status = diagnostic_results.get("docker_services", {})
        if docker_status.get("docker_daemon_status") == "not_available":
            recommendations.append("Installer Docker Desktop ou démarrer le service Docker")
        if not docker_status.get("docker_compose_files"):
            recommendations.append("Créer des fichiers docker-compose.yml pour les services")
        
        # Recommandations Scripts
        scripts_status = diagnostic_results.get("consolidated_scripts", {})
        if scripts_status.get("missing_scripts"):
            recommendations.append("Restaurer les scripts consolidés manquants depuis les backups")
        
        # Recommandations Notebooks
        notebooks_status = diagnostic_results.get("genai_notebooks", {})
        if notebooks_status.get("notebooks_count", 0) == 0:
            recommendations.append("Restaurer les notebooks GenAI depuis les sauvegardes")
        
        # Recommandations ComfyUI
        comfyui_status = diagnostic_results.get("comfyui_services", {})
        if not comfyui_status.get("comfyui_directories"):
            recommendations.append("Restaurer la configuration ComfyUI depuis les backups")
        
        return recommendations
    
    def run_diagnostic(self) -> Dict[str, Any]:
        """Exécution complète du diagnostic environnemental"""
        self.log("Démarrage du diagnostic environnemental SDDD...")
        
        # Exécution des vérifications
        self.results["components"]["docker_services"] = self.check_docker_services()
        self.results["components"]["consolidated_scripts"] = self.check_consolidated_scripts()
        self.results["components"]["genai_notebooks"] = self.check_genai_notebooks()
        self.results["components"]["comfyui_services"] = self.check_comfyui_services()
        
        # Compilation des problèmes
        for component in self.results["components"].values():
            if "issues" in component and component["issues"]:
                self.results["issues"].extend(component["issues"])
        
        # Génération des recommandations
        self.results["recommendations"] = self.generate_recommendations(self.results["components"])
        
        # Finalisation du diagnostic
        self.results["diagnostic_status"] = "COMPLETED"
        self.log("Diagnostic environnemental terminé")
        
        return self.results
    
    def save_report(self, output_path: str = None):
        """Sauvegarde du rapport de diagnostic"""
        if output_path is None:
            output_path = self.workspace_root / "docs/suivis/genai-image/phase-recovery-20251029-234009/reports/01-diagnostic-environnemental.json"
        
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.results, f, indent=2, ensure_ascii=False)
        
        self.log(f"Rapport de diagnostic sauvegardé: {output_path}")
        return str(output_path)

def main():
    """Fonction principale d'exécution du diagnostic"""
    print("🔍 DIAGNOSTIC ENVIRONNEMENTAL SDDD - PHASE RECOVERY")
    print("=" * 60)
    
    # Détection du workspace
    workspace_root = os.getcwd()
    print(f"📁 Workspace: {workspace_root}")
    
    # Initialisation et exécution du diagnostic
    diagnostic = EnvironmentDiagnostic(workspace_root)
    results = diagnostic.run_diagnostic()
    
    # Affichage résumé
    print("\n📊 RÉSUMÉ DU DIAGNOSTIC:")
    print(f"   Status: {results['diagnostic_status']}")
    print(f"   Composants analysés: {len(results['components'])}")
    print(f"   Problèmes identifiés: {len(results['issues'])}")
    print(f"   Recommandations: {len(results['recommendations'])}")
    
    if results['issues']:
        print("\n⚠️  PROBLÈMES IDENTIFIÉS:")
        for issue in results['issues'][:5]:  # Limiter à 5 pour la lisibilité
            print(f"   • {issue}")
        if len(results['issues']) > 5:
            print(f"   ... et {len(results['issues']) - 5} autres")
    
    if results['recommendations']:
        print("\n💡 RECOMMANDATIONS:")
        for rec in results['recommendations'][:5]:  # Limiter à 5 pour la lisibilité
            print(f"   • {rec}")
        if len(results['recommendations']) > 5:
            print(f"   ... et {len(results['recommendations']) - 5} autres")
    
    # Sauvegarde du rapport
    report_path = diagnostic.save_report()
    print(f"\n📄 Rapport détaillé sauvegardé: {report_path}")
    
    print("\n✅ Diagnostic environnemental SDDD terminé avec succès")
    return 0 if not results['issues'] else 1

if __name__ == "__main__":
    sys.exit(main())