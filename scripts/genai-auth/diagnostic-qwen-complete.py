#!/usr/bin/env python3
"""
Script de diagnostic complet pour l'environnement ComfyUI QwenImageWanBridge
Consolide les fonctionnalités de diagnostic de multiples scripts en une seule solution robuste.

Scripts remplacés par cette consolidation :
- debug-import-issue.py (diagnostic des imports)
- debug-import-detailed.py (diagnostic détaillé des imports)
- test-direct-container.py (test de connectivité conteneur)
- fix-qwen-package-structure.py (analyse structurelle)
- test-qwen-imports-fix.py (validation des imports)
- test-qwen-imports-validation.py (validation avancée des imports)
- test-qwen-corrected.py (test des corrections)
- test-qwen-final.py (test final)
- validate-qwen-fixes.py (validation des corrections)
- quick-check.sh (vérifications rapides)

Fonctionnalités:
1. Analyse structurelle des packages Python
2. Inspection des nodes ComfyUI
3. Diagnostic de l'environnement
4. Génération de rapport JSON détaillé

Auteur: Roo AI Assistant
Version: 2.0.0
Date: 2025-10-28
"""

import argparse
import json
import os
import platform
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Any


class QwenDiagnosticComplete:
    """Classe principale de diagnostic consolidé pour Qwen/ComfyUI"""
    
    def __init__(self, container_name: str = "comfy-ui-ia"):
        """
        Initialise le diagnostic avec configuration par défaut
        
        Args:
            container_name: Nom du container Docker ComfyUI
        """
        self.container_name = container_name
        self.custom_nodes_path = "/workspace/ComfyUI/custom_nodes"
        self.bridge_path = f"{self.custom_nodes_path}/ComfyUI_QwenImageWanBridge"
        self.results = {
            "timestamp": "",
            "container_name": container_name,
            "package_structure": {},
            "nodes_inspection": {},
            "environment_diagnostic": {},
            "summary": {
                "total_issues": 0,
                "critical_issues": 0,
                "warnings": 0,
                "recommendations": []
            }
        }
    
    def log_info(self, message: str) -> None:
        """Affiche un message informatif"""
        print(f"ℹ️  {message}")
    
    def log_success(self, message: str) -> None:
        """Affiche un message de succès"""
        print(f"✅ {message}")
    
    def log_warning(self, message: str) -> None:
        """Affiche un avertissement"""
        print(f"⚠️  {message}")
    
    def log_error(self, message: str) -> None:
        """Affiche une erreur"""
        print(f"❌ {message}")
    
    def log_critical(self, message: str) -> None:
        """Affiche une erreur critique"""
        print(f"🚨 {message}")
    
    def run_docker_command(self, command: str) -> Tuple[bool, str, str]:
        """
        Exécute une commande Docker et retourne le résultat
        
        Args:
            command: Commande à exécuter
            
        Returns:
            Tuple (success, stdout, stderr)
        """
        try:
            # Détection de l'OS et adaptation de la commande
            if platform.system() == "Windows":
                # Sur Windows, utiliser PowerShell avec échappement correct
                escaped_command = command.replace('"', '""').replace("'", "''")
                full_command = f'docker exec {self.container_name} powershell -Command "{escaped_command}"'
            else:
                # Sur Linux/Mac, utiliser bash
                escaped_command = command.replace("'", "'\"'\"'")
                full_command = f"docker exec {self.container_name} bash -c '{escaped_command}'"
            
            result = subprocess.run(
                full_command,
                shell=True,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            success = result.returncode == 0
            stdout = result.stdout.strip() if result.stdout else ""
            stderr = result.stderr.strip() if result.stderr else ""
            
            return success, stdout, stderr
        except subprocess.TimeoutExpired:
            return False, "", "Timeout après 30 secondes"
        except Exception as e:
            return False, "", f"Erreur d'exécution: {str(e)}"
    
    def check_container_connectivity(self) -> bool:
        """Vérifie si le container est accessible"""
        try:
            success, _, _ = self.run_docker_command("echo 'container_ok'")
            return success
        except Exception:
            return False
    
    def analyze_package_structure(self) -> Dict[str, Any]:
        """
        Analyse la structure du package ComfyUI-QwenImageWanBridge
        
        Returns:
            Dictionnaire avec les résultats de l'analyse
        """
        self.log_info("Analyse structurelle des packages Python...")
        
        analysis = {
            "bridge_path": self.bridge_path,
            "exists": False,
            "has_init": False,
            "subdirectories": [],
            "python_files": [],
            "missing_inits": [],
            "issues": []
        }
        
        # Vérifier si le package existe
        check_cmd = f"test -d {self.bridge_path}"
        success, _, stderr = self.run_docker_command(check_cmd)
        analysis["exists"] = success
        
        if not success:
            analysis["issues"].append(f"Package non trouvé: {self.bridge_path}")
            return analysis
        
        # Vérifier __init__.py à la racine
        init_check_cmd = f"test -f {self.bridge_path}/__init__.py"
        success, _, _ = self.run_docker_command(init_check_cmd)
        analysis["has_init"] = success
        
        if not success:
            analysis["missing_inits"].append("racine")
            analysis["issues"].append("__init__.py manquant à la racine du package")
        
        # Lister les fichiers et sous-répertoires
        list_cmd = f"ls -la {self.bridge_path}"
        success, stdout, stderr = self.run_docker_command(list_cmd)
        
        if success and stdout:
            lines = stdout.split('\n')
            for line in lines:
                if line.strip():
                    parts = line.split()
                    if len(parts) >= 9:
                        name = parts[8]
                        full_path = f"{self.bridge_path}/{name}"
                        
                        if parts[0].startswith('d'):
                            # C'est un répertoire
                            if name != '.' and name != '..':
                                sub_analysis = {
                                    "name": name,
                                    "path": full_path,
                                    "has_init": False
                                }
                                
                                # Vérifier __init__.py dans le sous-répertoire
                                init_check_cmd = f"test -f {full_path}/__init__.py"
                                init_success, _, _ = self.run_docker_command(init_check_cmd)
                                sub_analysis["has_init"] = init_success
                                
                                if not init_success:
                                    analysis["missing_inits"].append(name)
                                    analysis["issues"].append(f"__init__.py manquant dans {name}")
                                
                                analysis["subdirectories"].append(sub_analysis)
                        elif name.endswith('.py'):
                            # C'est un fichier Python
                            analysis["python_files"].append({
                                "name": name,
                                "path": full_path,
                                "size": parts[4] if len(parts) > 4 else "unknown"
                            })
        
        # Validation de la structure
        if not analysis["has_init"]:
            analysis["issues"].append("Structure du package invalide: __init__.py manquant")
        
        if analysis["missing_inits"]:
            analysis["issues"].append(f"Structure invalide: {len(analysis['missing_inits'])} __init__.py manquants")
        
        return analysis
    
    def inspect_comfyui_nodes(self) -> Dict[str, Any]:
        """
        Inspection des nodes ComfyUI Qwen
        
        Returns:
            Dictionnaire avec les résultats de l'inspection
        """
        self.log_info("Inspection des nodes ComfyUI...")
        
        inspection = {
            "custom_nodes_path": self.custom_nodes_path,
            "total_nodes": 0,
            "qwen_nodes": 0,
            "nodes_found": [],
            "registration_errors": [],
            "import_errors": []
        }
        
        # Vérifier si le répertoire des nodes existe
        check_cmd = f"test -d {self.custom_nodes_path}"
        success, _, stderr = self.run_docker_command(check_cmd)
        
        if not success:
            inspection["registration_errors"].append(f"Répertoire custom_nodes inaccessible: {self.custom_nodes_path}")
            return inspection
        
        # Lister les fichiers de nodes
        list_cmd = f"find {self.custom_nodes_path} -name '*qwen*.py' -type f 2>/dev/null"
        success, stdout, stderr = self.run_docker_command(list_cmd)
        
        if success:
            if stdout.strip():
                node_files = stdout.strip().split('\n')
                inspection["qwen_nodes"] = len(node_files)
            else:
                node_files = []
        else:
            node_files = []
        
        # Lister tous les nodes pour le comptage
        list_all_cmd = f"find {self.custom_nodes_path} -name '*.py' -type f 2>/dev/null | wc -l"
        success, total_stdout, _ = self.run_docker_command(list_all_cmd)
        if success and total_stdout.strip().isdigit():
            inspection["total_nodes"] = int(total_stdout.strip())
        
        # Inspection détaillée des nodes Qwen
        for node_file in node_files:
            if node_file.strip():
                node_name = os.path.basename(node_file)
                
                # Créer le script d'inspection pour ce node
                inspect_script = f'''
import os
import sys
import importlib.util
import json

def inspect_node():
    """Inspecte un node ComfyUI spécifique"""
    node_path = "{node_file}"
    
    try:
        # Vérifier si le fichier existe
        if not os.path.exists(node_path):
            return {{"error": "Fichier non trouvé", "file": node_path}}
        
        # Charger le module
        spec = importlib.util.spec_from_file_location("temp_node", node_path)
        if spec is None:
            return {{"error": "Impossible de créer le spec", "file": node_path}}
        
        module = importlib.util.module_from_spec(spec)
        if module is None:
            return {{"error": "Impossible de créer le module", "file": node_path}}
        
        # Tenter l'importation
        try:
            importlib.util.exec_module(module)
        except Exception as e:
            return {{"error": f"Erreur import: {{str(e)}}", "file": node_path}}
        
        # Analyser le contenu pour NODE_CLASS_MAPPINGS
        try:
            with open(node_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            has_mappings = "NODE_CLASS_MAPPINGS" in content
            has_init = "__init__.py" in node_path
            
            return {{
                "file": node_path,
                "name": "{node_name}",
                "has_mappings": has_mappings,
                "has_init": has_init,
                "size": len(content),
                "lines": len(content.split('\\n')),
                "importable": True
            }}
        except Exception as e:
            return {{"error": f"Erreur lecture: {{str(e)}}", "file": node_path}}

if __name__ == "__main__":
    result = inspect_node()
    print(json.dumps(result, indent=2))
'''
                
                # Adapter le script selon l'OS
                if platform.system() == "Windows":
                    escaped_script = inspect_script.replace('"', '""').replace("'", "''")
                    create_cmd = f'Set-Content -Path "/tmp/inspect_node.py" -Value @\'\n{escaped_script}\n\' -Force'
                else:
                    escaped_script = inspect_script.replace("'", "'\"'\"'")
                    create_cmd = f"echo '{escaped_script}' > /tmp/inspect_node.py"
                
                success, _, stderr = self.run_docker_command(create_cmd)
                
                if success:
                    # Exécuter le script d'inspection
                    exec_cmd = "python /tmp/inspect_node.py"
                    success, stdout, stderr = self.run_docker_command(exec_cmd)
                    
                    if success:
                        try:
                            result = json.loads(stdout)
                            inspection["nodes_found"].append(result)
                        except json.JSONDecodeError:
                            inspection["import_errors"].append(f"Erreur parsing JSON pour {node_name}: {stdout}")
                    else:
                        inspection["import_errors"].append(f"Erreur exécution inspection {node_name}: {stderr}")
                else:
                    inspection["registration_errors"].append(f"Erreur création script inspection {node_name}: {stderr}")
        
        return inspection
    
    def diagnose_environment(self) -> Dict[str, Any]:
        """
        Diagnostic de l'environnement
        
        Returns:
            Dictionnaire avec les résultats du diagnostic
        """
        self.log_info("Diagnostic de l'environnement...")
        
        diagnosis = {
            "container_accessible": False,
            "python_paths": [],
            "dependencies_check": {},
            "comfyui_connection": False,
            "environment_variables": {},
            "disk_space": {},
            "issues": []
        }
        
        # Test de connectivité avec le container
        diagnosis["container_accessible"] = self.check_container_connectivity()
        
        if not diagnosis["container_accessible"]:
            diagnosis["issues"].append("Container ComfyUI inaccessible")
            return diagnosis
        
        # Vérification des chemins Python
        paths_cmd = "python -c 'import sys; import json; print(json.dumps(sys.path))'"
        success, stdout, stderr = self.run_docker_command(paths_cmd)
        
        if success:
            try:
                diagnosis["python_paths"] = json.loads(stdout)
            except json.JSONDecodeError:
                diagnosis["python_paths"] = stdout.split('\n')
        else:
            diagnosis["issues"].append(f"Erreur récupération chemins Python: {stderr}")
        
        # Validation des dépendances Python
        dependencies = [
            "torch", "torchvision", "transformers", "PIL", "numpy", 
            "folder_paths", "comfy", "comfy.model_management"
        ]
        
        for dep in dependencies:
            test_cmd = f"python -c 'import {dep}; print(\"OK\")'"
            success, stdout, stderr = self.run_docker_command(test_cmd)
            diagnosis["dependencies_check"][dep] = {
                "available": success,
                "error": stderr if not success else None
            }
            
            if not success:
                diagnosis["issues"].append(f"Dépendance manquante: {dep}")
        
        # Test de connexion ComfyUI
        test_comfyui = '''
import sys
sys.path.insert(0, "/workspace/ComfyUI")
try:
    import comfy
    print("ComfyUI accessible")
except ImportError as e:
    print(f"Erreur ComfyUI: {e}")
'''
        
        # Adapter et exécuter le test ComfyUI
        if platform.system() == "Windows":
            escaped_test = test_comfyui.replace('"', '""').replace("'", "''")
            test_cmd = f'Set-Content -Path "/tmp/test_comfyui.py" -Value @\'\n{escaped_test}\n\' -Force && python /tmp/test_comfyui.py'
        else:
            escaped_test = test_comfyui.replace("'", "'\"'\"'")
            test_cmd = f"echo '{escaped_test}' > /tmp/test_comfyui.py && python /tmp/test_comfyui.py"
        
        success, stdout, stderr = self.run_docker_command(test_cmd)
        diagnosis["comfyui_connection"] = success and "ComfyUI accessible" in stdout
        
        if not diagnosis["comfyui_connection"]:
            diagnosis["issues"].append("ComfyUI non accessible depuis le container")
        
        # Variables d'environnement
        env_vars = ["PYTHONPATH", "COMFYUI_PATH", "CUDA_VISIBLE_DEVICES"]
        for var in env_vars:
            if platform.system() == "Windows":
                success, stdout, _ = self.run_docker_command(f"echo $env:{var}")
            else:
                success, stdout, _ = self.run_docker_command(f"echo ${var}")
            
            diagnosis["environment_variables"][var] = stdout.strip() if success else None
        
        # Espace disque (uniquement sur Linux)
        if platform.system() != "Windows":
            disk_cmd = "df -h /workspace"
            success, stdout, stderr = self.run_docker_command(disk_cmd)
            if success:
                lines = stdout.strip().split('\n')
                for line in lines[1:]:  # Skip header
                    if line.strip():
                        parts = line.split()
                        if len(parts) >= 6:
                            diagnosis["disk_space"] = {
                                "filesystem": parts[0],
                                "size": parts[1],
                                "used": parts[2],
                                "available": parts[3],
                                "usage_percent": parts[4],
                                "mount": parts[5]
                            }
        
        return diagnosis
    
    def generate_summary(self) -> Dict[str, Any]:
        """
        Génère le résumé des problèmes identifiés
        
        Returns:
            Dictionnaire avec le résumé
        """
        summary = {
            "total_issues": 0,
            "critical_issues": 0,
            "warnings": 0,
            "recommendations": []
        }
        
        # Analyser la structure du package
        package = self.results["package_structure"]
        if not package.get("exists", False):
            summary["critical_issues"] += 1
            summary["recommendations"].append("Le package ComfyUI-QwenImageWanBridge n'existe pas")
        
        if package.get("missing_inits"):
            summary["warnings"] += len(package["missing_inits"])
            summary["recommendations"].append("Ajouter les fichiers __init__.py manquants")
        
        # Analyser l'inspection des nodes
        nodes = self.results["nodes_inspection"]
        if nodes.get("registration_errors"):
            summary["critical_issues"] += len(nodes["registration_errors"])
            summary["recommendations"].append("Corriger les erreurs d'enregistrement des nodes")
        
        if nodes.get("import_errors"):
            summary["critical_issues"] += len(nodes["import_errors"])
            summary["recommendations"].append("Corriger les erreurs d'importation des nodes")
        
        # Analyser le diagnostic environnement
        env = self.results["environment_diagnostic"]
        if not env.get("container_accessible", False):
            summary["critical_issues"] += 1
            summary["recommendations"].append("Vérifier que le container ComfyUI est en cours d'exécution")
        
        missing_deps = [dep for dep, info in env.get("dependencies_check", {}).items() if not info.get("available", False)]
        if missing_deps:
            summary["critical_issues"] += len(missing_deps)
            summary["recommendations"].append(f"Installer les dépendances manquantes: {', '.join(missing_deps)}")
        
        summary["total_issues"] = summary["critical_issues"] + summary["warnings"]
        
        return summary
    
    def run_diagnostic(self) -> Dict[str, Any]:
        """
        Exécute le diagnostic complet
        
        Returns:
            Dictionnaire avec tous les résultats du diagnostic
        """
        self.log_info("🚀 DÉBUT DU DIAGNOSTIC COMPLET QWEN/COMFYUI")
        self.log_info("=" * 50)
        
        # Timestamp
        from datetime import datetime
        self.results["timestamp"] = datetime.now().isoformat()
        
        # 1. Analyse structurelle des packages
        self.results["package_structure"] = self.analyze_package_structure()
        
        # 2. Inspection des nodes ComfyUI
        self.results["nodes_inspection"] = self.inspect_comfyui_nodes()
        
        # 3. Diagnostic de l'environnement
        self.results["environment_diagnostic"] = self.diagnose_environment()
        
        # 4. Génération du résumé
        self.results["summary"] = self.generate_summary()
        
        return self.results
    
    def print_report(self) -> None:
        """Affiche le rapport de diagnostic"""
        print("\n📋 RAPPORT DE DIAGNOSTIC COMPLET QWEN/COMFYUI")
        print("=" * 50)
        
        # Structure du package
        package = self.results["package_structure"]
        print(f"\n📦 STRUCTURE PACKAGE:")
        print(f"   Fichiers trouvés: {len(package.get('python_files', []))}")
        print(f"   Fichiers manquants: {len(package.get('missing_inits', []))}")
        print(f"   Structure valide: {'✅' if package.get('has_init', False) else '❌'}")
        
        # Nodes ComfyUI
        nodes = self.results["nodes_inspection"]
        print(f"\n🔧 NODES COMFYUI:")
        print(f"   Nodes trouvés: {nodes.get('qwen_nodes', 0)}")
        print(f"   Erreurs d'import: {len(nodes.get('import_errors', []))}")
        print(f"   Erreurs d'enregistrement: {len(nodes.get('registration_errors', []))}")
        
        # Environnement
        env = self.results["environment_diagnostic"]
        print(f"\n🌍 ENVIRONNEMENT:")
        print(f"   Container accessible: {'✅' if env.get('container_accessible', False) else '❌'}")
        print(f"   ComfyUI connecté: {'✅' if env.get('comfyui_connection', False) else '❌'}")
        
        missing_deps = [dep for dep, info in env.get('dependencies_check', {}).items() if not info.get('available', False)]
        print(f"   Dépendances manquantes: {len(missing_deps)}")
        
        # Résumé
        summary = self.results["summary"]
        print(f"\n📊 RÉSUMÉ:")
        print(f"   Problèmes totaux: {summary['total_issues']}")
        print(f"   Problèmes critiques: {summary['critical_issues']}")
        print(f"   Avertissements: {summary['warnings']}")
        
        print(f"\n💡 RECOMMANDATIONS PRINCIPALES:")
        for i, rec in enumerate(summary['recommendations'], 1):
            print(f"   {i}. {rec}")
        
        print("\n" + "=" * 50)
        print("✅ Diagnostic complet terminé")
    
    def save_report(self, output_file: str = None) -> bool:
        """
        Sauvegarde le rapport au format JSON
        
        Args:
            output_file: Chemin du fichier de sortie
            
        Returns:
            True si succès, False sinon
        """
        try:
            if output_file:
                with open(output_file, 'w', encoding='utf-8') as f:
                    json.dump(self.results, f, indent=2, ensure_ascii=False)
                self.log_success(f"Rapport sauvegardé dans: {output_file}")
                return True
            else:
                print(json.dumps(self.results, indent=2, ensure_ascii=False))
                return True
        except Exception as e:
            self.log_error(f"Erreur sauvegarde rapport: {e}")
            return False


def main():
    """Point d'entrée principal"""
    parser = argparse.ArgumentParser(
        description="Script de diagnostic complet pour l'environnement Qwen/ComfyUI",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples:
  python diagnostic-qwen-complete.py                    # Diagnostic avec affichage console
  python diagnostic-qwen-complete.py --verbose          # Diagnostic détaillé
  python diagnostic-qwen-complete.py --output report.json  # Sauvegarde en JSON
  python diagnostic-qwen-complete.py --container my-container  # Container spécifique
        """
    )
    
    parser.add_argument(
        "--container",
        default="comfy-ui-ia",
        help="Nom du container Docker ComfyUI (défaut: comfy-ui-ia)"
    )
    
    parser.add_argument(
        "--output", "-o",
        help="Fichier de sortie pour le rapport JSON (optionnel)"
    )
    
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Mode verbeux avec détails supplémentaires"
    )
    
    args = parser.parse_args()
    
    # Initialiser le diagnostic
    diagnostic = QwenDiagnosticComplete(args.container)
    
    # Exécuter le diagnostic
    results = diagnostic.run_diagnostic()
    
    # Afficher le rapport
    if args.verbose or not args.output:
        diagnostic.print_report()
    
    # Sauvegarder si demandé
    if args.output:
        success = diagnostic.save_report(args.output)
        if not success:
            sys.exit(1)
    
    # Code de sortie basé sur les résultats
    summary = results.get("summary", {})
    if summary.get("critical_issues", 0) > 0:
        sys.exit(2)  # Erreurs critiques
    elif summary.get("total_issues", 0) > 0:
        sys.exit(1)  # Avertissements
    else:
        sys.exit(0)  # Succès


if __name__ == "__main__":
    main()