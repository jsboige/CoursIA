#!/usr/bin/env python3
"""
Script de Validation des Consolidations - Phase Recovery SDDD
Créé: 2025-10-29T23:43:00 CET
Auteur: Roo Code Mode
Mission: Validation des 4 scripts consolidés existants et identification des corrections nécessaires
"""

import os
import sys
import json
import importlib.util
import subprocess
import datetime
from pathlib import Path
from typing import Dict, List, Tuple, Any, Optional

class ConsolidationValidator:
    """Classe principale pour la validation des scripts consolidés"""
    
    def __init__(self, workspace_root: str):
        self.workspace_root = Path(workspace_root)
        self.timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.scripts_path = self.workspace_root / "scripts" / "genai-auth"
        self.results = {
            "timestamp": self.timestamp,
            "workspace_root": str(self.workspace_root),
            "validation_status": "IN_PROGRESS",
            "consolidated_scripts": {},
            "test_results": {},
            "corrections_needed": [],
            "improvements": []
        }
    
    def log(self, message: str, level: str = "INFO"):
        """Fonction de logging structuré"""
        print(f"[{level}] {self.timestamp} - {message}")
    
    def load_script_module(self, script_name: str) -> Optional[Any]:
        """Chargement dynamique d'un script comme module Python"""
        try:
            script_path = self.scripts_path / script_name
            if not script_path.exists():
                self.log(f"Script non trouvé: {script_name}", "ERROR")
                return None
            
            # Chargement du module
            spec = importlib.util.spec_from_file_location(script_name.replace('.py', ''), script_path)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            
            self.log(f"Module chargé: {script_name}")
            return module
        except Exception as e:
            self.log(f"Erreur chargement {script_name}: {str(e)}", "ERROR")
            return None
    
    def validate_diagnostic_qwen_complete(self) -> Dict[str, Any]:
        """Validation du script diagnostic-qwen-complete.py"""
        self.log("Validation de diagnostic-qwen-complete.py...")
        
        validation_result = {
            "script_name": "diagnostic-qwen-complete.py",
            "status": "NOT_TESTED",
            "issues": [],
            "improvements": []
        }
        
        module = self.load_script_module("diagnostic-qwen-complete.py")
        if module is None:
            validation_result["status"] = "LOAD_ERROR"
            validation_result["issues"].append("Impossible de charger le module")
            return validation_result
        
        # Vérification des fonctions requises
        required_functions = ["main", "check_qwen_environment", "validate_qwen_setup"]
        missing_functions = []
        
        for func_name in required_functions:
            if not hasattr(module, func_name):
                missing_functions.append(func_name)
        
        if missing_functions:
            validation_result["status"] = "INCOMPLETE"
            validation_result["issues"].append(f"Fonctions manquantes: {missing_functions}")
        
        # Vérification de la qualité du code
        try:
            script_path = self.scripts_path / "diagnostic-qwen-complete.py"
            with open(script_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Vérifications basiques de qualité
            if "TODO" in content:
                validation_result["issues"].append("Présence de TODO non résolus")
                validation_result["improvements"].append("Résoudre les TODO avant production")
            
            if len(content.splitlines()) < 50:
                validation_result["issues"].append("Script trop court pour un diagnostic complet")
                validation_result["improvements"].append("Ajouter plus de fonctionnalités de diagnostic")
            
            if "import sys" not in content:
                validation_result["issues"].append("Imports manquants")
                validation_result["improvements"].append("Ajouter les imports nécessaires")
        
        except Exception as e:
            validation_result["issues"].append(f"Erreur lecture fichier: {str(e)}")
        
        if not validation_result["issues"]:
            validation_result["status"] = "VALID"
            self.log("diagnostic-qwen-complete.py: VALIDÉ")
        else:
            self.log(f"diagnostic-qwen-complete.py: {validation_result['status']}")
        
        return validation_result
    
    def validate_fix_qwen_workflow(self) -> Dict[str, Any]:
        """Validation du script fix-qwen-workflow.py"""
        self.log("Validation de fix-qwen-workflow.py...")
        
        validation_result = {
            "script_name": "fix-qwen-workflow.py",
            "status": "NOT_TESTED",
            "issues": [],
            "improvements": []
        }
        
        module = self.load_script_module("fix-qwen-workflow.py")
        if module is None:
            validation_result["status"] = "LOAD_ERROR"
            validation_result["issues"].append("Impossible de charger le module")
            return validation_result
        
        # Vérification des fonctions requises
        required_functions = ["main", "fix_workflow_issues", "validate_workflow_structure"]
        missing_functions = []
        
        for func_name in required_functions:
            if not hasattr(module, func_name):
                missing_functions.append(func_name)
        
        if missing_functions:
            validation_result["status"] = "INCOMPLETE"
            validation_result["issues"].append(f"Fonctions manquantes: {missing_functions}")
        
        # Test de la fonction principale si disponible
        if hasattr(module, 'main'):
            try:
                # Simulation d'un test simple
                result = subprocess.run([
                    sys.executable, 
                    str(self.scripts_path / "fix-qwen-workflow.py"),
                    "--help"
                ], capture_output=True, text=True, timeout=10)
                
                if result.returncode == 0:
                    validation_result["status"] = "TESTABLE"
                    self.log("fix-qwen-workflow.py: TESTABLE")
                else:
                    validation_result["issues"].append(f"Erreur exécution --help: {result.stderr}")
            except Exception as e:
                validation_result["issues"].append(f"Erreur test main(): {str(e)}")
        
        if not validation_result["issues"]:
            validation_result["status"] = "VALID"
            self.log("fix-qwen-workflow.py: VALIDÉ")
        else:
            self.log(f"fix-qwen-workflow.py: {validation_result['status']}")
        
        return validation_result
    
    def validate_validate_qwen_solution(self) -> Dict[str, Any]:
        """Validation du script validate-qwen-solution.py"""
        self.log("Validation de validate-qwen-solution.py...")
        
        validation_result = {
            "script_name": "validate-qwen-solution.py",
            "status": "NOT_TESTED",
            "issues": [],
            "improvements": []
        }
        
        module = self.load_script_module("validate-qwen-solution.py")
        if module is None:
            validation_result["status"] = "LOAD_ERROR"
            validation_result["issues"].append("Impossible de charger le module")
            return validation_result
        
        # Vérification des fonctions requises
        required_functions = ["main", "validate_solution", "check_requirements"]
        missing_functions = []
        
        for func_name in required_functions:
            if not hasattr(module, func_name):
                missing_functions.append(func_name)
        
        if missing_functions:
            validation_result["status"] = "INCOMPLETE"
            validation_result["issues"].append(f"Fonctions manquantes: {missing_functions}")
        
        # Vérification de la logique de validation
        if hasattr(module, 'validate_solution'):
            validation_result["improvements"].append("Fonction validate_solution présente")
        else:
            validation_result["issues"].append("Fonction validate_solution manquante")
        
        if not validation_result["issues"]:
            validation_result["status"] = "VALID"
            self.log("validate-qwen-solution.py: VALIDÉ")
        else:
            self.log(f"validate-qwen-solution.py: {validation_result['status']}")
        
        return validation_result
    
    def validate_comfyui_client_helper(self) -> Dict[str, Any]:
        """Validation du script comfyui_client_helper.py"""
        self.log("Validation de comfyui_client_helper.py...")
        
        validation_result = {
            "script_name": "comfyui_client_helper.py",
            "status": "NOT_TESTED",
            "issues": [],
            "improvements": []
        }
        
        module = self.load_script_module("comfyui_client_helper.py")
        if module is None:
            validation_result["status"] = "LOAD_ERROR"
            validation_result["issues"].append("Impossible de charger le module")
            return validation_result
        
        # Vérification des fonctions requises pour un helper ComfyUI
        required_functions = ["ComfyUIClient", "authenticate", "get_workflow", "submit_job"]
        missing_functions = []
        
        for func_name in required_functions:
            if not hasattr(module, func_name):
                missing_functions.append(func_name)
        
        if missing_functions:
            validation_result["status"] = "INCOMPLETE"
            validation_result["issues"].append(f"Fonctions manquantes: {missing_functions}")
        
        # Vérification des imports typiques pour ComfyUI
        try:
            script_path = self.scripts_path / "comfyui_client_helper.py"
            with open(script_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            required_imports = ["requests", "json", "websocket"]
            missing_imports = []
            
            for imp in required_imports:
                if f"import {imp}" not in content and f"from {imp}" not in content:
                    missing_imports.append(imp)
            
            if missing_imports:
                validation_result["issues"].append(f"Imports manquants: {missing_imports}")
                validation_result["improvements"].append(f"Ajouter imports: {', '.join(missing_imports)}")
        
        except Exception as e:
            validation_result["issues"].append(f"Erreur lecture fichier: {str(e)}")
        
        if not validation_result["issues"]:
            validation_result["status"] = "VALID"
            self.log("comfyui_client_helper.py: VALIDÉ")
        else:
            self.log(f"comfyui_client_helper.py: {validation_result['status']}")
        
        return validation_result
    
    def run_validation(self) -> Dict[str, Any]:
        """Exécution complète de la validation des consolidations"""
        self.log("Démarrage de la validation des consolidations...")
        
        # Validation des 4 scripts consolidés
        scripts_to_validate = [
            self.validate_diagnostic_qwen_complete,
            self.validate_fix_qwen_workflow,
            self.validate_validate_qwen_solution,
            self.validate_comfyui_client_helper
        ]
        
        script_names = [
            "diagnostic-qwen-complete.py",
            "fix-qwen-workflow.py", 
            "validate-qwen-solution.py",
            "comfyui_client_helper.py"
        ]
        
        for i, validator in enumerate(scripts_to_validate):
            self.log(f"Validation script {i+1}/4: {script_names[i]}")
            result = validator()
            self.results["consolidated_scripts"][script_names[i]] = result
            self.results["test_results"][script_names[i]] = result["status"]
            
            # Compilation des problèmes et améliorations
            if result["issues"]:
                self.results["corrections_needed"].extend([
                    f"{script_names[i]}: {issue}" for issue in result["issues"]
                ])
            
            if result["improvements"]:
                self.results["improvements"].extend([
                    f"{script_names[i]}: {imp}" for imp in result["improvements"]
                ])
        
        # Finalisation de la validation
        self.results["validation_status"] = "COMPLETED"
        self.log("Validation des consolidations terminée")
        
        return self.results
    
    def save_report(self, output_path: str = None):
        """Sauvegarde du rapport de validation"""
        if output_path is None:
            output_path = self.workspace_root / "docs/suivis/genai-image/phase-recovery-20251029-234009/reports/02-validation-consolidations.json"
        
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.results, f, indent=2, ensure_ascii=False)
        
        self.log(f"Rapport de validation sauvegardé: {output_path}")
        return str(output_path)

def main():
    """Fonction principale d'exécution de la validation"""
    print("🔍 VALIDATION DES CONSOLIDATIONS SDDD - PHASE RECOVERY")
    print("=" * 60)
    
    # Détection du workspace
    workspace_root = os.getcwd()
    print(f"📁 Workspace: {workspace_root}")
    
    # Initialisation et exécution de la validation
    validator = ConsolidationValidator(workspace_root)
    results = validator.run_validation()
    
    # Affichage résumé
    print("\n📊 RÉSUMÉ DE LA VALIDATION:")
    print(f"   Status: {results['validation_status']}")
    print(f"   Scripts validés: {len(results['consolidated_scripts'])}")
    print(f"   Corrections nécessaires: {len(results['corrections_needed'])}")
    print(f"   Améliorations proposées: {len(results['improvements'])}")
    
    # Affichage détaillé par script
    print("\n📋 RÉSULTATS PAR SCRIPT:")
    for script_name, result in results['consolidated_scripts'].items():
        status_emoji = "✅" if result['status'] == 'VALID' else "⚠️" if result['status'] in ['INCOMPLETE', 'TESTABLE'] else "❌"
        print(f"   {status_emoji} {script_name}: {result['status']}")
        
        if result['issues']:
            for issue in result['issues'][:2]:  # Limiter pour lisibilité
                print(f"      • Problème: {issue}")
        
        if result['improvements']:
            for improvement in result['improvements'][:2]:  # Limiter pour lisibilité
                print(f"      💡 Amélioration: {improvement}")
    
    if results['corrections_needed']:
        print(f"\n🔧 CORRECTIONS NÉCESSAIRES ({len(results['corrections_needed'])}):")
        for correction in results['corrections_needed'][:5]:  # Limiter pour lisibilité
            print(f"   • {correction}")
        if len(results['corrections_needed']) > 5:
            print(f"   ... et {len(results['corrections_needed']) - 5} autres")
    
    # Sauvegarde du rapport
    report_path = validator.save_report()
    print(f"\n📄 Rapport détaillé sauvegardé: {report_path}")
    
    print("\n✅ Validation des consolidations SDDD terminée avec succès")
    return 0 if not results['corrections_needed'] else 1

if __name__ == "__main__":
    sys.exit(main())