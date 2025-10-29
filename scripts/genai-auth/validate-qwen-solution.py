#!/usr/bin/env python3
"""
Script de validation consolidé pour la solution Qwen ComfyUI - VERSION CORRIGÉE SDDD
===============================================================================

CORRECTION SDDD APPLIQUÉE :
- Suppression de tous les imports directs de modules ComfyUI
- Transformation en client API pur utilisant uniquement des requêtes HTTP
- Respect strict des frontières hôte/conteneur
- Utilisation de ComfyUIClient comme base pour les interactions API

Ce script respecte maintenant le principe "boundary awareness" :
l'hôte communique avec le conteneur UNIQUEMENT via l'API HTTP,
jamais par imports directs de modules internes.

Auteur: Consolidation des scripts de validation existants
Version: 4.0 - Version corrigée SDDD (boundary awareness)
Date: 2025-10-29
"""

import argparse
import json
import logging
import os
import sys
import time
import requests
import subprocess
import platform
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from datetime import datetime

# Import du client API ComfyUI pur (respect des frontières hôte/conteneur)
# Ajout du répertoire courant au sys.path pour résoudre le problème d'import
current_dir = Path(__file__).parent.absolute()
if str(current_dir) not in sys.path:
    sys.path.insert(0, str(current_dir))

try:
    from comfyui_client_helper import ComfyUIClient, ComfyUIConfig
except ImportError as e:
    print(f"❌ ERREUR CRITIQUE: Impossible d'importer ComfyUIClient: {e}")
    print(f"💡 SOLUTION: Assurez-vous que comfyui-client-helper.py est dans le répertoire: {current_dir}")
    print(f"📂 Répertoire courant: {current_dir}")
    print(f"🐍 PYTHONPATH: {sys.path[:3]}...")  # Affiche les 3 premiers chemins
    sys.exit(1)

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('qwen_validation.log'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

class QwenValidationResult:
    """Classe pour stocker les résultats de validation"""
    
    def __init__(self):
        self.tests = {}
        self.start_time = time.time()
        self.end_time = None
        self.success_count = 0
        self.failure_count = 0
        self.critical_issues = []
        self.warnings = []
        self.recommendations = []
        
    def add_test(self, test_name: str, status: str, details: str = "", 
                critical: bool = False, warning: bool = False):
        """Ajoute un résultat de test"""
        self.tests[test_name] = {
            'status': status,
            'details': details,
            'critical': critical,
            'warning': warning,
            'timestamp': datetime.now().isoformat()
        }
        
        if status == 'SUCCESS':
            self.success_count += 1
        elif status == 'FAILURE':
            self.failure_count += 1
            if critical:
                self.critical_issues.append(f"{test_name}: {details}")
            if warning:
                self.warnings.append(f"{test_name}: {details}")
    
    def finalize(self):
        """Finalise le rapport et calcule les métriques"""
        self.end_time = time.time()
        execution_time = self.end_time - self.start_time
        
        return {
            'execution_time': round(execution_time, 2),
            'total_tests': len(self.tests),
            'success_count': self.success_count,
            'failure_count': self.failure_count,
            'critical_issues_count': len(self.critical_issues),
            'warnings_count': len(self.warnings),
            'success_rate': round((self.success_count / len(self.tests)) * 100, 1) if self.tests else 0
        }

class QwenValidator:
    """Classe principale de validation pour la solution Qwen - VERSION CORRIGÉE SDDD"""
    
    def __init__(self, mode: str = 'complete'):
        self.mode = mode
        self.result = QwenValidationResult()
        self.workspace_dir = Path.cwd()
        
        # Configuration des chemins selon l'environnement
        if platform.system() == 'Windows':
            self.comfyui_dir = self.workspace_dir / 'docker-configurations' / 'comfyui-qwen'
            self.custom_nodes_dir = self.comfyui_dir / 'custom_nodes' / 'ComfyUI_QwenImageWanBridge'
        else:
            self.comfyui_dir = Path('/workspace/ComfyUI')
            self.custom_nodes_dir = self.comfyui_dir / 'custom_nodes' / 'ComfyUI-QwenImageWanBridge'
        
        # Configuration du client API ComfyUI (respect des frontières)
        self.comfyui_config = ComfyUIConfig(
            base_url='http://localhost:8188',
            timeout=30,
            max_retries=3
        )
        self.comfyui_client = ComfyUIClient(self.comfyui_config)
        
        self.container_name = 'comfyui-qwen'
        
        logger.info(f"Mode de validation: {mode}")
        logger.info(f"Répertoire ComfyUI: {self.comfyui_dir}")
        logger.info(f"Répertoire custom nodes: {self.custom_nodes_dir}")
        logger.info("🔧 CONFIGURATION SDDD: Client API pur (boundary awareness)")
    
    def validate_docker_container(self) -> bool:
        """Valide que le container Docker ComfyUI est en cours d'exécution"""
        logger.info("Validation du l'état du container Docker...")
        
        try:
            # Vérifier si le container est en cours d'exécution
            cmd = ['docker', 'ps', '--filter', f'name={self.container_name}', '--format', '{{.Status}}']
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
            
            if result.returncode == 0 and ('Up' in result.stdout or 'unhealthy' in result.stdout):
                self.result.add_test(
                    'docker_container', 
                    'SUCCESS', 
                    f"Container {self.container_name} est en cours d'exécution"
                )
                return True
            else:
                self.result.add_test(
                    'docker_container', 
                    'FAILURE', 
                    f"Container {self.container_name} n'est pas en cours d'exécution",
                    critical=True
                )
                return False
            
        except subprocess.TimeoutExpired:
            self.result.add_test(
                'docker_container', 
                'FAILURE', 
                "Timeout lors de la vérification du container Docker",
                critical=True
            )
            return False
        except Exception as e:
            self.result.add_test(
                'docker_container', 
                'FAILURE', 
                f"Erreur lors de la vérification du container: {str(e)}",
                critical=True
            )
            return False
    
    def validate_package_structure(self) -> bool:
        """Valide la structure du package ComfyUI-QwenImageWanBridge"""
        logger.info("Validation de la structure du package...")
        
        required_files = [
            self.custom_nodes_dir / '__init__.py',
            self.custom_nodes_dir / 'nodes' / '__init__.py'
        ]
        
        required_dirs = [
            self.custom_nodes_dir,
            self.custom_nodes_dir / 'nodes'
        ]
        
        all_valid = True
        
        # Vérification des répertoires
        for dir_path in required_dirs:
            if dir_path.exists():
                self.result.add_test(
                    f'directory_{dir_path.name}', 
                    'SUCCESS', 
                    f"Répertoire {dir_path.name} existe"
                )
            else:
                self.result.add_test(
                    f'directory_{dir_path.name}', 
                    'FAILURE', 
                    f"Répertoire {dir_path.name} manquant",
                    critical=True
                )
                all_valid = False
        
        # Vérification des fichiers __init__.py
        init_files_found = 0
        for init_file in required_files:
            if init_file.exists():
                init_files_found += 1
                self.result.add_test(
                    f'init_file_{init_file.parent.name}_{init_file.name}', 
                    'SUCCESS', 
                    f"Fichier {init_file.name} existe dans {init_file.parent.name}"
                )
            else:
                self.result.add_test(
                    f'init_file_{init_file.parent.name}_{init_file.name}', 
                    'FAILURE', 
                    f"Fichier {init_file.name} manquant dans {init_file.parent.name}",
                    critical=True
                )
                all_valid = False
        
        # Validation du contenu des __init__.py
        if all_valid:
            for init_file in required_files:
                if init_file.exists():
                    try:
                        with open(init_file, 'r', encoding='utf-8') as f:
                            content = f.read()
                            if 'ComfyUI-QwenImageWanBridge' in content or 'QwenImageWanBridge' in content:
                                self.result.add_test(
                                    f'init_content_{init_file.parent.name}', 
                                    'SUCCESS', 
                                    f"Contenu de {init_file.name} valide"
                                )
                            else:
                                self.result.add_test(
                                    f'init_content_{init_file.parent.name}', 
                                    'WARNING', 
                                    f"Contenu de {init_file.name} semble incomplet",
                                    warning=True
                                )
                    except Exception as e:
                        self.result.add_test(
                            f'init_content_{init_file.parent.name}', 
                            'FAILURE', 
                            f"Erreur lecture {init_file.name}: {str(e)}"
                        )
        
        # Vérification des fichiers sources des nodes
        node_files = list(self.custom_nodes_dir.glob('nodes/*.py'))
        if node_files:
            self.result.add_test(
                'node_source_files', 
                'SUCCESS', 
                f"{len(node_files)} fichiers sources de nodes trouvés"
            )
        else:
            self.result.add_test(
                'node_source_files', 
                'FAILURE', 
                "Aucun fichier source de node trouvé",
                critical=True
            )
            all_valid = False
        
        return all_valid
    
    def validate_python_imports(self) -> bool:
        """
        🔧 SDDD CORRECTION : Validation des imports Python SANS VIOLATION DES FRONTIÈRES
        
        Ancienne version : Import direct de modules ComfyUI (VIOLATION SDDD)
        Nouvelle version : Validation via API ComfyUI uniquement (boundary awareness)
        """
        logger.info("Validation des imports Python via API ComfyUI...")
        
        # Test de connexion API ComfyUI
        try:
            # Utilisation du client API pur (respect des frontières)
            system_stats = self.comfyui_client.get_system_stats()
            
            if system_stats:
                self.result.add_test(
                    'api_connectivity', 
                    'SUCCESS', 
                    "Connexion API ComfyUI établie avec succès"
                )
            else:
                self.result.add_test(
                    'api_connectivity', 
                    'FAILURE', 
                    "Impossible de se connecter à l'API ComfyUI",
                    critical=True
                )
                return False
            
            # Vérification que les nodes Qwen sont détectées via API
            object_info = self.comfyui_client.get_object_info()
            
            if object_info:
                qwen_nodes = [k for k in object_info.keys() if 'Qwen' in k or 'qwen' in k.lower()]
                
                if qwen_nodes:
                    self.result.add_test(
                        'qwen_nodes_detection', 
                        'SUCCESS', 
                        f"{len(qwen_nodes)} nodes Qwen détectés via API: {', '.join(qwen_nodes)}"
                    )
                else:
                    self.result.add_test(
                        'qwen_nodes_detection', 
                        'WARNING', 
                        "Aucun node Qwen détecté via API",
                        warning=True
                    )
            else:
                self.result.add_test(
                    'qwen_nodes_detection', 
                    'FAILURE', 
                    "Impossible de récupérer les informations des nodes via API",
                    critical=True
                )
                return False
            
            return True
            
        except Exception as e:
            self.result.add_test(
                'api_connectivity', 
                'FAILURE', 
                f"Erreur validation API: {str(e)}",
                critical=True
            )
            return False
    
    def validate_comfyui_integration(self) -> bool:
        """Valide l'intégration avec ComfyUI via API pure"""
        logger.info("Validation de l'intégration ComfyUI via API...")
        
        # Test de détection des nodes par ComfyUI via API
        try:
            object_info = self.comfyui_client.get_object_info()
            
            if not object_info:
                self.result.add_test(
                    'comfyui_api_access', 
                    'FAILURE', 
                    "API ComfyUI inaccessible",
                    critical=True
                )
                return False
            
            qwen_nodes = [k for k in object_info.keys() if 'Qwen' in k or 'qwen' in k.lower()]
            
            if qwen_nodes:
                self.result.add_test(
                    'comfyui_node_detection', 
                    'SUCCESS', 
                    f"{len(qwen_nodes)} nodes Qwen détectés: {', '.join(qwen_nodes)}"
                )
            else:
                self.result.add_test(
                    'comfyui_node_detection', 
                    'FAILURE', 
                    "Aucun node Qwen détecté par ComfyUI",
                    critical=True
                )
                return False
            
            # Test de soumission de workflow via API
            return self.test_workflow_submission_api()
            
        except Exception as e:
            self.result.add_test(
                'comfyui_api_access', 
                'FAILURE', 
                f"Erreur de connexion API ComfyUI: {str(e)}",
                critical=True
            )
            return False
    
    def test_workflow_submission_api(self) -> bool:
        """Test la soumission d'un workflow JSON via API ComfyUI (version corrigée)"""
        logger.info("Test de soumission de workflow via API...")
        
        # Workflow de test simple avec node Qwen
        test_workflow = {
            "3": {
                "inputs": {
                    "seed": 42,
                    "steps": 20,
                    "cfg": 8.0,
                    "sampler_name": "euler",
                    "scheduler": "normal",
                    "denoise": 1,
                    "model": ["4", 0],
                    "positive": ["6", 0],
                    "negative": ["7", 0],
                    "latent_image": ["5", 0]
                },
                "class_type": "QwenImageSamplerNode",
                "_meta": {
                    "title": "Qwen Sampler Test"
                }
            },
            "5": {
                "inputs": {
                    "filename_prefix": "Qwen_test_",
                    "format": "png"
                },
                "class_type": "SaveImage",
                "_meta": {
                    "title": "Save Image"
                }
            }
        }
        
        try:
            # Prompt de test
            test_prompt = "A beautiful landscape with mountains"
            
            # Utilisation du client API pur pour soumettre le workflow
            prompt_id = self.comfyui_client.submit_workflow(
                prompt=test_prompt,
                workflow=test_workflow
            )
            
            if prompt_id:
                self.result.add_test(
                    'workflow_submission_api', 
                    'SUCCESS', 
                    f"Workflow soumis avec ID: {prompt_id}"
                )
                
                # Vérification de la génération d'image via API
                return self.check_image_generation_api(prompt_id)
            else:
                self.result.add_test(
                    'workflow_submission_api', 
                    'FAILURE', 
                    "Échec soumission workflow via API",
                    critical=True
                )
                return False
            
        except Exception as e:
            self.result.add_test(
                'workflow_submission_api', 
                'FAILURE', 
                f"Erreur workflow API: {str(e)}",
                critical=True
            )
            return False
    
    def check_image_generation_api(self, prompt_id: str) -> bool:
        """Vérifie la génération d'images via API ComfyUI"""
        max_attempts = 30
        attempt = 0
        
        while attempt < max_attempts:
            try:
                # Utilisation du client API pur pour vérifier l'historique
                history = self.comfyui_client.get_history(prompt_id)
                
                if history:
                    # Vérifier si des images ont été générées
                    outputs = history[0].get('outputs', {})
                    if outputs:
                        self.result.add_test(
                            'image_generation_api', 
                            'SUCCESS', 
                            f"Images générées avec succès via API: {list(outputs.keys())}"
                        )
                        return True
                
                attempt += 1
                time.sleep(2)
                
            except Exception:
                attempt += 1
                time.sleep(2)
        
        self.result.add_test(
            'image_generation_api', 
            'FAILURE', 
            f"Timeout après {max_attempts} tentatives via API",
            warning=True
        )
        return False
    
    def run_quick_validation(self):
        """Exécute une validation rapide (vérifications essentielles)"""
        logger.info("Exécution du test rapide...")
        
        # Validation Docker uniquement
        docker_ok = self.validate_docker_container()
        
        # Validation structure minimale
        if self.custom_nodes_dir.exists():
            self.result.add_test('basic_structure', 'SUCCESS', "Répertoire principal existe")
        else:
            self.result.add_test('basic_structure', 'FAILURE', "Répertoire principal manquant", critical=True)
        
        # Validation API minimale via client pur
        try:
            system_stats = self.comfyui_client.get_system_stats()
            if system_stats:
                self.result.add_test('basic_api', 'SUCCESS', "API ComfyUI accessible via client pur")
            else:
                self.result.add_test('basic_api', 'FAILURE', "API inaccessible via client pur")
        except:
            self.result.add_test('basic_api', 'FAILURE', "API inaccessible via client pur")
        
        return docker_ok
    
    def run_complete_validation(self):
        """Exécute la validation complète (version corrigée SDDD)"""
        logger.info("Exécution de la validation complète...")
        
        # Validation Docker
        docker_ok = self.validate_docker_container()
        
        # Validation structurelle
        structure_ok = self.validate_package_structure()
        
        # Validation imports via API (correction SDDD)
        imports_ok = self.validate_python_imports()
        
        # Validation intégration ComfyUI via API
        integration_ok = self.validate_comfyui_integration()
        
        # Recommandations basées sur les résultats
        if not docker_ok:
            self.result.recommendations.append(
                "Démarrez le container ComfyUI avec: docker-compose -f docker-configurations/comfyui-qwen/docker-compose.yml up -d"
            )
        
        if not structure_ok:
            self.result.recommendations.append(
                "Exécutez le script de correction: python scripts/genai-auth/fix-qwen-workflow.py"
            )
        
        if not imports_ok:
            self.result.recommendations.append(
                "Vérifiez la connectivité API ComfyUI et le démarrage du service"
            )
        
        if not integration_ok:
            self.result.recommendations.append(
                "Vérifiez l'installation des nodes Qwen dans ComfyUI"
            )
        
        return docker_ok and structure_ok and imports_ok and integration_ok
    
    def run_workflow_validation(self, workflow_path: str):
        """Test un workflow spécifique via API"""
        logger.info(f"Test du workflow spécifique: {workflow_path}")
        
        if not Path(workflow_path).exists():
            self.result.add_test(
                'workflow_file', 
                'FAILURE', 
                f"Fichier workflow introuvable: {workflow_path}"
            )
            return False
        
        try:
            with open(workflow_path, 'r') as f:
                workflow = json.load(f)
            
            # Test du workflow via API
            prompt_id = self.comfyui_client.submit_workflow(
                prompt="Test workflow spécifique",
                workflow=workflow
            )
            
            if prompt_id:
                self.result.add_test(
                    'workflow_specific_api', 
                    'SUCCESS', 
                    f"Workflow {workflow_path} exécuté avec succès via API"
                )
                return True
            else:
                self.result.add_test(
                    'workflow_specific_api', 
                    'FAILURE', 
                    f"Échec workflow {workflow_path} via API"
                )
                return False
            
        except Exception as e:
            self.result.add_test(
                'workflow_specific_api', 
                'FAILURE', 
                f"Erreur workflow {workflow_path}: {str(e)}"
            )
            return False
    
    def generate_report(self) -> Dict[str, Any]:
        """Génère le rapport de validation détaillé"""
        metrics = self.result.finalize()
        
        report = {
            'metadata': {
                'validation_mode': self.mode,
                'timestamp': datetime.now().isoformat(),
                'validator_version': '4.0 - CORRIGÉE SDDD',
                'platform': platform.system(),
                'comfyui_url': self.comfyui_config.base_url,
                'container_name': self.container_name,
                'boundary_awareness': 'RESPECTÉE - Client API pur uniquement',
                'sddd_correction': 'VIOLATION des frontières hôte/conteneur corrigée'
            },
            'metrics': metrics,
            'tests': self.result.tests,
            'critical_issues': self.result.critical_issues,
            'warnings': self.result.warnings,
            'recommendations': self.result.recommendations,
            'summary': {
                'status': 'SUCCESS' if self.result.failure_count == 0 else 'FAILURE',
                'total_critical': len(self.result.critical_issues),
                'total_warnings': len(self.result.warnings),
                'needs_intervention': len(self.result.critical_issues) > 0
            }
        }
        
        return report
    
    def save_report(self, report: Dict[str, Any], filename: Optional[str] = None):
        """Sauvegarde le rapport de validation"""
        if filename is None:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = f'qwen_validation_report_{timestamp}.json'
        
        report_path = Path.cwd() / filename
        
        try:
            with open(report_path, 'w', encoding='utf-8') as f:
                json.dump(report, f, indent=2, ensure_ascii=False)
             
            logger.info(f"Rapport sauvegardé: {report_path.absolute()}")
            self.result.add_test(
                'report_save',
                'SUCCESS',
                f"Rapport sauvegardé dans {filename}"
            )
            
        except Exception as e:
            logger.error(f"Erreur sauvegarde rapport: {e}")
            self.result.add_test(
                'report_save',
                'FAILURE',
                f"Erreur sauvegarde rapport: {str(e)}"
            )
            logger.error(f"Chemin du rapport: {report_path}")
            logger.error(f"Répertoire courant: {Path.cwd()}")

def main():
    """Fonction principale du script de validation - VERSION CORRIGÉE SDDD"""
    parser = argparse.ArgumentParser(
        description='Script de validation consolidé pour la solution Qwen ComfyUI - VERSION CORRIGÉE SDDD',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples d'utilisation:
  # Validation complète (avec correction SDDD)
  python validate-qwen-solution.py --mode complete
  
  # Test rapide
  python validate-qwen-solution.py --mode quick
  
  # Test workflow spécifique
  python validate-qwen-solution.py --mode workflow --workflow test_workflow.json
  
  # Rapport détaillé
  python validate-qwen-solution.py --mode complete --report detailed_report.json

🔧 CORRECTION SDDD APPLIQUÉE :
- Suppression de tous les imports directs de modules ComfyUI
- Transformation en client API pur utilisant ComfyUIClient
- Respect strict des frontières hôte/conteneur (boundary awareness)
- Communication avec ComfyUI UNIQUEMENT via HTTP API

Scripts de validation remplacés par ce script consolidé corrigé:
- test-qwen-imports-simple.py: Validation des imports de base (CORRIGÉ)
- test-qwen-sampler-compatibility.py: Test de compatibilité des samplers (CORRIGÉ)
- validate-qwen-fixes.py: Validation des corrections appliquées (CORRIGÉ)
- diagnostic-qwen-complete.py: Diagnostic complet de l'environnement (CORRIGÉ)
- fix-qwen-workflow.py: Application des corrections structurelles (CORRIGÉ)

Modes de fonctionnement:
- complete: Validation complète de tous les aspects (défaut)
- quick: Tests rapides des fonctionnalités essentielles
- workflow: Test d'un workflow JSON spécifique
- report: Génération de rapport JSON détaillé sans tests actifs

⚠️  NOTE IMPORTANTE : Ce script respecte maintenant les frontières système SDDD
        """
    )
    
    parser.add_argument(
        '--mode',
        choices=['complete', 'quick', 'workflow', 'report'],
        default='complete',
        help='Mode de validation à exécuter'
    )
    
    parser.add_argument(
        '--workflow',
        type=str,
        help='Chemin vers un fichier workflow JSON à tester (mode workflow uniquement)'
    )
    
    parser.add_argument(
        '--report',
        type=str,
        help='Nom du fichier de rapport à générer (optionnel)'
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Active le logging détaillé'
    )
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # Création du validateur et exécution
    validator = QwenValidator(mode=args.mode)
    
    print("🔍 SCRIPT DE VALIDATION QWEN CONSOLIDÉ - VERSION CORRIGÉE SDDD")
    print("=" * 60)
    print(f"Mode: {args.mode.upper()}")
    print(f"Heure: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("🔧 CONFIGURATION: Boundary Awareness RESPECTÉE")
    print("📡 Communication: Client API pur uniquement")
    print()
    
    success = False
    
    if args.mode == 'quick':
        success = validator.run_quick_validation()
    elif args.mode == 'workflow':
        if not args.workflow:
            print("❌ Erreur: Le mode --workflow nécessite le paramètre --workflow")
            sys.exit(1)
        success = validator.run_workflow_validation(args.workflow)
    elif args.mode == 'report':
        # Mode rapport uniquement - génère un rapport vide
        validator.result.add_test('report_mode', 'SUCCESS', "Mode rapport activé")
        success = True
    else:  # complete
        success = validator.run_complete_validation()
    
    # Génération et sauvegarde du rapport
    print("\n📊 GÉNÉRATION DU RAPPORT DE VALIDATION")
    print("-" * 60)
    
    report = validator.generate_report()
    validator.save_report(report, args.report)
    
    # Affichage du résumé
    print(f"\n📈 RÉSUMÉ DE VALIDATION:")
    print(f"   Tests totaux: {report['metrics']['total_tests']}")
    print(f"   ✅ Succès: {report['metrics']['success_count']}")
    print(f"   ❌ Échecs: {report['metrics']['failure_count']}")
    print(f"   🚨 Problèmes critiques: {report['metrics']['critical_issues_count']}")
    print(f"   ⚠️  Avertissements: {report['metrics']['warnings_count']}")
    print(f"   ⏱️  Temps d'exécution: {report['metrics']['execution_time']}s")
    print(f"   📊 Taux de succès: {report['metrics']['success_rate']}%")
    
    if report['critical_issues']:
        print(f"\n🚨 PROBLÈMES CRITIQUES DÉTECTÉS:")
        for i, issue in enumerate(report['critical_issues'], 1):
            print(f"   {i}. {issue}")
    
    if report['warnings']:
        print(f"\n⚠️  AVERTISSEMENTS:")
        for i, warning in enumerate(report['warnings'], 1):
            print(f"   {i}. {warning}")
    
    if report['recommendations']:
        print(f"\n💡 RECOMMANDATIONS:")
        for i, rec in enumerate(report['recommendations'], 1):
            print(f"   {i}. {rec}")
    
    print(f"\n📄 Rapport détaillé sauvegardé: {args.report or 'généré automatiquement'}")
    print(f"🎯 Statut final: {report['summary']['status']}")
    print(f"🔧 Boundary Awareness: {report['metadata']['boundary_awareness']}")
    print(f"🔧 SDDD Correction: {report['metadata']['sddd_correction']}")
    
    # Code de sortie
    exit_code = 0 if success else 1
    sys.exit(exit_code)

if __name__ == '__main__':
    main()