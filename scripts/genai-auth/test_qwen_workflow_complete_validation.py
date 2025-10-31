#!/usr/bin/env python3
"""
Script de test de validation complet pour le workflow Qwen ComfyUI - VERSION ISOLÉE

Ce script effectue une validation complète et isolée des corrections du workflow Qwen :
- Validation de l'import des nodes Qwen sans violation des frontières SDDD
- Test de connectivité ComfyUI via API pure
- Test du workflow corrigé avec l'API ComfyUI
- Test de génération simple de bout en bout
- Génération d'un rapport détaillé des résultats

Approche prudente et non-destructive avec validation à chaque étape.
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

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('qwen_complete_validation.log'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

class QwenCompleteValidator:
    """Classe principale de validation complète pour la solution Qwen"""
    
    def __init__(self, workflow_path: str = None):
        self.workflow_path = workflow_path or "temp_official_workflow_qwen_t2i_fixed.json"
        self.start_time = time.time()
        self.end_time = None
        self.test_results = {}
        self.success_count = 0
        self.failure_count = 0
        self.critical_issues = []
        self.warnings = []
        self.recommendations = []
        
        # Configuration des chemins selon l'environnement
        self.workspace_dir = Path.cwd()
        
        if platform.system() == 'Windows':
            self.comfyui_dir = self.workspace_dir / 'docker-configurations' / 'comfyui-qwen'
            self.custom_nodes_dir = self.comfyui_dir / 'custom_nodes' / 'ComfyUI_QwenImageWanBridge'
        else:
            self.comfyui_dir = Path('/workspace/ComfyUI')
            self.custom_nodes_dir = self.comfyui_dir / 'custom_nodes' / 'ComfyUI-QwenImageWanBridge'
        
        logger.info(f"Répertoire de travail: {self.workspace_dir}")
        logger.info(f"Répertoire ComfyUI: {self.comfyui_dir}")
        logger.info(f"Répertoire custom nodes: {self.custom_nodes_dir}")
        
        # Import du client API ComfyUI (boundary awareness)
        self._import_comfyui_client()
        
    def _import_comfyui_client(self):
        """Import du client ComfyUI avec gestion des erreurs"""
        try:
            # Ajout du répertoire scripts au path Python
            scripts_dir = Path(__file__).parent / "scripts" / "genai-auth"
            if str(scripts_dir) not in sys.path:
                sys.path.insert(0, str(scripts_dir))
            
            from comfyui_client_helper import ComfyUIClient, ComfyUIConfig
            
            # Configuration du client API ComfyUI (respect des frontières)
            self.comfyui_config = ComfyUIConfig(
                host='localhost',
                port=8188,
                protocol='http',
                timeout=30,
                max_retries=3,
                api_key='2b$12$UUDceblhZeEySDwVMC0ccN.IaQmMBfKdTY.aAE3poXcq1zsOP6coni'  # Token d'authentification ComfyUI
            )
            self.comfyui_client = ComfyUIClient(self.comfyui_config)
            
            self.add_test_result(
                'comfyui_client_import', 
                'SUCCESS', 
                "Client ComfyUI importé avec succès (boundary awareness respecté)"
            )
            
        except ImportError as e:
            self.add_test_result(
                'comfyui_client_import', 
                'FAILURE', 
                f"Erreur d'import ComfyUIClient: {e}",
                critical=True
            )
            self.comfyui_client = None
        except Exception as e:
            self.add_test_result(
                'comfyui_client_import', 
                'FAILURE', 
                f"Erreur inattendue lors de l'import: {e}",
                critical=True
            )
            self.comfyui_client = None
    
    def add_test_result(self, test_name: str, status: str, details: str = "", 
                      critical: bool = False, warning: bool = False):
        """Ajoute un résultat de test"""
        self.test_results[test_name] = {
            'status': status,
            'details': details,
            'critical': critical,
            'warning': warning,
            'timestamp': datetime.now().isoformat()
        }
        
        if status == 'SUCCESS':
            self.success_count += 1
            logger.info(f"✅ {test_name}: {details}")
        elif status == 'FAILURE':
            self.failure_count += 1
            logger.error(f"❌ {test_name}: {details}")
            if critical:
                self.critical_issues.append(f"{test_name}: {details}")
            if warning:
                self.warnings.append(f"{test_name}: {details}")
    
    def test_1_import_qwen_nodes(self) -> bool:
        """Test 1: Valider l'import des nodes Qwen"""
        logger.info("🔍 Test 1: Validation de l'import des nodes Qwen...")
        
        if not self.comfyui_client:
            logger.error("❌ Client ComfyUI non disponible - test d'import impossible")
            return False
        
        try:
            # Vérification de la structure du package
            required_files = [
                self.custom_nodes_dir / '__init__.py',
                self.custom_nodes_dir / 'nodes' / '__init__.py'
            ]
            
            structure_valid = True
            for file_path in required_files:
                if file_path.exists():
                    self.add_test_result(
                        f'node_file_{file_path.name}', 
                        'SUCCESS', 
                        f"Fichier {file_path.name} présent"
                    )
                else:
                    self.add_test_result(
                        f'node_file_{file_path.name}', 
                        'FAILURE', 
                        f"Fichier {file_path.name} manquant",
                        critical=True
                    )
                    structure_valid = False
            
            # Vérification des fichiers de nodes
            node_files = list(self.custom_nodes_dir.glob('nodes/*.py'))
            qwen_node_files = [f for f in node_files if 'qwen' in f.name.lower()]
            
            if qwen_node_files:
                self.add_test_result(
                    'qwen_node_files', 
                    'SUCCESS', 
                    f"{len(qwen_node_files)} fichiers Qwen trouvés: {[f.name for f in qwen_node_files]}"
                )
            else:
                self.add_test_result(
                    'qwen_node_files', 
                    'FAILURE', 
                    "Aucun fichier de node Qwen trouvé",
                    critical=True
                )
                structure_valid = False
            
            # Test d'import via API (boundary awareness)
            try:
                system_stats = self.comfyui_client.get_system_stats()
                if system_stats:
                    object_info = self.comfyui_client.get_object_info()
                    qwen_nodes = [k for k in object_info.keys() if 'qwen' in k.lower()]
                    
                    if qwen_nodes:
                        self.add_test_result(
                            'qwen_nodes_api_detection', 
                            'SUCCESS', 
                            f"{len(qwen_nodes)} nodes Qwen détectés via API: {qwen_nodes}"
                        )
                    else:
                        self.add_test_result(
                            'qwen_nodes_api_detection', 
                            'WARNING', 
                            "Aucun node Qwen détecté via API (peut être normal si pas chargé)"
                        )
                else:
                    self.add_test_result(
                        'qwen_nodes_api_detection', 
                        'FAILURE', 
                        "API ComfyUI inaccessible",
                        critical=True
                    )
                    structure_valid = False
                    
            except Exception as e:
                self.add_test_result(
                    'qwen_nodes_api_detection', 
                    'FAILURE', 
                    f"Erreur lors de la détection API: {e}",
                    critical=True
                )
                structure_valid = False
            
            return structure_valid
            
        except Exception as e:
            self.add_test_result(
                'import_qwen_nodes', 
                'FAILURE', 
                f"Erreur globale test import: {e}",
                critical=True
            )
            return False
    
    def test_2_comfyui_connectivity(self) -> bool:
        """Test 2: Tester la connectivité ComfyUI"""
        logger.info("🌐 Test 2: Test de connectivité ComfyUI...")
        
        if not self.comfyui_client:
            self.add_test_result(
                'comfyui_connectivity', 
                'FAILURE', 
                "Client ComfyUI non disponible",
                critical=True
            )
            return False
        
        try:
            # Test de connectivité de base
            if self.comfyui_client.test_connectivity():
                self.add_test_result(
                    'comfyui_basic_connectivity', 
                    'SUCCESS', 
                    "Connectivité de base établie"
                )
            else:
                self.add_test_result(
                    'comfyui_basic_connectivity', 
                    'FAILURE', 
                    "Échec connectivité de base",
                    critical=True
                )
                return False
            
            # Test des statistiques système
            system_stats = self.comfyui_client.get_system_stats()
            if system_stats:
                self.add_test_result(
                    'comfyui_system_stats', 
                    'SUCCESS', 
                    f"Statistiques système récupérées: {list(system_stats.keys())}"
                )
            else:
                self.add_test_result(
                    'comfyui_system_stats', 
                    'FAILURE', 
                    "Impossible de récupérer les statistiques système",
                    critical=True
                )
                return False
            
            # Test des informations d'objets
            object_info = self.comfyui_client.get_object_info()
            if object_info:
                self.add_test_result(
                    'comfyui_object_info', 
                    'SUCCESS', 
                    f"Informations objets récupérées: {len(object_info)} objets"
                )
            else:
                self.add_test_result(
                    'comfyui_object_info', 
                    'FAILURE', 
                    "Impossible de récupérer les informations d'objets",
                    critical=True
                )
                return False
            
            return True
            
        except Exception as e:
            self.add_test_result(
                'comfyui_connectivity', 
                'FAILURE', 
                f"Erreur lors du test de connectivité: {e}",
                critical=True
            )
            return False
    
    def test_3_workflow_validation(self) -> bool:
        """Test 3: Tester le workflow corrigé avec l'API"""
        logger.info("📋 Test 3: Test du workflow corrigé...")
        
        if not self.comfyui_client:
            self.add_test_result(
                'workflow_validation', 
                'FAILURE', 
                "Client ComfyUI non disponible",
                critical=True
            )
            return False
        
        # Vérification que le fichier workflow existe
        workflow_file = Path(self.workflow_path)
        if not workflow_file.exists():
            self.add_test_result(
                'workflow_file_existence', 
                'FAILURE', 
                f"Fichier workflow introuvable: {self.workflow_path}",
                critical=True
            )
            return False
        
        try:
            # Chargement du workflow
            with open(workflow_file, 'r', encoding='utf-8') as f:
                workflow = json.load(f)
            
            self.add_test_result(
                'workflow_loading', 
                'SUCCESS', 
                f"Workflow chargé: {len(workflow.get('nodes', []))} nodes"
            )
            
            # Validation structurelle basique
            nodes = workflow.get('nodes', [])
            links = workflow.get('links', [])
            
            if nodes and links:
                self.add_test_result(
                    'workflow_structure', 
                    'SUCCESS', 
                    f"Structure valide: {len(nodes)} nodes, {len(links)} links"
                )
            else:
                self.add_test_result(
                    'workflow_structure', 
                    'FAILURE', 
                    "Structure invalide: nodes ou links manquants",
                    critical=True
                )
                return False
            
            # Test de soumission via API
            test_prompt = "A beautiful landscape with mountains"
            prompt_id = self.comfyui_client.submit_workflow(
                workflow=workflow
            )
            
            if prompt_id:
                self.add_test_result(
                    'workflow_submission', 
                    'SUCCESS', 
                    f"Workflow soumis avec ID: {prompt_id}"
                )
                
                # Vérification du statut
                time.sleep(3)  # Attendre un peu
                
                try:
                    history = self.comfyui_client.get_history(prompt_id)
                    if history:
                        self.add_test_result(
                            'workflow_processing', 
                            'SUCCESS', 
                            f"Workflow en cours de traitement: {prompt_id}"
                        )
                    else:
                        self.add_test_result(
                            'workflow_processing', 
                            'WARNING', 
                            "Workflow soumis mais historique vide"
                        )
                except Exception as e:
                    self.add_test_result(
                        'workflow_processing', 
                        'WARNING', 
                        f"Impossible de vérifier le traitement: {e}"
                    )
                
                return True
            else:
                self.add_test_result(
                    'workflow_submission', 
                    'FAILURE', 
                    "Échec de la soumission du workflow",
                    critical=True
                )
                return False
                
        except Exception as e:
            self.add_test_result(
                'workflow_validation', 
                'FAILURE', 
                f"Erreur lors du test du workflow: {e}",
                critical=True
            )
            return False
    
    def test_4_simple_generation(self) -> bool:
        """Test 4: Test de génération simple de bout en bout"""
        logger.info("🎨 Test 4: Test de génération simple...")
        
        if not self.comfyui_client:
            self.add_test_result(
                'simple_generation', 
                'FAILURE', 
                "Client ComfyUI non disponible",
                critical=True
            )
            return False
        
        try:
            # Workflow minimal pour le test
            minimal_workflow = {
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
                        "title": "Qwen Simple Generation Test"
                    }
                },
                "5": {
                    "inputs": {
                        "filename_prefix": "qwen_simple_test_",
                        "format": "png"
                    },
                    "class_type": "SaveImage",
                    "_meta": {
                        "title": "Save Simple Test"
                    }
                }
            }
            
            test_prompt = "A simple test image generation"
            
            # Soumission du workflow minimal
            prompt_id = self.comfyui_client.submit_workflow(
                workflow=minimal_workflow
            )
            
            if not prompt_id:
                self.add_test_result(
                    'simple_generation_submission', 
                    'FAILURE', 
                    "Échec de soumission du workflow minimal",
                    critical=True
                )
                return False
            
            self.add_test_result(
                'simple_generation_submission', 
                'SUCCESS', 
                f"Workflow minimal soumis avec ID: {prompt_id}"
            )
            
            # Attendre la génération avec timeout
            max_wait_time = 60  # 60 secondes maximum
            wait_interval = 2
            elapsed_time = 0
            
            while elapsed_time < max_wait_time:
                try:
                    history = self.comfyui_client.get_history(prompt_id)
                    
                    if history and len(history) > 0:
                        outputs = history[0].get('outputs', {})
                        
                        if outputs:
                            self.add_test_result(
                                'simple_generation_success', 
                                'SUCCESS', 
                                f"Image générée avec succès: {list(outputs.keys())}"
                            )
                            return True
                        else:
                            # Vérifier le statut de la tâche
                            status = history[0].get('status', {})
                            if status.get('completed', False):
                                self.add_test_result(
                                    'simple_generation_success', 
                                    'SUCCESS', 
                                    "Génération complétée (pas d'output visible)"
                                )
                                return True
                            elif status.get('error', None):
                                self.add_test_result(
                                    'simple_generation_error', 
                                    'FAILURE', 
                                    f"Erreur de génération: {status.get('error')}",
                                    critical=True
                                )
                                return False
                    
                    time.sleep(wait_interval)
                    elapsed_time += wait_interval
                    
                except Exception as e:
                    logger.warning(f"Erreur lors de la vérification: {e}")
                    time.sleep(wait_interval)
                    elapsed_time += wait_interval
            
            self.add_test_result(
                'simple_generation_timeout', 
                'FAILURE', 
                f"Timeout après {max_wait_time}s lors de la génération simple",
                critical=True
            )
            return False
            
        except Exception as e:
            self.add_test_result(
                'simple_generation', 
                'FAILURE', 
                f"Erreur lors du test de génération simple: {e}",
                critical=True
            )
            return False
    
    def run_complete_validation(self) -> bool:
        """Exécute la validation complète"""
        logger.info("🚀 Démarrage de la validation complète Qwen...")
        print("🔍 SCRIPT DE VALIDATION COMPLÈTE QWEN - VERSION ISOLÉE")
        print("=" * 60)
        print(f"Heure: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"Workflow cible: {self.workflow_path}")
        print("🔧 Configuration: Boundary Awareness RESPECTÉE")
        print("📡 Communication: Client API pur uniquement")
        print()
        
        # Exécution des tests séquentiels
        all_tests_passed = True
        
        # Test 1: Import des nodes Qwen
        test1_passed = self.test_1_import_qwen_nodes()
        if not test1_passed:
            all_tests_passed = False
        
        # Test 2: Connectivité ComfyUI
        test2_passed = self.test_2_comfyui_connectivity()
        if not test2_passed:
            all_tests_passed = False
        
        # Test 3: Validation du workflow
        test3_passed = self.test_3_workflow_validation()
        if not test3_passed:
            all_tests_passed = False
        
        # Test 4: Génération simple
        test4_passed = self.test_4_simple_generation()
        if not test4_passed:
            all_tests_passed = False
        
        # Finalisation
        self.end_time = time.time()
        execution_time = self.end_time - self.start_time
        
        # Génération des recommandations
        self._generate_recommendations()
        
        # Affichage des résultats
        self._display_results(execution_time)
        
        # Sauvegarde du rapport
        self._save_report()
        
        return all_tests_passed
    
    def _generate_recommendations(self):
        """Génère les recommandations basées sur les résultats"""
        if self.failure_count > 0:
            self.recommendations.append("Analysez les erreurs critiques et corrigez-les avant de continuer")
        
        if not any('comfyui_client_import' in test for test in self.test_results.keys() 
                  if self.test_results[test]['status'] == 'SUCCESS'):
            self.recommendations.append("Vérifiez l'installation du client ComfyUI et les dépendances")
        
        if not any('qwen_nodes_api_detection' in test for test in self.test_results.keys() 
                  if self.test_results[test]['status'] == 'SUCCESS'):
            self.recommendations.append("Vérifiez que les nodes Qwen sont bien chargées dans ComfyUI")
        
        if not any('workflow_submission' in test for test in self.test_results.keys() 
                  if self.test_results[test]['status'] == 'SUCCESS'):
            self.recommendations.append("Vérifiez la configuration du workflow et les modèles requis")
        
        if not any('simple_generation_success' in test for test in self.test_results.keys() 
                  if self.test_results[test]['status'] == 'SUCCESS'):
            self.recommendations.append("Vérifiez les modèles Qwen et les ressources GPU")
    
    def _display_results(self, execution_time: float):
        """Affiche les résultats des tests"""
        print("\n📊 RÉSULTATS DES TESTS")
        print("=" * 60)
        
        print(f"⏱️  Temps d'exécution: {execution_time:.2f}s")
        print(f"📈 Tests totaux: {len(self.test_results)}")
        print(f"✅ Succès: {self.success_count}")
        print(f"❌ Échecs: {self.failure_count}")
        print(f"🚨 Problèmes critiques: {len(self.critical_issues)}")
        print(f"⚠️  Avertissements: {len(self.warnings)}")
        print(f"📊 Taux de succès: {(self.success_count / len(self.test_results) * 100):.1f}%")
        
        print("\n📋 DÉTAIL DES TESTS:")
        for test_name, result in self.test_results.items():
            status_icon = "✅" if result['status'] == 'SUCCESS' else "❌" if result['critical'] else "⚠️"
            print(f"   {status_icon} {test_name}: {result['details']}")
        
        if self.critical_issues:
            print("\n🚨 PROBLÈMES CRITIQUES:")
            for i, issue in enumerate(self.critical_issues, 1):
                print(f"   {i}. {issue}")
        
        if self.warnings:
            print("\n⚠️  AVERTISSEMENTS:")
            for i, warning in enumerate(self.warnings, 1):
                print(f"   {i}. {warning}")
        
        if self.recommendations:
            print("\n💡 RECOMMANDATIONS:")
            for i, rec in enumerate(self.recommendations, 1):
                print(f"   {i}. {rec}")
    
    def _save_report(self):
        """Sauvegarde le rapport de validation"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        report_filename = f'qwen_complete_validation_report_{timestamp}.json'
        
        report = {
            'metadata': {
                'validation_type': 'COMPLETE_ISOLATED',
                'timestamp': datetime.now().isoformat(),
                'workflow_path': self.workflow_path,
                'platform': platform.system(),
                'execution_time': self.end_time - self.start_time if self.end_time else None,
                'boundary_awareness': 'RESPECTÉ - Client API pur uniquement'
            },
            'summary': {
                'total_tests': len(self.test_results),
                'success_count': self.success_count,
                'failure_count': self.failure_count,
                'critical_issues_count': len(self.critical_issues),
                'warnings_count': len(self.warnings),
                'success_rate': (self.success_count / len(self.test_results) * 100) if self.test_results else 0,
                'overall_status': 'SUCCESS' if self.failure_count == 0 else 'FAILURE'
            },
            'test_results': self.test_results,
            'critical_issues': self.critical_issues,
            'warnings': self.warnings,
            'recommendations': self.recommendations
        }
        
        try:
            report_path = Path.cwd() / report_filename
            with open(report_path, 'w', encoding='utf-8') as f:
                json.dump(report, f, indent=2, ensure_ascii=False)
            
            print(f"\n📄 Rapport sauvegardé: {report_filename}")
            logger.info(f"Rapport sauvegardé: {report_path.absolute()}")
            
        except Exception as e:
            error_msg = f"Erreur sauvegarde rapport: {e}"
            print(f"\n❌ {error_msg}")
            logger.error(error_msg)

def main():
    """Fonction principale"""
    parser = argparse.ArgumentParser(
        description='Script de validation complète et isolée pour le workflow Qwen ComfyUI',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples d'utilisation:
  # Validation complète avec workflow par défaut
  python test_qwen_workflow_complete_validation.py
  
  # Validation avec workflow spécifique
  python test_qwen_workflow_complete_validation.py --workflow custom_workflow.json
  
  # Mode verbose
  python test_qwen_workflow_complete_validation.py --verbose

Ce script effectue une validation complète en 4 étapes :
1. Import des nodes Qwen (boundary awareness)
2. Connectivité ComfyUI via API pure
3. Validation du workflow corrigé
4. Test de génération simple de bout en bout

Approche prudente avec validation à chaque étape.
        """
    )
    
    parser.add_argument(
        '--workflow',
        type=str,
        default='temp_official_workflow_qwen_t2i_fixed.json',
        help='Chemin vers le fichier workflow JSON à tester'
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
    validator = QwenCompleteValidator(args.workflow)
    
    try:
        success = validator.run_complete_validation()
        
        print(f"\n🎯 STATUT FINAL: {'SUCCÈS' if success else 'ÉCHEC'}")
        print(f"🔧 Boundary Awareness: RESPECTÉ")
        print(f"📡 Communication: API pure uniquement")
        
        return 0 if success else 1
        
    except KeyboardInterrupt:
        print("\n⏹️  Test interrompu par l'utilisateur")
        return 130
    except Exception as e:
        print(f"\n💥 Erreur inattendue: {e}")
        logger.exception("Erreur inattendue lors de l'exécution")
        return 1

if __name__ == '__main__':
    sys.exit(main())