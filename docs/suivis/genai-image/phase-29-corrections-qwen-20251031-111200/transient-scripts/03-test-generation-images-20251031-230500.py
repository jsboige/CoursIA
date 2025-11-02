#!/usr/bin/env python3
"""
Script Transient 03 - Test Génération d'Images Qwen

Ce script transient teste la génération d'images avec ComfyUI Qwen
en utilisant les scripts consolidés d'authentification et de workflow.

Auteur: Script transient pour validation ComfyUI Qwen
Date: 2025-10-31
Version: 1.0.0
"""

import sys
import os
import json
import time
import argparse
import logging
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any, Optional

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('test_generation_images.log'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

# Import des scripts consolidés
# Calcul du chemin précis vers la racine du projet
current_file_path = Path(__file__).resolve()
# Extraire la racine du projet en supprimant les sous-répertoires connus
path_parts = current_file_path.parts
# Trouver l'index de 'docs' dans le chemin
docs_index = path_parts.index('docs') if 'docs' in path_parts else -1
if docs_index >= 0:
    project_root = Path(*path_parts[:docs_index])  # Racine avant 'docs'
else:
    # Fallback: utiliser la méthode traditionnelle
    project_root = current_file_path.parent.parent.parent.parent

scripts_path = str(project_root / "scripts" / "genai-auth")
sys.path.insert(0, scripts_path)

logger.info(f"Chemin du script actuel: {current_file_path}")
logger.info(f"Racine du projet détectée: {project_root}")
logger.info(f"Chemin des scripts consolidés: {scripts_path}")

try:
    from genai_auth_manager import GenAIAuthManager
    from comfyui_client_helper import ComfyUIConfig, ComfyUIClient
    from workflow_utils import WorkflowUtils
    logger.info("Scripts consolidés importés")
    logger.info(f"Scripts path: {scripts_path}")
except ImportError as e:
    logger.error(f"Erreur import scripts consolidés: {e}")
    logger.error(f"Scripts path: {scripts_path}")
    logger.error(f"Current working directory: {os.getcwd()}")
    sys.exit(1)


class TestGenerationImages:
    """
    Classe principale pour les tests de génération d'images Qwen
    """
    
    def __init__(self, config_file: Optional[str] = None):
        """Initialise le testeur de génération d'images"""
        self.config_file = config_file
        self.auth_manager = GenAIAuthManager(config_file)
        self.workflow_utils = WorkflowUtils()
        self.client = None
        self.test_results = {
            "timestamp": datetime.now().isoformat(),
            "tests": {},
            "summary": {
                "total_tests": 0,
                "passed_tests": 0,
                "failed_tests": 0,
                "issues": []
            }
        }
        
        logger.info("Initialiseur de test de génération d'images Qwen")
    
    def setup_authentication(self) -> Dict[str, Any]:
        """
        Configure l'authentification pour ComfyUI Qwen
        
        Returns:
            Dictionnaire avec les résultats du test
        """
        logger.info("Configuration de l'authentification ComfyUI Qwen")
        
        test_result = {
            "test_name": "authentication",
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "details": {},
            "issues": []
        }
        
        try:
            # Valider les tokens existants
            validation = self.auth_manager.validate_tokens("comfyui-qwen")
            
            if not validation.get("token_exists", False):
                logger.warning("Tokens non trouvés, génération en cours")
                
                # Générer des tokens si nécessaire
                if not self.auth_manager.generate_tokens("comfyui-qwen"):
                    test_result["issues"].append("Échec génération tokens ComfyUI Qwen")
                    logger.error("Échec génération tokens ComfyUI Qwen")
                    return test_result
                
                logger.info("Tokens ComfyUI Qwen générés avec succès")
            
            # Charger la configuration du service
            service_config = self.auth_manager.config["services"]["comfyui-qwen"]
            
            # Charger le token depuis le fichier .env.generated
            env_file = Path(".secrets/.env.generated")
            api_key = None
            
            if env_file.exists():
                with open(env_file, 'r', encoding='utf-8') as f:
                    for line in f:
                        if line.startswith(service_config["env_var"]):
                            api_key = line.split('=', 1)[1].strip()
                            break
            
            if not api_key:
                # Fallback: essayer depuis l'environnement
                api_key = os.environ.get(service_config["env_var"])
            
            if not api_key:
                test_result["issues"].append("Token API non trouvé dans .env.generated ou environnement")
                logger.error("Token API non trouvé")
                return test_result
            
            # Créer la configuration ComfyUI
            comfyui_config = ComfyUIConfig(
                host=service_config["host"],
                port=service_config["port"],
                protocol=service_config["protocol"],
                api_key=api_key,
                timeout=service_config.get("timeout", 30),
                max_retries=service_config.get("max_retries", 3)
            )
            
            # Initialiser le client ComfyUI
            self.client = ComfyUIClient(comfyui_config)
            
            test_result["success"] = True
            test_result["details"]["message"] = "Authentification configurée avec succès"
            test_result["details"]["api_key_loaded"] = True
            logger.info("Authentification configurée avec succès")
            
        except Exception as e:
            test_result["issues"].append(f"Erreur configuration authentification: {e}")
            logger.error(f"Erreur configuration authentification: {e}")
        
        return test_result
    
    def test_connectivity(self) -> Dict[str, Any]:
        """
        Test la connectivité avec l'API ComfyUI
        
        Returns:
            Dictionnaire avec les résultats du test
        """
        logger.info("Test de connectivité API ComfyUI")
        
        test_result = {
            "test_name": "connectivity",
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "details": {},
            "issues": []
        }
        
        try:
            if not self.client:
                test_result["issues"].append("Client non initialisé")
                return test_result
            
            # Test de connectivité basique
            if self.client.test_connectivity():
                test_result["success"] = True
                test_result["details"]["message"] = "Connectivité établie avec succès"
                logger.info("Connectivité API ComfyUI OK")
            else:
                test_result["issues"].append("Échec connexion API ComfyUI")
                logger.error("Connectivité API ComfyUI échouée")
            
            # Test des endpoints principaux
            server_info = self.client.get_server_info()
            if server_info:
                test_result["details"]["server_info"] = server_info
                logger.info(f"Infos serveur: {len(server_info)} champs récupérés")
            else:
                test_result["issues"].append("Impossible récupérer infos serveur")
            
        except Exception as e:
            test_result["issues"].append(f"Erreur test connectivité: {e}")
            logger.error(f"Erreur test connectivité: {e}")
        
        return test_result
    
    def create_simple_qwen_workflow(self) -> Dict[str, Any]:
        """
        Crée un workflow Qwen T2I basique pour tester la génération
        
        Returns:
            Workflow JSON simple pour Qwen
        """
        logger.info("Création workflow Qwen T2I basique")
        
        workflow = {
            "nodes": [
                {
                    "id": 1,
                    "type": "QwenImageSamplerNode",
                    "inputs": {
                        "seed": 42,
                        "steps": 20,
                        "cfg": 7.0,
                        "sampler_name": "euler_ancestral",
                        "scheduler": "normal",
                        "transformer": ["1", 1],
                        "positive": ["conditioning", 0],
                        "negative": ["conditioning", 1],
                        "latent_image": ["latent", 0]
                    }
                }
            ],
            "links": [],
            "groups": [],
            "config": {},
            "extra": {},
            "version": 0.4
        }
        
        logger.info("Workflow Qwen basique créé")
        return workflow
    
    def test_workflow_submission(self) -> Dict[str, Any]:
        """
        Test la soumission d'un workflow Qwen à l'API ComfyUI
        
        Returns:
            Dictionnaire avec les résultats du test
        """
        logger.info("Test de soumission de workflow")
        
        test_result = {
            "test_name": "workflow_submission",
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "details": {},
            "issues": []
        }
        
        try:
            if not self.client:
                test_result["issues"].append("Client non initialisé")
                return test_result
            
            # Créer un workflow simple
            workflow = self.create_simple_qwen_workflow()
            
            # Sauvegarder temporairement le workflow pour validation
            temp_workflow_file = Path("test_workflow.json")
            try:
                with open(temp_workflow_file, 'w', encoding='utf-8') as f:
                    json.dump(workflow, f, indent=2)
                
                # Valider le workflow
                validation_results = self.workflow_utils.validate_workflow_json(temp_workflow_file)
                if not validation_results.get("valid", False):
                    errors = validation_results.get("errors", [])
                    test_result["issues"].extend([f"Workflow invalide: {error}" for error in errors])
                    logger.error(f"Workflow invalide: {errors}")
                    return test_result
            finally:
                # Nettoyer le fichier temporaire
                if temp_workflow_file.exists():
                    temp_workflow_file.unlink()
            
            # Soumettre le workflow
            prompt_id = self.client.submit_workflow(workflow)
            
            if prompt_id:
                test_result["success"] = True
                test_result["details"]["prompt_id"] = prompt_id
                test_result["details"]["workflow_nodes"] = len(workflow.get("nodes", []))
                logger.info(f"Workflow soumis avec ID: {prompt_id}")
                
                # Attendre un peu pour l'exécution
                time.sleep(2)
                
                # Vérifier le statut
                queue_status = self.client.get_queue_status()
                if queue_status:
                    test_result["details"]["queue_status"] = queue_status
                    logger.info(f"Statut file: {queue_status}")
                
            else:
                test_result["issues"].append("Échec soumission workflow")
                logger.error("Échec soumission workflow")
            
        except Exception as e:
            test_result["issues"].append(f"Erreur soumission workflow: {e}")
            logger.error(f"Erreur soumission workflow: {e}")
        
        return test_result
    
    def test_image_generation(self) -> Dict[str, Any]:
        """
        Test la génération effective d'une image
        
        Returns:
            Dictionnaire avec les résultats du test
        """
        logger.info("Test de génération d'image")
        
        test_result = {
            "test_name": "image_generation",
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "details": {},
            "issues": []
        }
        
        try:
            if not self.client:
                test_result["issues"].append("Client non initialisé")
                return test_result
            
            # Récupérer le dernier prompt_id depuis le test précédent
            if "workflow_submission" not in self.test_results["tests"]:
                test_result["issues"].append("Test de soumission workflow requis")
                return test_result
            
            submission_test = self.test_results["tests"]["workflow_submission"]
            prompt_id = submission_test.get("details", {}).get("prompt_id")
            
            if not prompt_id:
                test_result["issues"].append("Aucun prompt_id disponible")
                return test_result
            
            # Attendre la génération
            logger.info(f"Attente génération image (prompt_id: {prompt_id})")
            
            max_wait_time = 120
            start_time = time.time()
            
            while time.time() - start_time < max_wait_time:
                try:
                    # Récupérer le résultat
                    result = self.client.get_result(prompt_id, wait_completion=False)
                    
                    if result and result.get("status", {}).get("completed", False):
                        test_result["success"] = True
                        test_result["details"]["generation_completed"] = True
                        
                        # Analyser les outputs
                        outputs = result.get("outputs", {})
                        if outputs:
                            test_result["details"]["output_count"] = len(outputs)
                            test_result["details"]["outputs"] = outputs
                            
                            # Vérifier la présence d'images
                            image_count = 0
                            for node_id, node_outputs in outputs.items():
                                if isinstance(node_outputs, dict):
                                    for output_name, output_data in node_outputs.items():
                                        if output_data.get("type") == "image" and "filename" in output_data:
                                            image_count += 1
                            
                            test_result["details"]["image_count"] = image_count
                            
                            if image_count > 0:
                                logger.info(f"Image générée avec succès: {image_count} image(s)")
                                test_result["details"]["message"] = f"Génération réussie: {image_count} image(s)"
                            else:
                                test_result["issues"].append("Aucune image générée")
                                logger.warning("Aucune image générée dans les outputs")
                        else:
                            test_result["issues"].append("Outputs vides ou invalides")
                            logger.warning("Outputs vides ou invalides")
                        
                        break
                    
                    elif result and result.get("status", {}).get("running", False):
                        elapsed = int(time.time() - start_time)
                        logger.info(f"Génération en cours ({elapsed}s)")
                        time.sleep(5)
                        continue
                    
                    else:
                        elapsed = int(time.time() - start_time)
                        logger.info(f"Statut intermédiaire: {result.get('status', {})} ({elapsed}s)")
                        time.sleep(5)
                        continue
                
                except Exception as e:
                    logger.error(f"Erreur surveillance génération: {e}")
                    time.sleep(2)
                    continue
            
            # Timeout
            if not test_result["success"]:
                test_result["issues"].append(f"Timeout après {max_wait_time}s")
                logger.error(f"Timeout génération image après {max_wait_time}s")
            
        except Exception as e:
            test_result["issues"].append(f"Erreur test génération: {e}")
            logger.error(f"Erreur test génération: {e}")
        
        return test_result
    
    def test_image_validation(self) -> Dict[str, Any]:
        """
        Test la validation des images générées
        
        Returns:
            Dictionnaire avec les résultats du test
        """
        logger.info("Test de validation des images")
        
        test_result = {
            "test_name": "image_validation",
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "details": {},
            "issues": []
        }
        
        try:
            if not self.client:
                test_result["issues"].append("Client non initialisé")
                return test_result
            
            # Récupérer les résultats du test précédent
            if "image_generation" not in self.test_results["tests"]:
                test_result["issues"].append("Test de génération d'image requis")
                return test_result
            
            generation_test = self.test_results["tests"]["image_generation"]
            if not generation_test.get("success", False):
                test_result["issues"].append("Génération d'image échouée")
                return test_result
            
            outputs = generation_test.get("details", {}).get("outputs", {})
            image_count = generation_test.get("details", {}).get("image_count", 0)
            
            if image_count == 0:
                test_result["issues"].append("Aucune image à valider")
                return test_result
            
            test_result["success"] = True
            test_result["details"]["validated_images"] = image_count
            test_result["details"]["output_structure"] = outputs
            test_result["details"]["message"] = f"Validation réussie: {image_count} image(s)"
            
            logger.info(f"Validation images réussie: {image_count} image(s)")
            
        except Exception as e:
            test_result["issues"].append(f"Erreur validation images: {e}")
            logger.error(f"Erreur validation images: {e}")
        
        return test_result
    
    def run_all_tests(self) -> bool:
        """
        Exécute tous les tests de génération d'images
        
        Returns:
            True si tous les tests passent, False sinon
        """
        logger.info("Démarrage des tests de génération d'images Qwen")
        
        # Test 1: Configuration de l'authentification
        auth_test = self.setup_authentication()
        self.test_results["tests"]["authentication"] = auth_test
        
        # Si l'authentification échoue, arrêter les tests
        if not auth_test.get("success", False):
            logger.error("Authentification échouée, arrêt des tests")
            self.test_results["summary"] = {
                "total_tests": 1,
                "passed_tests": 0,
                "failed_tests": 1,
                "issues": auth_test.get("issues", [])
            }
            return False
        
        # Test 2: Connectivité API
        connectivity_test = self.test_connectivity()
        self.test_results["tests"]["connectivity"] = connectivity_test
        
        # Test 3: Soumission de workflow
        workflow_test = self.test_workflow_submission()
        self.test_results["tests"]["workflow_submission"] = workflow_test
        
        # Test 4: Génération d'image
        generation_test = self.test_image_generation()
        self.test_results["tests"]["image_generation"] = generation_test
        
        # Test 5: Validation des images
        validation_test = self.test_image_validation()
        self.test_results["tests"]["image_validation"] = validation_test
        
        # Calculer le résumé
        total_tests = len(self.test_results["tests"])
        passed_tests = sum(1 for test in self.test_results["tests"].values() if test.get("success", False))
        failed_tests = total_tests - passed_tests
        
        self.test_results["summary"] = {
            "total_tests": total_tests,
            "passed_tests": passed_tests,
            "failed_tests": failed_tests,
            "issues": []
        }
        
        # Collecter les problèmes
        for test_name, test_result in self.test_results["tests"].items():
            if not test_result.get("success", False):
                self.test_results["summary"]["issues"].extend(test_result.get("issues", []))
        
        logger.info(f"Résumé tests: {passed_tests}/{total_tests} réussis")
        
        return passed_tests == total_tests
    
    def generate_report(self, output_dir: str = "./rapports") -> bool:
        """
        Génère un rapport détaillé des tests
        
        Args:
            output_dir: Répertoire de sortie pour le rapport
            
        Returns:
            True si succès, False sinon
        """
        logger.info("Génération du rapport de test")
        
        try:
            # Créer le répertoire de sortie
            Path(output_dir).mkdir(parents=True, exist_ok=True)
            
            # Préparer le rapport
            report = {
                "title": "Rapport de Test - Génération d'Images Qwen",
                "timestamp": datetime.now().isoformat(),
                "script_version": "1.0.0",
                "test_environment": {
                    "python_version": sys.version,
                    "platform": sys.platform,
                    "working_directory": str(Path.cwd()),
                    "config_file": str(self.config_file) if self.config_file else "default"
                },
                "test_results": self.test_results,
                "summary": self.test_results["summary"],
                "recommendations": []
            }
            
            # Générer les recommandations
            if self.test_results["summary"]["failed_tests"] > 0:
                report["recommendations"].append("Corriger les problèmes d'authentification identifiés")
                report["recommendations"].append("Vérifier la connectivité réseau")
                report["recommendations"].append("Valider la configuration ComfyUI Qwen")
            
            if self.test_results["summary"]["passed_tests"] == self.test_results["summary"]["total_tests"]:
                report["recommendations"].append("Système ComfyUI Qwen fonctionnel")
                report["recommendations"].append("Prêt pour la production d'images")
            else:
                report["recommendations"].append("Tests supplémentaires requis")
                report["recommendations"].append("Investiguer les erreurs de workflow")
            
            # Sauvegarder le rapport
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            report_file = Path(output_dir) / f"rapport-test-generation-images-{timestamp}.md"
            
            with open(report_file, 'w', encoding='utf-8') as f:
                f.write(f"# {report['title']}\n\n")
                f.write(f"**Date**: {report['timestamp']}\n")
                f.write(f"**Version du script**: {report['script_version']}\n\n")
                
                f.write("## Résumé des Tests\n\n")
                summary = report['summary']
                f.write(f"- **Tests totaux**: {summary['total_tests']}\n")
                f.write(f"- **Tests réussis**: {summary['passed_tests']}\n")
                f.write(f"- **Tests échoués**: {summary['failed_tests']}\n")
                f.write(f"- **Taux de succès**: {summary['passed_tests']/summary['total_tests']*100:.1f}%\n\n")
                
                f.write("## Résultats Détaillés\n\n")
                
                for test_name, test_result in report['test_results']['tests'].items():
                    status = "RÉUSSI" if test_result.get('success', False) else "ÉCHOUÉ"
                    f.write(f"### {test_name.replace('_', ' ').title()}: {status}\n\n")
                    
                    if test_result.get('success', False):
                        details = test_result.get('details', {})
                        for key, value in details.items():
                            f.write(f"- **{key}**: {value}\n")
                    else:
                        issues = test_result.get('issues', [])
                        for issue in issues:
                            f.write(f"- **Problème**: {issue}\n")
                    f.write("\n")
                
                f.write("## Recommandations\n\n")
                for i, rec in enumerate(report['recommendations'], 1):
                    f.write(f"{i}. {rec}\n")
                
                f.write(f"\n---\n*Généré le*: {report['timestamp']}*\n")
            
            logger.info(f"Rapport généré: {report_file}")
            return True
            
        except Exception as e:
            logger.error(f"Erreur génération rapport: {e}")
            return False


def main():
    """
    Fonction principale du script transient
    """
    parser = argparse.ArgumentParser(
        description='Script Transient 03 - Test Génération d\'Images Qwen',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples d'utilisation:
  # Test complet avec configuration par défaut
  python 03-test-generation-images-20251031-230500.py
  
  # Test avec fichier de configuration spécifique
  python 03-test-generation-images-20251031-230500.py --config ./genai_auth_config.json
  
  # Générer uniquement le rapport sans exécuter les tests
  python 03-test-generation-images-20251031-230500.py --report-only --output ./rapports
        """
    )
    
    parser.add_argument(
        '--config',
        help='Chemin vers le fichier de configuration GenAI Auth (défaut: genai_auth_config.json)'
    )
    
    parser.add_argument(
        '--output',
        default='./rapports',
        help='Répertoire de sortie pour les rapports (défaut: ./rapports)'
    )
    
    parser.add_argument(
        '--report-only',
        action='store_true',
        help='Générer uniquement le rapport sans exécuter les tests'
    )
    
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Activer les logs détaillés'
    )
    
    args = parser.parse_args()
    
    # Configurer le logging verbose si demandé
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
        logger.info("Mode verbose activé")
    
    # Initialiser le testeur
    tester = TestGenerationImages(args.config)
    
    try:
        if args.report_only:
            # Générer uniquement le rapport
            logger.info("Mode rapport uniquement")
            success = tester.generate_report(args.output)
        else:
            # Exécuter tous les tests
            success = tester.run_all_tests()
            
            # Générer le rapport dans tous les cas
            if success:
                logger.info("Tests terminés avec succès")
            else:
                logger.warning("Certains tests ont échoué")
            
            # Générer le rapport
            report_success = tester.generate_report(args.output)
            
            if not report_success:
                logger.error("Échec génération rapport")
                success = False
        
        # Afficher le résumé final
        summary = tester.test_results["summary"]
        print("\n" + "="*60)
        print("RÉSULTATS DES TESTS DE GÉNÉRATION D'IMAGES QWEN")
        print("="*60)
        print(f"Tests totaux: {summary['total_tests']}")
        print(f"Tests réussis: {summary['passed_tests']}")
        print(f"Tests échoués: {summary['failed_tests']}")
        print(f"Taux de succès: {summary['passed_tests']/summary['total_tests']*100:.1f}%")
        print("="*60)
        
        sys.exit(0 if success else 1)
        
    except KeyboardInterrupt:
        print("\nTests interrompus par l'utilisateur")
        sys.exit(130)
    except Exception as e:
        logger.error(f"Erreur inattendue: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()