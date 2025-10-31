#!/usr/bin/env python3
"""
Validateur complet pour la solution Qwen ComfyUI - Script consolidé paramétrique

Ce script consolide les fonctionnalités de validation pour ComfyUI Qwen :
- Validation complète de l'environnement
- Tests de connectivité et d'API
- Validation des workflows
- Diagnostic des problèmes
- Génération de rapports détaillés

Auteur: Consolidation des scripts de validation existants
Date: 2025-10-31
Version: 1.0.0
"""

import argparse
import json
import logging
import sys
import time
import requests
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('qwen_validator.log'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

class QwenValidator:
    """Validateur complet pour la solution Qwen ComfyUI"""
    
    def __init__(self, config_file: Optional[str] = None):
        self.config_file = Path(config_file) if config_file else Path.cwd() / "qwen_validator_config.json"
        self.config = self._load_config()
        
    def _load_config(self) -> Dict[str, Any]:
        """Charge la configuration depuis le fichier"""
        try:
            if self.config_file.exists():
                with open(self.config_file, 'r', encoding='utf-8') as f:
                    return json.load(f)
            else:
                logger.info(f"Création du fichier de configuration: {self.config_file}")
                return self._get_default_config()
        except Exception as e:
            logger.error(f"Erreur chargement configuration: {e}")
            return self._get_default_config()
    
    def _get_default_config(self) -> Dict[str, Any]:
        """Retourne la configuration par défaut"""
        return {
            "comfyui": {
                "host": "localhost",
                "port": 8188,
                "protocol": "http",
                "timeout": 30,
                "max_retries": 3,
                "api_key": None,
                "container_name": "comfyui-qwen"
            },
            "validation": {
                "quick_mode": True,
                "comprehensive_mode": True,
                "parallel_checks": True,
                "timeout_basic": 10,
                "timeout_comprehensive": 300,
                "retry_delay": 2.0,
                "report_format": "json",
                "backup_results": True
            },
            "workflow": {
                "default_test_workflow": {
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
            }
        }
    
    def _save_config(self):
        """Sauvegarde la configuration dans le fichier"""
        try:
            with open(self.config_file, 'w', encoding='utf-8') as f:
                json.dump(self.config, f, indent=2)
            logger.info(f"Configuration sauvegardée: {self.config_file}")
        except Exception as e:
            logger.error(f"Erreur sauvegarde configuration: {e}")
    
    def validate_environment(self, mode: str = "comprehensive") -> Dict[str, Any]:
        """Validation complète de l'environnement ComfyUI Qwen"""
        logger.info(f"Validation environnement - Mode: {mode}")
        
        validation_results = {
            "validation_timestamp": datetime.now().isoformat(),
            "mode": mode,
            "checks": {},
            "issues": [],
            "recommendations": []
        }
        
        comfyui_config = self.config["comfyui"]
        
        # Test 1: Connectivité de base
        try:
            start_time = time.time()
            response = requests.get(
                f"{comfyui_config['protocol']}://{comfyui_config['host']}:{comfyui_config['port']}/system_stats",
                timeout=self.config["validation"]["timeout_basic"]
            )
            
            validation_results["checks"]["basic_connectivity"] = {
                "status": "success" if response.status_code == 200 else "failed",
                "response_time": response.elapsed.total_seconds(),
                "status_code": response.status_code
            }
            
            if response.status_code == 200:
                logger.info("✅ Connectivité de base établie")
            else:
                validation_results["issues"].append(f"Connectivité de base échouée: HTTP {response.status_code}")
                
        except Exception as e:
            validation_results["checks"]["basic_connectivity"] = {
                "status": "error",
                "error": str(e)
            }
            validation_results["issues"].append(f"Erreur connectivité: {e}")
        
        # Test 2: Validation des nodes Qwen
        if mode == "comprehensive":
            try:
                response = requests.get(
                    f"{comfyui_config['protocol']}://{comfyui_config['host']}:{comfyui_config['port']}/object_info",
                    timeout=self.config["validation"]["timeout_comprehensive"]
                )
                
                if response.status_code == 200:
                    object_info = response.json()
                    qwen_nodes = [k for k in object_info.keys() if 'Qwen' in k or 'qwen' in k.lower()]
                    
                    validation_results["checks"]["qwen_nodes"] = {
                        "status": "success",
                        "nodes_found": len(qwen_nodes),
                        "node_list": qwen_nodes
                    }
                    
                    if qwen_nodes:
                        logger.info(f"✅ {len(qwen_nodes)} nodes Qwen détectés")
                    else:
                        validation_results["issues"].append("Aucun node Qwen détecté")
                else:
                    validation_results["checks"]["qwen_nodes"] = {
                        "status": "failed",
                        "error_code": response.status_code,
                        "error_message": response.text[:200]
                    }
                    validation_results["issues"].append(f"Échec détection nodes Qwen: HTTP {response.status_code}")
                    
            except Exception as e:
                validation_results["checks"]["qwen_nodes"] = {
                    "status": "error",
                    "error": str(e)
                }
                validation_results["issues"].append(f"Erreur détection nodes: {e}")
        
        # Test 3: Validation des workflows
        try:
            workflow = self.config["workflow"]["default_test_workflow"]
            
            # Soumettre le workflow de test
            response = requests.post(
                f"{comfyui_config['protocol']}://{comfyui_config['host']}:{comfyui_config['port']}/prompt",
                json={"prompt": "Test validation workflow", "workflow": workflow},
                timeout=self.config["validation"]["timeout_comprehensive"]
            )
            
            if response.status_code == 200:
                result = response.json()
                
                validation_results["checks"]["workflow_submission"] = {
                    "status": "success",
                    "prompt_id": result.get("prompt_id"),
                    "submission_time": datetime.now().isoformat()
                }
                
                logger.info(f"✅ Workflow de test soumis avec ID: {result.get('prompt_id')}")
                
                # Vérifier le traitement
                time.sleep(5)
                
                try:
                    history_response = requests.get(
                        f"{comfyui_config['protocol']}://{comfyui_config['host']}:{comfyui_config['port']}/history/{result.get('prompt_id')}",
                        timeout=30
                    )
                    
                    if history_response.status_code == 200:
                        history = history_response.json()
                        
                        if result.get("prompt_id") in history:
                            workflow_result = history[result.get("prompt_id")]
                            status = workflow_result.get("status", {}).get("completed", False)
                            
                            validation_results["checks"]["workflow_processing"] = {
                                "status": "success" if status else "processing",
                                "completed": status,
                                "outputs_count": len(workflow_result.get("outputs", {}))
                            }
                            
                            if status:
                                logger.info("✅ Workflow de test traité avec succès")
                            else:
                                logger.info("⏳ Workflow de test en cours de traitement")
                    else:
                        validation_results["issues"].append("Historique du workflow non trouvé")
                        
                except Exception as e:
                    validation_results["issues"].append(f"Erreur vérification traitement: {e}")
                    
            else:
                validation_results["checks"]["workflow_submission"] = {
                    "status": "failed",
                    "error_code": response.status_code,
                    "error_message": response.text[:200]
                }
                validation_results["issues"].append(f"Échec soumission workflow: HTTP {response.status_code}")
                
        except Exception as e:
            validation_results["checks"]["workflow_submission"] = {
                "status": "error",
                "error": str(e)
            }
            validation_results["issues"].append(f"Erreur soumission workflow: {e}")
        
        # Recommandations basées sur les résultats
        if validation_results["issues"]:
            validation_results["recommendations"].append("Corriger les problèmes détectés avant de continuer")
        
        if not validation_results["checks"].get("qwen_nodes", {}).get("nodes_found", 0):
            validation_results["recommendations"].append("Vérifier l'installation des nodes Qwen dans ComfyUI")
        
        validation_results["total_execution_time"] = time.time() - start_time
        
        return validation_results
    
    def validate_workflow_file(self, workflow_path: str) -> Dict[str, Any]:
        """Valide un fichier de workflow spécifique"""
        logger.info(f"Validation du fichier workflow: {workflow_path}")
        
        validation_results = {
            "validation_timestamp": datetime.now().isoformat(),
            "workflow_file": workflow_path,
            "checks": {},
            "issues": [],
            "recommendations": []
        }
        
        try:
            workflow_file = Path(workflow_path)
            
            if not workflow_file.exists():
                validation_results["issues"].append(f"Fichier workflow introuvable: {workflow_path}")
                return validation_results
            
            # Validation JSON
            with open(workflow_file, 'r', encoding='utf-8') as f:
                workflow_data = json.load(f)
            
            validation_results["checks"]["json_syntax"] = {
                "status": "success",
                "file_size": workflow_file.stat().st_size
            }
            
            # Validation structurelle
            required_sections = ["nodes", "links"]
            for section in required_sections:
                if section not in workflow_data:
                    validation_results["issues"].append(f"Section '{section}' manquante")
                else:
                    validation_results["checks"][f"section_{section}"] = {
                        "status": "success",
                        "count": len(workflow_data[section]) if isinstance(workflow_data[section], list) else 0
                    }
            
            # Validation des nodes
            if "nodes" in workflow_data:
                nodes = workflow_data["nodes"]
                for i, node in enumerate(nodes):
                    if not isinstance(node, dict):
                        validation_results["issues"].append(f"Node {i}: format invalide")
                    elif "class_type" not in node:
                        validation_results["issues"].append(f"Node {i}: class_type manquant")
                    elif "inputs" not in node:
                        validation_results["issues"].append(f"Node {i}: inputs manquants")
            
            # Validation des liens
            if "links" in workflow_data:
                links = workflow_data["links"]
                for i, link in enumerate(links):
                    if not isinstance(link, list) or len(link) != 4:
                        validation_results["issues"].append(f"Link {i}: format invalide")
            
            if not validation_results["issues"]:
                validation_results["checks"]["structural"] = {
                    "status": "success",
                    "nodes_count": len(workflow_data.get("nodes", [])),
                    "links_count": len(workflow_data.get("links", []))
                }
            
        except json.JSONDecodeError as e:
            validation_results["checks"]["json_syntax"] = {
                "status": "failed",
                "error": str(e)
            }
            validation_results["issues"].append(f"Erreur JSON: {e}")
        except Exception as e:
            validation_results["issues"].append(f"Erreur lecture fichier: {e}")
        
        return validation_results
    
    def generate_report(self, validation_results: Dict[str, Any], output_file: Optional[str] = None) -> str:
        """Génère un rapport de validation détaillé"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        if output_file is None:
            output_file = f"qwen_validation_report_{timestamp}.json"
        
        report_data = {
            "metadata": {
                "report_timestamp": datetime.now().isoformat(),
                "validator_version": "1.0.0",
                "validation_mode": validation_results.get("mode", "unknown"),
                "total_execution_time": validation_results.get("total_execution_time", 0),
                "total_issues": len(validation_results.get("issues", [])),
                "total_recommendations": len(validation_results.get("recommendations", []))
            },
            "validation_results": validation_results
        }
        
        try:
            with open(output_file, 'w', encoding='utf-8') as f:
                json.dump(report_data, f, indent=2)
            
            logger.info(f"Rapport de validation sauvegardé: {output_file}")
            return output_file
            
        except Exception as e:
            logger.error(f"Erreur sauvegarde rapport: {e}")
            return None
    
    def show_config(self):
        """Affiche la configuration actuelle"""
        print("🔍 CONFIGURATION QWEN VALIDATOR")
        print("=" * 50)
        print(json.dumps(self.config, indent=2))
        print("=" * 50)

def main():
    """Fonction principale du validateur"""
    parser = argparse.ArgumentParser(
        description='Validateur complet pour la solution Qwen ComfyUI - Script consolidé paramétrique',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples d'utilisation:
  # Validation rapide
  python qwen-validator.py --mode quick
  
  # Validation complète
  python qwen-validator.py --mode comprehensive
  
  # Validation d'un workflow spécifique
  python qwen-validator.py --workflow workflow.json --output validation_report.json
  
  # Afficher la configuration
  python qwen-validator.py --show-config
        """
    )
    
    parser.add_argument(
        '--config',
        help='Chemin vers le fichier de configuration (défaut: qwen_validator_config.json)'
    )
    
    parser.add_argument(
        '--mode',
        choices=['quick', 'comprehensive'],
        default='comprehensive',
        help='Mode de validation (quick ou comprehensive)'
    )
    
    parser.add_argument(
        '--workflow',
        help='Chemin vers un fichier workflow à valider (mode workflow uniquement)'
    )
    
    parser.add_argument(
        '--output',
        help='Fichier de sortie pour le rapport de validation'
    )
    
    parser.add_argument(
        '--show-config',
        action='store_true',
        help='Afficher la configuration actuelle'
    )
    
    args = parser.parse_args()
    
    # Initialiser le validateur
    validator = QwenValidator(args.config)
    
    # Exécuter l'action appropriée
    if args.show_config:
        validator.show_config()
        sys.exit(0)
    
    elif args.workflow:
        results = validator.validate_workflow_file(args.workflow)
        print("\n📊 RÉSULTATS DE VALIDATION WORKFLOW:")
        print(json.dumps(results, indent=2))
        
        if args.output:
            validator.generate_report(results, args.output)
        
        sys.exit(0 if not results.get("issues") else 1)
    
    else:
        # Validation environnement
        results = validator.validate_environment(args.mode)
        print("\n📊 RÉSULTATS DE VALIDATION ENVIRONNEMENT:")
        print(json.dumps(results, indent=2))
        
        # Générer le rapport
        if args.output:
            output_file = validator.generate_report(results, args.output)
        else:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            output_file = f"qwen_validation_report_{timestamp}.json"
            validator.generate_report(results, output_file)
        
        sys.exit(0 if not results.get("issues") else 1)

if __name__ == "__main__":
    main()