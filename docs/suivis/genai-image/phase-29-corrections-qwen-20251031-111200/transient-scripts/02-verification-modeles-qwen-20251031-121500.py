#!/usr/bin/env python3
"""
Script Transient 02 - Vérification des Modèles Qwen

Ce script effectue une vérification complète de l'accessibilité et de l'état
des modèles Qwen dans le système ComfyUI.

Auteur: Script transient basé sur les scripts consolidés
Date: 2025-10-31
Version: 1.0.0

Scripts consolidés utilisés:
- comfyui_client_helper.py pour les interactions avec l'API ComfyUI
- diagnostic_utils.py pour les validations de modèles

Usage:
    python 02-verification-modeles-qwen-20251031-121500.py [options]
"""

import sys
import os
import json
import time
import argparse
import logging
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any, Optional, Tuple

# Import des scripts consolidés
script_dir = Path("d:/Dev/CoursIA/scripts/genai-auth")
if script_dir.exists():
    sys.path.append(str(script_dir))
else:
    print(f"❌ Répertoire des scripts consolidés non trouvé: {script_dir}")
    sys.exit(1)

try:
    from comfyui_client_helper import ComfyUIConfig, ComfyUIClient, ComfyUIError
    from diagnostic_utils import DiagnosticUtils
except ImportError as e:
    print(f"❌ Erreur import scripts consolidés: {e}")
    sys.exit(1)

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


class QwenModelVerifier:
    """
    Vérificateur spécialisé pour les modèles Qwen dans ComfyUI
    """
    
    def __init__(self, config: ComfyUIConfig):
        self.config = config
        self.client = ComfyUIClient(config)
        self.diagnostic = DiagnosticUtils()
        
        # Modèles Qwen attendus
        self.expected_qwen_models = [
            "Qwen-Image-Edit-2509-FP8",
            "Qwen-Image-Edit-2509-FP16",
            "Qwen-Image-Edit-2509-FP32"
        ]
        
        # Répertoires attendus pour les modèles (chemins WSL absolus)
        self.expected_model_directories = [
            r"\\wsl.localhost\Ubuntu\home\jesse\SD\workspace\comfyui-qwen\ComfyUI\models\checkpoints\Qwen-Image-Edit-2509-FP8",
            r"\\wsl.localhost\Ubuntu\home\jesse\SD\workspace\comfyui-qwen\ComfyUI\models\vae",
            r"\\wsl.localhost\Ubuntu\home\jesse\SD\workspace\comfyui-qwen\ComfyUI\models\clip_vision",
            r"\\wsl.localhost\Ubuntu\home\jesse\SD\workspace\comfyui-qwen\ComfyUI\custom_nodes\ComfyUI_QwenImageWanBridge"
        ]
    
    def verify_model_accessibility(self) -> Dict[str, Any]:
        """
        Vérifie l'accessibilité des modèles Qwen
        
        Returns:
            Dictionnaire avec les résultats de vérification
        """
        logger.info("🔍 Vérification de l'accessibilité des modèles Qwen...")
        
        verification_results = {
            "timestamp": datetime.now().isoformat(),
            "models_found": [],
            "models_missing": [],
            "directories_accessible": [],
            "directories_inaccessible": [],
            "file_permissions": {},
            "model_integrity": {},
            "comfyui_models": [],
            "issues": []
        }
        
        # Vérifier les répertoires attendus
        for directory in self.expected_model_directories:
            dir_accessible = self._check_directory_access(directory)
            if dir_accessible:
                verification_results["directories_accessible"].append(directory)
                models_in_dir = self._scan_directory_for_qwen_models(directory)
                verification_results["models_found"].extend(models_in_dir)
            else:
                verification_results["directories_inaccessible"].append(directory)
                verification_results["issues"].append(f"Répertoire inaccessible: {directory}")
        
        # Vérifier les modèles via l'API ComfyUI
        try:
            if self.client.test_connectivity():
                api_models = self._get_comfyui_models()
                verification_results["comfyui_models"] = api_models
                
                # Croiser les informations
                api_model_names = [model.get("name", "") for model in api_models]
                for expected_model in self.expected_qwen_models:
                    if expected_model in api_model_names:
                        verification_results["models_found"].append(expected_model)
                    else:
                        verification_results["models_missing"].append(expected_model)
            else:
                verification_results["issues"].append("ComfyUI API inaccessible")
        except Exception as e:
            verification_results["issues"].append(f"Erreur API ComfyUI: {e}")
        
        # Vérifier l'intégrité des fichiers trouvés
        for model_path in verification_results["models_found"]:
            integrity_check = self._verify_model_integrity(model_path)
            verification_results["model_integrity"][model_path] = integrity_check
        
        logger.info(f"✅ Vérification terminée: {len(verification_results['models_found'])} modèles trouvés")
        return verification_results
    
    def _convert_wsl_path(self, wsl_path: str) -> str:
        """
        Convertit un chemin WSL en chemin accessible depuis Windows
        
        Args:
            wsl_path: Chemin WSL au format \\\\wsl.localhost\\\\Ubuntu\\\\...
            
        Returns:
            Chemin converti pour accès depuis Windows
        """
        try:
            # Les chemins WSL sont déjà au bon format pour Windows
            # On retourne le chemin tel quel
            return wsl_path
        except Exception as e:
            logger.error(f"❌ Erreur conversion chemin WSL {wsl_path}: {e}")
            return wsl_path
    
    def _check_directory_access(self, directory: str) -> bool:
        """
        Vérifie l'accès à un répertoire
        
        Args:
            directory: Chemin du répertoire à vérifier
            
        Returns:
            True si accessible, False sinon
        """
        try:
            # Conversion du chemin WSL si nécessaire
            converted_path = self._convert_wsl_path(directory)
            logger.debug(f"🔍 Vérification accès au répertoire: {directory}")
            logger.debug(f"🔄 Chemin converti: {converted_path}")
            
            path = Path(converted_path)
            if path.exists() and path.is_dir():
                # Test d'écriture
                test_file = path / ".access_test"
                test_file.write_text("test")
                test_file.unlink()
                logger.info(f"✅ Répertoire accessible: {directory}")
                return True
            else:
                logger.warning(f"⚠️ Répertoire n'existe pas: {directory}")
                logger.debug(f"   Chemin testé: {converted_path}")
                return False
        except PermissionError:
            logger.warning(f"⚠️ Permission refusée pour: {directory}")
            return False
        except Exception as e:
            logger.warning(f"⚠️ Erreur accès {directory}: {e}")
            logger.debug(f"   Exception type: {type(e).__name__}")
            return False
    
    def _scan_directory_for_qwen_models(self, directory: str) -> List[str]:
        """
        Scan un répertoire à la recherche de modèles Qwen
        
        Args:
            directory: Répertoire à scanner
            
        Returns:
            Liste des chemins des modèles Qwen trouvés
        """
        qwen_models = []
        try:
            # Conversion du chemin WSL si nécessaire
            converted_path = self._convert_wsl_path(directory)
            logger.debug(f"🔍 Scan du répertoire: {directory}")
            logger.debug(f"🔄 Chemin converti: {converted_path}")
            
            path = Path(converted_path)
            if not path.exists():
                logger.warning(f"⚠️ Répertoire inexistant: {converted_path}")
                return qwen_models
            
            logger.info(f"📂 Scan du répertoire: {converted_path}")
            files_found = 0
            for file_path in path.rglob("*"):
                if file_path.is_file():
                    file_name = file_path.name.lower()
                    if any(qwen_model.lower() in file_name for qwen_model in self.expected_qwen_models):
                        qwen_models.append(str(file_path))
                        logger.info(f"📁 Modèle Qwen trouvé: {file_path}")
                        files_found += 1
            
            logger.info(f"✅ Scan terminé: {files_found} modèles Qwen trouvés dans {directory}")
            return qwen_models
        except Exception as e:
            logger.error(f"❌ Erreur scan {directory}: {e}")
            logger.debug(f"   Exception type: {type(e).__name__}")
            return qwen_models
    
    def _get_comfyui_models(self) -> List[Dict[str, Any]]:
        """
        Récupère la liste des modèles disponibles via l'API ComfyUI
        
        Returns:
            Liste des modèles disponibles
        """
        try:
            # Utiliser l'endpoint object_info pour les modèles
            response = self.client._make_request('GET', '/object_info')
            if response.status_code == 200:
                object_info = response.json()
                
                # Chercher les modèles dans les différents types
                models = []
                
                # Vérifier les checkpoints
                if 'CheckpointLoaderSimple' in object_info:
                    checkpoint_info = object_info['CheckpointLoaderSimple']
                    if checkpoint_info.get('input', {}).get('required'):
                        models.extend([{
                            "type": "checkpoint",
                            "name": model_name,
                            "path": f"/models/checkpoints/{model_name}"
                        } for model_name in checkpoint_info.get('input', {}).get('required', [])])
                
                # Vérifier les VAE
                if 'VAELoader' in object_info:
                    vae_info = object_info['VAELoader']
                    if vae_info.get('input', {}).get('required'):
                        models.extend([{
                            "type": "vae",
                            "name": model_name,
                            "path": f"/models/vae/{model_name}"
                        } for model_name in vae_info.get('input', {}).get('required', [])])
                
                # Vérifier les CLIP Vision
                if 'CLIPVisionLoader' in object_info:
                    clip_info = object_info['CLIPVisionLoader']
                    if clip_info.get('input', {}).get('required'):
                        models.extend([{
                            "type": "clip_vision",
                            "name": model_name,
                            "path": f"/models/clip_vision/{model_name}"
                        } for model_name in clip_info.get('input', {}).get('required', [])])
                
                logger.info(f"📋 {len(models)} modèles récupérés via API ComfyUI")
                return models
            else:
                logger.error(f"❌ Erreur récupération modèles API: {response.status_code}")
                return []
                
        except Exception as e:
            logger.error(f"❌ Erreur API ComfyUI: {e}")
            return []
    
    def _verify_model_integrity(self, model_path: str) -> Dict[str, Any]:
        """
        Vérifie l'intégrité d'un fichier de modèle
        
        Args:
            model_path: Chemin du fichier de modèle
            
        Returns:
            Dictionnaire avec les résultats de vérification d'intégrité
        """
        try:
            path = Path(model_path)
            if not path.exists():
                return {
                    "status": "missing",
                    "error": "Fichier non trouvé"
                }
            
            # Informations de base
            stat = path.stat()
            integrity_info = {
                "status": "verified",
                "size_bytes": stat.st_size,
                "size_mb": round(stat.st_size / (1024 * 1024), 2),
                "modified": datetime.fromtimestamp(stat.st_mtime).isoformat(),
                "readable": os.access(model_path, os.R_OK),
                "file_extension": path.suffix.lower()
            }
            
            # Vérifications spécifiques selon le type
            file_name = path.name.lower()
            if "fp8" in file_name:
                integrity_info["precision"] = "FP8"
            elif "fp16" in file_name:
                integrity_info["precision"] = "FP16"
            elif "fp32" in file_name:
                integrity_info["precision"] = "FP32"
            else:
                integrity_info["precision"] = "inconnue"
            
            # Vérifier si c'est un fichier de modèle valide
            valid_extensions = ['.safetensors', '.bin', '.pth', '.ckpt']
            if path.suffix.lower() not in valid_extensions:
                integrity_info["status"] = "invalid_extension"
                integrity_info["error"] = f"Extension non valide: {path.suffix}"
            
            logger.info(f"✅ Intégrité vérifiée: {path.name}")
            return integrity_info
            
        except Exception as e:
            logger.error(f"❌ Erreur vérification intégrité {model_path}: {e}")
            return {
                "status": "error",
                "error": str(e)
            }
    
    def test_model_loading(self) -> Dict[str, Any]:
        """
        Test le chargement des modèles via l'API ComfyUI
        
        Returns:
            Dictionnaire avec les résultats des tests de chargement
        """
        logger.info("🧪 Test de chargement des modèles Qwen...")
        
        test_results = {
            "timestamp": datetime.now().isoformat(),
            "loading_tests": [],
            "success_count": 0,
            "error_count": 0,
            "issues": []
        }
        
        # Créer un workflow de test simple
        test_workflow = {
            "nodes": [
                {
                    "id": 1,
                    "type": "CheckpointLoaderSimple",
                    "inputs": {
                        "ckpt_name": "Qwen-Image-Edit-2509-FP8.safetensors"
                    }
                },
                {
                    "id": 2,
                    "type": "VAELoader",
                    "inputs": {
                        "vae_name": "Qwen-VAE.safetensors"
                    }
                }
            ],
            "links": [],
            "groups": [],
            "config": {},
            "extra": {},
            "version": 0.4
        }
        
        try:
            # Tester le chargement du checkpoint
            if self.client.test_connectivity():
                prompt_id = self.client.submit_workflow(test_workflow)
                if prompt_id:
                    # Attendre un court moment pour voir si le workflow se charge
                    time.sleep(5)
                    result = self.client.get_result(prompt_id, wait_completion=False)
                    
                    if result:
                        test_results["loading_tests"].append({
                            "model_type": "checkpoint",
                            "model_name": "Qwen-Image-Edit-2509-FP8.safetensors",
                            "status": "success",
                            "prompt_id": prompt_id
                        })
                        test_results["success_count"] += 1
                        logger.info("✅ Test checkpoint réussi")
                    else:
                        test_results["loading_tests"].append({
                            "model_type": "checkpoint",
                            "model_name": "Qwen-Image-Edit-2509-FP8.safetensors",
                            "status": "no_result",
                            "error": "Pas de résultat retourné"
                        })
                        test_results["error_count"] += 1
                        test_results["issues"].append("Test checkpoint sans résultat")
                else:
                    test_results["issues"].append("Échec soumission workflow test")
                    test_results["error_count"] += 1
            else:
                test_results["issues"].append("ComfyUI inaccessible pour les tests")
                test_results["error_count"] += 1
                
        except Exception as e:
            test_results["issues"].append(f"Erreur test chargement: {e}")
            test_results["error_count"] += 1
        
        logger.info(f"✅ Tests terminés: {test_results['success_count']} succès, {test_results['error_count']} erreurs")
        return test_results
    
    def generate_verification_report(self, verification_results: Dict[str, Any], 
                             test_results: Optional[Dict[str, Any]] = None) -> str:
        """
        Génère un rapport détaillé de vérification des modèles
        
        Args:
            verification_results: Résultats de la vérification d'accessibilité
            test_results: Résultats des tests de chargement (optionnel)
            
        Returns:
            Rapport formaté en Markdown
        """
        report_lines = [
            "# RAPPORT DE VÉRIFICATION DES MODÈLES QWEN",
            f"Généré le {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            "",
            "## 📊 RÉSUMÉ EXÉCUTIF",
            f"**Date de vérification**: {verification_results.get('timestamp', 'Inconnue')}",
            f"**Modèles attendus**: {len(self.expected_qwen_models)}",
            f"**Modèles trouvés**: {len(verification_results.get('models_found', []))}",
            f"**Modèles manquants**: {len(verification_results.get('models_missing', []))}",
            f"**Répertoires accessibles**: {len(verification_results.get('directories_accessible', []))}",
            f"**Répertoires inaccessibles**: {len(verification_results.get('directories_inaccessible', []))}",
            "",
            "## 📋 MODÈLES QWEN ATTENDUS",
            ""
        ]
        
        # Liste des modèles attendus
        for model in self.expected_qwen_models:
            status = "✅ Trouvé" if model in verification_results.get('models_found', []) else "❌ Manquant"
            report_lines.append(f"- **{model}**: {status}")
        
        report_lines.extend([
            "",
            "## 📁 RÉPERTOIRES VÉRIFIÉS",
            ""
        ])
        
        # Répertoires accessibles
        accessible_dirs = verification_results.get('directories_accessible', [])
        if accessible_dirs:
            report_lines.append("### ✅ Répertoires Accessibles:")
            for directory in accessible_dirs:
                report_lines.append(f"- {directory}")
        
        # Répertoires inaccessibles
        inaccessible_dirs = verification_results.get('directories_inaccessible', [])
        if inaccessible_dirs:
            report_lines.append("")
            report_lines.append("### ❌ Répertoires Inaccessibles:")
            for directory in inaccessible_dirs:
                report_lines.append(f"- {directory}")
        
        # Modèles trouvés avec détails
        models_found = verification_results.get('models_found', [])
        if models_found:
            report_lines.extend([
                "",
                "## 📄 MODÈLES TROUVÉS (DÉTAILS)",
                ""
            ])
            
            for model_path in models_found:
                integrity = verification_results.get('model_integrity', {}).get(model_path, {})
                report_lines.append(f"### 📁 {model_path}")
                report_lines.append(f"- **Taille**: {integrity.get('size_mb', 'Inconnue')} MB")
                report_lines.append(f"- **Précision**: {integrity.get('precision', 'Inconnue')}")
                report_lines.append(f"- **Extension**: {integrity.get('file_extension', 'Inconnue')}")
                report_lines.append(f"- **Modifié**: {integrity.get('modified', 'Inconnue')}")
                report_lines.append(f"- **Lecture**: {'✅' if integrity.get('readable') else '❌'}")
                
                if integrity.get('status') != 'verified':
                    report_lines.append(f"- **⚠️ Erreur**: {integrity.get('error', 'Inconnue')}")
        
        # Résultats des tests de chargement
        if test_results:
            report_lines.extend([
                "",
                "## 🧪 TESTS DE CHARGEMENT",
                f"**Tests réussis**: {test_results.get('success_count', 0)}",
                f"**Tests échoués**: {test_results.get('error_count', 0)}",
                ""
            ])
            
            loading_tests = test_results.get('loading_tests', [])
            for test in loading_tests:
                status_icon = "✅" if test.get('status') == 'success' else "❌"
                report_lines.append(f"- **{test.get('model_name')}**: {status_icon} {test.get('status')}")
                if test.get('error'):
                    report_lines.append(f"  - Erreur: {test.get('error')}")
        
        # Problèmes détectés
        issues = verification_results.get('issues', [])
        if test_results:
            issues.extend(test_results.get('issues', []))
        
        if issues:
            report_lines.extend([
                "",
                "## ⚠️ PROBLÈMES DÉTECTÉS",
                ""
            ])
            for issue in issues:
                report_lines.append(f"- ❌ {issue}")
        
        # Recommandations
        report_lines.extend([
            "",
            "## 💡 RECOMMANDATIONS",
            ""
        ])
        
        recommendations = []
        
        if verification_results.get('models_missing'):
            recommendations.append("Installer les modèles Qwen manquants dans les répertoires appropriés")
        
        if verification_results.get('directories_inaccessible'):
            recommendations.append("Vérifier les permissions des répertoires de modèles")
        
        if test_results and test_results.get('error_count', 0) > 0:
            recommendations.append("Vérifier la configuration des custom nodes Qwen")
        
        if not recommendations:
            recommendations.append("Aucun problème détecté - système fonctionnel")
        
        for recommendation in recommendations:
            report_lines.append(f"- {recommendation}")
        
        return "\n".join(report_lines)
    
    def save_report(self, report: str, output_dir: str = "./rapports") -> bool:
        """
        Sauvegarde le rapport de vérification
        
        Args:
            report: Contenu du rapport
            output_dir: Répertoire de sortie
            
        Returns:
            True si succès, False sinon
        """
        try:
            output_path = Path(output_dir)
            output_path.mkdir(parents=True, exist_ok=True)
            
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            report_file = output_path / f"02-verification-modeles-qwen-{timestamp}.md"
            
            with open(report_file, 'w', encoding='utf-8') as f:
                f.write(report)
            
            logger.info(f"✅ Rapport sauvegardé: {report_file}")
            return True
            
        except Exception as e:
            logger.error(f"❌ Erreur sauvegarde rapport: {e}")
            return False


class QwenVerificationCLI:
    """
    Interface en ligne de commande pour la vérification des modèles Qwen
    """
    
    def __init__(self):
        self.config = ComfyUIConfig()
        self.verifier = None
    
    def setup_parser(self) -> argparse.ArgumentParser:
        """
        Configure le parser d'arguments
        """
        parser = argparse.ArgumentParser(
            description="Script Transient 02 - Vérification des Modèles Qwen",
            formatter_class=argparse.RawDescriptionHelpFormatter,
            epilog="""
Exemples:
  # Vérification complète
  python 02-verification-modeles-qwen-20251031-121500.py --full
  
  # Vérification avec configuration personnalisée
  python 02-verification-modeles-qwen-20251031-121500.py --host 192.168.1.100 --port 8188
  
  # Vérification avec tests de chargement
  python 02-verification-modeles-qwen-20251031-121500.py --test-loading
  
  # Sauvegarde personnalisée
  python 02-verification-modeles-qwen-20251031-121500.py --output ./mes-rapports
            """
        )
        
        # Arguments de configuration ComfyUI
        parser.add_argument('--host', default='localhost', help='Hôte ComfyUI (défaut: localhost)')
        parser.add_argument('--port', type=int, default=8188, help='Port ComfyUI (défaut: 8188)')
        parser.add_argument('--protocol', choices=['http', 'https'], default='http', help='Protocole (défaut: http)')
        parser.add_argument('--api-key', help='Clé API ComfyUI')
        parser.add_argument('--timeout', type=int, default=30, help='Timeout en secondes (défaut: 30)')
        parser.add_argument('--no-ssl-verify', action='store_true', help='Désactiver la vérification SSL')
        
        # Arguments de vérification
        parser.add_argument('--test-loading', action='store_true', help='Effectuer des tests de chargement des modèles')
        parser.add_argument('--scan-only', action='store_true', help='Scanner uniquement les répertoires (pas API)')
        parser.add_argument('--full', action='store_true', help='Vérification complète (défaut)')
        
        # Arguments de sortie
        parser.add_argument('--output', default='./rapports', help='Répertoire de sortie pour les rapports')
        parser.add_argument('--verbose', action='store_true', help='Logs détaillés')
        
        return parser
    
    def run_verification(self, args) -> bool:
        """
        Exécute la vérification des modèles Qwen
        
        Args:
            args: Arguments parseés
            
        Returns:
            True si succès, False sinon
        """
        logger.info("🚀 Démarrage de la vérification des modèles Qwen...")
        
        # Mettre à jour la configuration
        self.config.host = args.host
        self.config.port = args.port
        self.config.protocol = args.protocol
        self.config.api_key = args.api_key
        self.config.timeout = args.timeout
        self.config.verify_ssl = not args.no_ssl_verify
        
        # Initialiser le vérificateur
        self.verifier = QwenModelVerifier(self.config)
        
        try:
            # Vérification de l'accessibilité
            verification_results = self.verifier.verify_model_accessibility()
            
            # Tests de chargement si demandé
            test_results = None
            if args.test_loading:
                test_results = self.verifier.test_model_loading()
            
            # Générer le rapport
            report = self.verifier.generate_verification_report(verification_results, test_results)
            
            # Afficher le rapport
            if args.verbose:
                print(report)
            else:
                print("📊 Rapport généré - utilisez --verbose pour les détails")
                print(f"📁 Modèles trouvés: {len(verification_results.get('models_found', []))}")
                print(f"❌ Modèles manquants: {len(verification_results.get('models_missing', []))}")
                print(f"⚠️ Problèmes: {len(verification_results.get('issues', []))}")
            
            # Sauvegarder le rapport
            success = self.verifier.save_report(report, args.output)
            if success:
                print(f"✅ Rapport sauvegardé dans: {args.output}")
            else:
                print("❌ Erreur sauvegarde du rapport")
            
            return success
            
        except KeyboardInterrupt:
            print("\n⏹️ Vérification interrompue par l'utilisateur")
            return False
        except Exception as e:
            logger.error(f"❌ Erreur lors de la vérification: {e}")
            return False
    
    def run(self, args=None):
        """
        Point d'entrée principal
        """
        if args is None:
            parser = self.setup_parser()
            args = parser.parse_args()
        
        # Configurer le niveau de logging
        if args.verbose:
            logging.getLogger().setLevel(logging.DEBUG)
        
        return self.run_verification(args)


def main():
    """
    Fonction principale
    """
    cli = QwenVerificationCLI()
    return cli.run()


if __name__ == "__main__":
    sys.exit(main())