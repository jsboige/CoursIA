#!/usr/bin/env python3
"""
Script de setup initial pour ComfyUI Qwen - Script consolidé paramétrique

Ce script consolide les fonctionnalités de setup initial pour ComfyUI Qwen :
- Initialisation complète de l'environnement
- Installation des dépendances
- Configuration de l'authentification
- Démarrage des services
- Validation du setup complet

Auteur: Consolidation des scripts de setup existants
Date: 2025-10-31
Version: 1.0.0
"""

import argparse
import json
import logging
import subprocess
import sys
import os
from pathlib import Path
from typing import Dict, List, Optional, Any
from datetime import datetime

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('qwen_setup.log'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

class QwenSetup:
    """Gestionnaire de setup initial pour ComfyUI Qwen"""
    
    def __init__(self, config_file: Optional[str] = None):
        self.config_file = Path(config_file) if config_file else Path.cwd() / "qwen_setup_config.json"
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
            "environment": {
                "python_version": "3.10",
                "venv_path": "/workspace/ComfyUI/venv",
                "workspace_path": "/workspace/ComfyUI",
                "models_path": "/workspace/ComfyUI/models",
                "docker_compose_path": "docker-configurations/comfyui-qwen/docker-compose.yml"
            },
            "services": {
                "comfyui-qwen": {
                    "enabled": True,
                    "auto_start": True,
                    "health_check": True
                }
            },
            "setup": {
                "install_dependencies": True,
                "configure_auth": True,
                "validate_setup": True,
                "create_directories": True,
                "backup_existing": True
            },
            "paths": {
                "secrets_dir": ".secrets",
                "logs_dir": "./logs",
                "backups_dir": "./backups"
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
    
    def check_prerequisites(self) -> Dict[str, Any]:
        """Vérifie les prérequis système"""
        logger.info("Vérification des prérequis système...")
        
        check_results = {
            "check_timestamp": datetime.now().isoformat(),
            "system": {},
            "dependencies": {},
            "issues": [],
            "recommendations": []
        }
        
        # Vérifier Python
        python_version = sys.version_info()
        check_results["system"]["python"] = {
            "version": python_version,
            "version_ok": python_version >= (3, 10),
            "executable": sys.executable
        }
        
        if not check_results["system"]["python"]["version_ok"]:
            check_results["issues"].append(f"Python {python_version} requis, version actuelle: {python_version}")
        
        # Vérifier les commandes système
        required_commands = ["docker", "docker-compose", "git"]
        missing_commands = []
        
        for cmd in required_commands:
            try:
                subprocess.run([cmd, "--version"], capture_output=True, check=True)
                logger.info(f"✅ {cmd} disponible")
            except (subprocess.CalledProcessError, FileNotFoundError):
                missing_commands.append(cmd)
                logger.warning(f"⚠️ {cmd} non trouvé")
        
        check_results["dependencies"]["commands"] = {
            "required": required_commands,
            "missing": missing_commands
        }
        
        if missing_commands:
            check_results["issues"].append("Commandes système manquantes")
            check_results["recommendations"].append("Installer les commandes manquantes")
        
        return check_results
    
    def setup_environment(self) -> bool:
        """Configure l'environnement ComfyUI Qwen"""
        logger.info("Configuration de l'environnement ComfyUI Qwen...")
        
        success = True
        
        # Créer les répertoires nécessaires
        directories_to_create = [
            self.config["paths"]["secrets_dir"],
            self.config["paths"]["logs_dir"],
            self.config["paths"]["backups_dir"]
        ]
        
        for directory in directories_to_create:
            try:
                Path(directory).mkdir(parents=True, exist_ok=True)
                logger.info(f"✅ Répertoire créé: {directory}")
            except Exception as e:
                logger.error(f"❌ Erreur création répertoire {directory}: {e}")
                success = False
        
        # Configuration des variables d'environnement
        env_vars = {
            "COMFYUI_HOST": "localhost",
            "COMFYUI_PORT": "8188",
            "COMFYUI_PROTOCOL": "http",
            "PYTHONPATH": self.config["environment"]["workspace_path"],
            "COMFYUI_MODELS_PATH": f"{self.config['environment']['workspace_path']}/models"
        }
        
        for var_name, var_value in env_vars.items():
            os.environ[var_name] = var_value
            logger.info(f"Variable d'environnement définie: {var_name}={var_value}")
        
        return success
    
    def install_dependencies(self) -> bool:
        """Installe les dépendances ComfyUI Qwen"""
        logger.info("Installation des dépendances ComfyUI Qwen...")
        
        if not self.config["setup"]["install_dependencies"]:
            logger.info("Installation des dépendances désactivée dans la configuration")
            return True
        
        success = True
        
        # Installation des dépendances Python
        python_packages = [
            "torch", "torchvision", "numpy", "Pillow", 
            "requests", "aiohttp", "cryptography", "bcrypt"
        ]
        
        for package in python_packages:
            try:
                logger.info(f"Installation de {package}...")
                result = subprocess.run([
                    sys.executable, "-m", "pip", "install", package
                ], capture_output=True, text=True)
                
                if result.returncode == 0:
                    logger.info(f"✅ {package} installé avec succès")
                else:
                    logger.error(f"❌ Échec installation {package}: {result.stderr}")
                    success = False
            except Exception as e:
                logger.error(f"❌ Erreur installation {package}: {e}")
                success = False
        
        return success
    
    def configure_authentication(self) -> bool:
        """Configure l'authentification ComfyUI Qwen"""
        logger.info("Configuration de l'authentification ComfyUI Qwen...")
        
        if not self.config["setup"]["configure_auth"]:
            logger.info("Configuration de l'authentification désactivée dans la configuration")
            return True
        
        success = True
        
        # Utiliser le gestionnaire d'authentification
        try:
            # Importer le gestionnaire d'authentification
            sys.path.insert(0, str(Path(__file__).parent))
            from genai_auth_manager import GenAIAuthManager
            
            auth_manager = GenAIAuthManager()
            
            # Générer des tokens pour ComfyUI Qwen
            if auth_manager.generate_tokens("comfyui-qwen"):
                logger.info("✅ Tokens ComfyUI Qwen générés avec succès")
            else:
                logger.error("❌ Échec génération tokens ComfyUI Qwen")
                success = False
        except Exception as e:
            logger.error(f"❌ Erreur configuration authentification: {e}")
            success = False
        
        return success
    
    def validate_setup(self) -> Dict[str, Any]:
        """Valide le setup complet"""
        logger.info("Validation du setup complet...")
        
        validation_results = {
            "validation_timestamp": datetime.now().isoformat(),
            "checks": {},
            "issues": [],
            "recommendations": []
        }
        
        # Vérifier l'environnement
        env_checks = {
            "comfyui_host": os.environ.get("COMFYUI_HOST") == "localhost",
            "comfyui_port": os.environ.get("COMFYUI_PORT") == "8188",
            "comfyui_protocol": os.environ.get("COMFYUI_PROTOCOL") == "http",
            "pythonpath_configured": "PYTHONPATH" in os.environ,
            "models_path_configured": "COMFYUI_MODELS_PATH" in os.environ
        }
        
        validation_results["checks"]["environment"] = {
            "status": "success" if all(env_checks.values()) else "partial",
            "details": env_checks
        }
        
        # Vérifier les répertoires
        required_dirs = [
            self.config["paths"]["secrets_dir"],
            self.config["paths"]["logs_dir"],
            self.config["paths"]["backups_dir"]
        ]
        
        for directory in required_dirs:
            if Path(directory).exists():
                validation_results["checks"]["directories"][directory] = {
                    "status": "exists",
                    "path": str(Path(directory).absolute())
                }
            else:
                validation_results["issues"].append(f"Répertoire manquant: {directory}")
        
        # Vérifier les dépendances
        try:
            import torch
            import torchvision
            import numpy
            import requests
            validation_results["checks"]["dependencies"] = {
                "status": "installed",
                "packages": ["torch", "torchvision", "numpy", "requests"]
            }
        except ImportError as e:
            validation_results["checks"]["dependencies"] = {
                "status": "missing",
                "error": str(e)
            }
            validation_results["issues"].append(f"Dépendances manquantes: {e}")
        
        return validation_results
    
    def run_full_setup(self) -> bool:
        """Exécute le setup complet"""
        logger.info("Exécution du setup complet pour ComfyUI Qwen...")
        
        success = True
        
        # Étape 1: Vérification des prérequis
        prereq_results = self.check_prerequisites()
        if prereq_results["issues"]:
            logger.error("❌ Prérequis non satisfaits")
            for issue in prereq_results["issues"]:
                logger.error(f"  - {issue}")
            success = False
        
        # Étape 2: Configuration de l'environnement
        if success:
            success = self.setup_environment()
        
        # Étape 3: Installation des dépendances
        if success:
            success = self.install_dependencies()
        
        # Étape 4: Configuration de l'authentification
        if success:
            success = self.configure_authentication()
        
        # Étape 5: Validation du setup
        if success and self.config["setup"]["validate_setup"]:
            validation_results = self.validate_setup()
            
            logger.info("📊 RÉSULTATS DE LA VALIDATION:")
            for check_name, check_result in validation_results["checks"].items():
                status_icon = "✅" if check_result.get("status") == "success" else "❌"
                logger.info(f"  {check_name}: {status_icon} {check_result.get('status')}")
            
            if validation_results["issues"]:
                logger.error("❌ Problèmes détectés:")
                for issue in validation_results["issues"]:
                    logger.error(f"  - {issue}")
            
            if validation_results["recommendations"]:
                logger.info("💡 Recommandations:")
                for rec in validation_results["recommendations"]:
                    logger.info(f"  - {rec}")
        
        return success
    
    def show_config(self):
        """Affiche la configuration actuelle"""
        print("🔧 CONFIGURATION QWEN SETUP MANAGER")
        print("=" * 50)
        print(json.dumps(self.config, indent=2))
        print("=" * 50)

def main():
    """Fonction principale du setup"""
    parser = argparse.ArgumentParser(
        description='Script de setup initial pour ComfyUI Qwen - Script consolidé paramétrique',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples d'utilisation:
  # Setup complet
  python qwen-setup.py --full-setup
  
  # Vérification des prérequis seulement
  python qwen-setup.py --check-prereqs
  
  # Configuration de l'environnement seulement
  python qwen-setup.py --setup-env
  
  # Installation des dépendances seulement
  python qwen-setup.py --install-deps
  
  # Configuration de l'authentification seulement
  python qwen-setup.py --setup-auth
  
  # Afficher la configuration actuelle
  python qwen-setup.py --show-config
        """
    )
    
    parser.add_argument(
        '--config',
        help='Chemin vers le fichier de configuration (défaut: qwen_setup_config.json)'
    )
    
    subparsers = parser.add_subparsers(dest='action', help='Action à exécuter')
    
    # Sous-commande full-setup
    subparsers.add_parser('full-setup', help='Exécute le setup complet')
    
    # Sous-commande check-prereqs
    subparsers.add_parser('check-prereqs', help='Vérifie les prérequis système')
    
    # Sous-commande setup-env
    subparsers.add_parser('setup-env', help='Configure l\'environnement ComfyUI')
    
    # Sous-commande install-deps
    subparsers.add_parser('install-deps', help='Installe les dépendances Python')
    
    # Sous-commande setup-auth
    subparsers.add_parser('setup-auth', help='Configure l\'authentification ComfyUI')
    
    # Sous-commande show-config
    subparsers.add_parser('show-config', help='Affiche la configuration actuelle')
    
    args = parser.parse_args()
    
    # Initialiser le gestionnaire
    setup = QwenSetup(args.config)
    
    # Exécuter l'action appropriée
    if args.action == 'full-setup':
        success = setup.run_full_setup()
        sys.exit(0 if success else 1)
    
    elif args.action == 'check-prereqs':
        results = setup.check_prerequisites()
        print("\n📋 RÉSULTATS DES PRÉREQUIS:")
        print(json.dumps(results, indent=2))
        sys.exit(0 if not results.get("issues") else 1)
    
    elif args.action == 'setup-env':
        success = setup.setup_environment()
        sys.exit(0 if success else 1)
    
    elif args.action == 'install-deps':
        success = setup.install_dependencies()
        sys.exit(0 if success else 1)
    
    elif args.action == 'setup-auth':
        success = setup.configure_authentication()
        sys.exit(0 if success else 1)
    
    elif args.action == 'show-config':
        setup.show_config()
        sys.exit(0)
    
    else:
        parser.print_help()
        sys.exit(1)

if __name__ == "__main__":
    main()