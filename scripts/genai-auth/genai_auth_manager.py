#!/usr/bin/env python3
"""
Gestionnaire principal d'authentification GenAI - Script consolidé paramétrique

Ce script consolide les fonctionnalités d'authentification :
- Génération de tokens Bearer sécurisés
- Configuration de l'authentification pour différents services
- Validation des tokens existants
- Diagnostic des problèmes d'authentification
- Gestion des environnements d'authentification

Auteur: Consolidation des scripts d'authentification existants
Date: 2025-10-31
Version: 1.0.0
"""

import argparse
import bcrypt
import secrets
import string
import sys
import os
import json
import logging
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Any

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('genai_auth_manager.log'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

class GenAIAuthManager:
    """Gestionnaire principal d'authentification GenAI"""
    
    def __init__(self, config_file: Optional[str] = None):
        self.config_file = Path(config_file) if config_file else Path.cwd() / "genai_auth_config.json"
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
            "services": {
                "comfyui-qwen": {
                    "host": "localhost",
                    "port": 8188,
                    "protocol": "http",
                    "api_key_file": ".secrets/qwen-api-user.token",
                    "env_var": "QWEN_API_TOKEN"
                },
                "comfyui-forge": {
                    "host": "localhost", 
                    "port": 8188,
                    "protocol": "http",
                    "api_key_file": ".secrets/forge-api-user.token",
                    "env_var": "FORGE_API_TOKEN"
                }
            },
            "token_settings": {
                "password_length": 32,
                "bcrypt_work_factor": 12,
                "token_format": "bearer",
                "backup_enabled": True
            },
            "security": {
                "allowed_chars": string.ascii_letters + string.digits + "!@#$%^&*()_+",
                "session_timeout": 3600,
                "max_retries": 3
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
    
    def generate_secure_password(self, length: int = 32) -> str:
        """Génère un mot de passe sécurisé aléatoire"""
        charset = self.config["security"]["allowed_chars"]
        return ''.join(secrets.choice(charset) for _ in range(length))
    
    def generate_bcrypt_hash(self, password: str, work_factor: int = None) -> str:
        """Génère un hash bcrypt du mot de passe"""
        if work_factor is None:
            work_factor = self.config["token_settings"]["bcrypt_work_factor"]
        
        salt = bcrypt.gensalt(rounds=work_factor)
        hashed = bcrypt.hashpw(password.encode('utf-8'), salt)
        return hashed.decode('utf-8')
    
    def generate_tokens(self, service: str, username: str = None, output_dir: str = None) -> bool:
        """Génère des tokens Bearer pour un service spécifique"""
        logger.info(f"Génération de tokens pour le service: {service}")
        
        if service not in self.config["services"]:
            logger.error(f"Service inconnu: {service}")
            return False
        
        service_config = self.config["services"][service]
        
        if username is None:
            username = service.replace("-", "_") + "-api-user"
        
        if output_dir is None:
            output_dir = Path(".secrets")
        else:
            output_dir = Path(output_dir)
        
        # Créer le répertoire de sortie
        output_dir.mkdir(exist_ok=True)
        logger.info(f"Répertoire de sortie: {output_dir.absolute()}")
        
        # Générer le mot de passe
        password_length = self.config["token_settings"]["password_length"]
        password = self.generate_secure_password(password_length)
        
        # Hasher le mot de passe
        work_factor = self.config["token_settings"]["bcrypt_work_factor"]
        logger.info(f"Hachage avec bcrypt (work factor: {work_factor})...")
        hashed_password = self.generate_bcrypt_hash(password, work_factor)
        
        # Créer le fichier .token
        token_file = output_dir / f"{username}.token"
        logger.info(f"Création du fichier token: {token_file}")
        token_file.write_text(hashed_password, encoding='utf-8')
        
        # Créer le fichier .env.generated
        env_file = output_dir / ".env.generated"
        env_var_name = service_config["env_var"]
        env_content = f"{env_var_name}={password}\n"
        env_file.write_text(env_content, encoding='utf-8')
        
        # Afficher les résultats
        print("\n" + "="*60)
        print("🎉 GÉNÉRATION DE TOKENS TERMINÉE 🎉")
        print("="*60)
        print(f"Service : {service}")
        print(f"Utilisateur : {username}")
        print(f"Mot de passe: {password}")
        print(f"Hash bcrypt : {hashed_password[:20]}...{hashed_password[-10:]}")
        print("-"*60)
        print(f"✅ Fichier token créé : {token_file}")
        print(f"✅ Fichier .env créé  : {env_file}")
        print("-"*60)
        print("\n⚠️  IMPORTANT: Stockez ce mot de passe en lieu sûr!")
        print(f"⚠️  Le fichier {env_file} contient le token brut.")
        print("\n")
        
        return True
    
    def validate_tokens(self, service: str) -> Dict[str, Any]:
        """Valide les tokens existants pour un service"""
        logger.info(f"Validation des tokens pour le service: {service}")
        
        if service not in self.config["services"]:
            logger.error(f"Service inconnu: {service}")
            return {"error": f"Service inconnu: {service}"}
        
        service_config = self.config["services"][service]
        token_file = Path(service_config["api_key_file"])
        
        validation_results = {
            "service": service,
            "token_file": str(token_file),
            "token_exists": token_file.exists(),
            "env_var_set": os.environ.get(service_config["env_var"]) is not None,
            "validation_timestamp": datetime.now().isoformat(),
            "issues": []
        }
        
        if not token_file.exists():
            validation_results["issues"].append(f"Fichier token manquant: {token_file}")
        
        # Vérifier le format du token
        if token_file.exists():
            try:
                with open(token_file, 'r', encoding='utf-8') as f:
                    token_content = f.read().strip()
                
                # Vérifier si c'est un hash bcrypt
                if token_content.startswith('$2'):
                    validation_results["issues"].append("Le token contient un hash bcrypt au lieu du token brut")
                    validation_results["token_format"] = "hashed"
                else:
                    validation_results["token_format"] = "plain"
                    validation_results["token_length"] = len(token_content)
                
            except Exception as e:
                validation_results["issues"].append(f"Erreur lecture token: {e}")
        
        return validation_results
    
    def diagnose_auth_issues(self, service: str) -> Dict[str, Any]:
        """Diagnostic des problèmes d'authentification pour un service"""
        logger.info(f"Diagnostic des problèmes d'authentification pour: {service}")
        
        if service not in self.config["services"]:
            logger.error(f"Service inconnu: {service}")
            return {"error": f"Service inconnu: {service}"}
        
        service_config = self.config["services"][service]
        
        diagnostic_results = {
            "service": service,
            "diagnostic_timestamp": datetime.now().isoformat(),
            "checks": {},
            "recommendations": [],
            "issues": []
        }
        
        # Vérifier la connectivité au service
        try:
            import requests
            base_url = f"{service_config['protocol']}://{service_config['host']}:{service_config['port']}"
            response = requests.get(f"{base_url}/system_stats", timeout=5)
            
            if response.status_code == 200:
                diagnostic_results["checks"]["connectivity"] = {
                    "status": "success",
                    "response_time": response.elapsed.total_seconds()
                }
            else:
                diagnostic_results["checks"]["connectivity"] = {
                    "status": "failed",
                    "error_code": response.status_code,
                    "error_message": response.text[:200]
                }
                diagnostic_results["issues"].append(f"Service inaccessible: HTTP {response.status_code}")
        
        except Exception as e:
            diagnostic_results["checks"]["connectivity"] = {
                "status": "error",
                "error": str(e)
            }
            diagnostic_results["issues"].append(f"Erreur de connectivité: {e}")
        
        # Vérifier la configuration de l'environnement
        env_var = service_config["env_var"]
        if os.environ.get(env_var):
            diagnostic_results["checks"]["environment"] = {
                "status": "configured",
                "env_var": env_var
            }
        else:
            diagnostic_results["checks"]["environment"] = {
                "status": "missing",
                "env_var": env_var
            }
            diagnostic_results["recommendations"].append(f"Configurer la variable d'environnement {env_var}")
        
        return diagnostic_results
    
    def list_services(self) -> List[str]:
        """Liste tous les services configurés"""
        return list(self.config["services"].keys())
    
    def add_service(self, service_name: str, service_config: Dict[str, Any]) -> bool:
        """Ajoute un nouveau service à la configuration"""
        try:
            self.config["services"][service_name] = service_config
            self._save_config()
            logger.info(f"Service {service_name} ajouté à la configuration")
            return True
        except Exception as e:
            logger.error(f"Erreur ajout service: {e}")
            return False
    
    def remove_service(self, service_name: str) -> bool:
        """Supprime un service de la configuration"""
        try:
            if service_name in self.config["services"]:
                del self.config["services"][service_name]
                self._save_config()
                logger.info(f"Service {service_name} supprimé de la configuration")
                return True
            else:
                logger.warning(f"Service {service_name} non trouvé dans la configuration")
                return False
        except Exception as e:
            logger.error(f"Erreur suppression service: {e}")
            return False
    
    def show_config(self):
        """Affiche la configuration actuelle"""
        print("📋 CONFIGURATION ACTUELLE GENAI AUTH MANAGER")
        print("=" * 50)
        print(json.dumps(self.config, indent=2))
        print("=" * 50)

def main():
    """Fonction principale du gestionnaire d'authentification"""
    parser = argparse.ArgumentParser(
        description='Gestionnaire principal d\'authentification GenAI - Script consolidé paramétrique',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples d'utilisation:
  # Générer des tokens pour ComfyUI Qwen
  python genai-auth-manager.py generate --service comfyui-qwen
  
  # Valider les tokens existants
  python genai-auth-manager.py validate --service comfyui-qwen
  
  # Diagnostiquer les problèmes d'authentification
  python genai-auth-manager.py diagnose --service comfyui-qwen
  
  # Lister tous les services
  python genai-auth-manager.py list-services
  
  # Afficher la configuration actuelle
  python genai-auth-manager.py show-config
  
  # Ajouter un nouveau service
  python genai-auth-manager.py add-service --name mon-service --config '{"host": "localhost", "port": 8080}'
        """
    )
    
    parser.add_argument(
        '--config',
        help='Chemin vers le fichier de configuration (défaut: genai_auth_config.json)'
    )
    
    subparsers = parser.add_subparsers(dest='action', help='Action à exécuter')
    
    # Sous-commande generate
    generate_parser = subparsers.add_parser('generate', help='Générer des tokens')
    generate_parser.add_argument('--service', required=True, help='Service cible')
    generate_parser.add_argument('--username', help='Nom d\'utilisateur (défaut: auto-généré)')
    generate_parser.add_argument('--output-dir', help='Répertoire de sortie (défaut: .secrets)')
    
    # Sous-commande validate
    validate_parser = subparsers.add_parser('validate', help='Valider les tokens existants')
    validate_parser.add_argument('--service', required=True, help='Service à valider')
    
    # Sous-commande diagnose
    diagnose_parser = subparsers.add_parser('diagnose', help='Diagnostiquer les problèmes d\'authentification')
    diagnose_parser.add_argument('--service', required=True, help='Service à diagnostiquer')
    
    # Sous-commande list-services
    subparsers.add_parser('list-services', help='Lister tous les services configurés')
    
    # Sous-commande show-config
    subparsers.add_parser('show-config', help='Afficher la configuration actuelle')
    
    # Sous-commande add-service
    add_service_parser = subparsers.add_parser('add-service', help='Ajouter un nouveau service')
    add_service_parser.add_argument('--name', required=True, help='Nom du service')
    add_service_parser.add_argument('--config', required=True, help='Configuration JSON du service')
    
    args = parser.parse_args()
    
    # Initialiser le gestionnaire
    manager = GenAIAuthManager(args.config)
    
    # Exécuter l'action appropriée
    if args.action == 'generate':
        success = manager.generate_tokens(
            service=args.service,
            username=args.username,
            output_dir=args.output_dir
        )
        sys.exit(0 if success else 1)
    
    elif args.action == 'validate':
        results = manager.validate_tokens(args.service)
        print("\n📊 RÉSULTATS DE VALIDATION:")
        print(json.dumps(results, indent=2))
        sys.exit(0 if not results.get("error") else 1)
    
    elif args.action == 'diagnose':
        results = manager.diagnose_auth_issues(args.service)
        print("\n🔍 RÉSULTATS DU DIAGNOSTIC:")
        print(json.dumps(results, indent=2))
        sys.exit(0 if not results.get("error") else 1)
    
    elif args.action == 'list-services':
        services = manager.list_services()
        print("\n📋 SERVICES CONFIGURÉS:")
        for service in services:
            print(f"  - {service}")
        sys.exit(0)
    
    elif args.action == 'show-config':
        manager.show_config()
        sys.exit(0)
    
    elif args.action == 'add-service':
        try:
            service_config = json.loads(args.config)
            success = manager.add_service(args.name, service_config)
            sys.exit(0 if success else 1)
        except json.JSONDecodeError as e:
            print(f"❌ Erreur JSON dans la configuration: {e}")
            sys.exit(1)
    
    else:
        parser.print_help()
        sys.exit(1)

if __name__ == "__main__":
    main()