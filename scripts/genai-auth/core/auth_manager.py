#!/usr/bin/env python3
"""
auth_manager.py - Gestionnaire Centralisé d'Authentification GenAI

Ce module consolide toutes les opérations liées à l'authentification :
- Génération de secrets (Tokens, Hashs)
- Synchronisation multi-environnements (Windows -> WSL -> Docker)
- Audit de sécurité et validation de cohérence
- Interface unique pour récupérer les credentials dans les autres scripts

Auteur: Consolidation Phase 36
Date: 2025-12-12
"""

import os
import sys
import json
import logging
import secrets
import time
import string
import shutil
import bcrypt
import argparse
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime
from dataclasses import dataclass, asdict

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger("AuthManager")

# Constantes
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
SECRETS_DIR = PROJECT_ROOT / ".secrets"
CONFIG_FILE = SECRETS_DIR / "comfyui_auth_tokens.conf"

@dataclass
class TokenLocation:
    """Représente un emplacement de token"""
    path: str
    type: str  # 'bcrypt', 'raw', 'env'
    description: str
    exists: bool = False
    content: Optional[str] = None
    is_valid: bool = False

@dataclass
class AuditReport:
    """Rapport d'audit des tokens"""
    timestamp: str
    locations: List[TokenLocation]
    inconsistencies: List[Dict]
    recommendations: List[str]
    
    def to_dict(self):
        return {
            'timestamp': self.timestamp,
            'locations': [asdict(loc) for loc in self.locations],
            'inconsistencies': self.inconsistencies,
            'recommendations': self.recommendations
        }

class GenAIAuthManager:
    """Gestionnaire principal d'authentification (Singleton Facade)"""
    
    def __init__(self, root_dir: Path = None):
        self.root_dir = root_dir if root_dir else PROJECT_ROOT
        self.secrets_dir = self.root_dir / ".secrets"
        self.secrets_dir.mkdir(exist_ok=True, parents=True)
        self.config_file = self.secrets_dir / "comfyui_auth_tokens.conf"
        
        # Emplacements connus pour l'audit
        self.docker_config_dir = self.root_dir / "docker-configurations" / "services" / "comfyui-qwen"
        
    # =========================================================================
    # 1. GESTION DES SECRETS (Génération & Hashage)
    # =========================================================================
    
    def generate_secure_token(self, length: int = 32) -> str:
        """Génère un token aléatoire sécurisé"""
        alphabet = string.ascii_letters + string.digits
        return ''.join(secrets.choice(alphabet) for i in range(length))

    def generate_bcrypt_hash(self, password: str, rounds: int = 12) -> str:
        """Génère un hash bcrypt du mot de passe"""
        salt = bcrypt.gensalt(rounds=rounds)
        hashed = bcrypt.hashpw(password.encode('utf-8'), salt)
        return hashed.decode('utf-8')

    def validate_bcrypt_pair(self, raw_token: str, bcrypt_hash: str) -> bool:
        """Valide la correspondance entre token brut et hash bcrypt"""
        try:
            return bcrypt.checkpw(raw_token.encode('utf-8'), bcrypt_hash.encode('utf-8'))
        except Exception as e:
            logger.error(f"Erreur validation bcrypt: {e}")
            return False

    def is_bcrypt_hash(self, token: str) -> bool:
        """Vérifie si une chaîne ressemble à un hash bcrypt valide"""
        if not token: return False
        return token.startswith('$2b$') or token.startswith('$2a$') or token.startswith('$2y$')

    # =========================================================================
    # 2. GESTION DE LA CONFIGURATION (Source de Vérité)
    # =========================================================================

    def load_config(self) -> Optional[Dict]:
        """Charge la configuration d'auth unifiée"""
        if not self.config_file.exists():
            return None
        try:
            with open(self.config_file, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception as e:
            logger.error(f"Erreur chargement config: {e}")
            return None

    def create_unified_config(self, raw_token: str = None) -> bool:
        """Crée ou recrée la configuration unifiée"""
        logger.info("🔐 Création configuration unifiée...")
        
        try:
            if not raw_token:
                raw_token = self.generate_secure_token()
                logger.info("Nouveau token généré")
            
            bcrypt_hash = self.generate_bcrypt_hash(raw_token)
            
            config = {
                'version': '1.0',
                'updated_at': datetime.now().isoformat(),
                'raw_token': raw_token,
                'bcrypt_hash': bcrypt_hash,
                'services': {
                    'comfyui-qwen': {
                        'locations': [
                            {'type': 'secrets_file', 'path': str(self.secrets_dir / "qwen-api-user.token")},
                            {'type': 'env_file', 'path': str(self.docker_config_dir / ".env")},
                            {'type': 'docker_secrets', 'path': str(self.docker_config_dir / ".secrets" / "qwen-api-user.token")}
                        ]
                    }
                }
            }
            
            with open(self.config_file, 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=2)
            
            # Mettre à jour les permissions (lecture seule pour user si possible)
            try:
                os.chmod(self.config_file, 0o600)
            except:
                pass
                
            logger.info(f"✅ Configuration sauvegardée: {self.config_file}")
            return True
            
        except Exception as e:
            logger.error(f"❌ Erreur création config: {e}")
            return False

    # =========================================================================
    # 3. SYNCHRONISATION (Déploiement)
    # =========================================================================

    def synchronize_credentials(self) -> bool:
        """Synchronise les credentials vers tous les emplacements définis"""
        config = self.load_config()
        if not config:
            logger.error("Configuration introuvable. Veuillez d'abord générer les tokens.")
            return False
            
        logger.info("🔄 Synchronisation des credentials...")
        success_count = 0
        total_ops = 0
        
        raw_token = config.get('raw_token')
        bcrypt_hash = config.get('bcrypt_hash')
        
        for service, details in config.get('services', {}).items():
            for loc in details.get('locations', []):
                total_ops += 1
                path = Path(loc['path'])
                type_ = loc['type']
                
                try:
                    # Assurer que le dossier parent existe
                    path.parent.mkdir(parents=True, exist_ok=True)
                    
                    if type_ in ['secrets_file', 'docker_secrets']:
                        # Écriture directe du hash
                        path.write_text(bcrypt_hash, encoding='utf-8')
                        logger.info(f"✅ Écrit hash dans: {path}")
                        success_count += 1
                        
                    elif type_ == 'env_file':
                        # Mise à jour intelligente du .env
                        self._update_env_file(path, raw_token, bcrypt_hash)
                        logger.info(f"✅ Mis à jour .env: {path}")
                        success_count += 1
                        
                except Exception as e:
                    logger.error(f"❌ Erreur synchro {path}: {e}")
        
        logger.info(f"Synchronisation terminée: {success_count}/{total_ops} opérations réussies.")
        return success_count == total_ops

    def _update_env_file(self, env_path: Path, raw_token: str, bcrypt_hash: str):
        """Met à jour les variables d'auth dans un fichier .env sans toucher au reste"""
        if not env_path.exists():
            # Créer nouveau si n'existe pas
            content = f"COMFYUI_API_TOKEN={bcrypt_hash}\nCOMFYUI_RAW_TOKEN={raw_token}\n"
            env_path.write_text(content, encoding='utf-8')
            return

        lines = env_path.read_text(encoding='utf-8').splitlines()
        new_lines = []
        updated_keys = set()
        
        # Mapping des clés à mettre à jour
        updates = {
            'COMFYUI_API_TOKEN': bcrypt_hash,
            'COMFYUI_BEARER_TOKEN': bcrypt_hash, # Alias souvent utilisé
            'QWEN_API_USER_TOKEN': bcrypt_hash,  # Legacy
            'COMFYUI_RAW_TOKEN': raw_token,
            'COMFYUI_PASSWORD': raw_token        # Pour login simple
        }
        
        for line in lines:
            if not line.strip() or line.startswith('#'):
                new_lines.append(line)
                continue
                
            key = line.split('=')[0].strip()
            if key in updates:
                new_lines.append(f"{key}={updates[key]}")
                updated_keys.add(key)
            else:
                new_lines.append(line)
        
        # Ajouter les clés manquantes importantes (au moins une version du token)
        if 'COMFYUI_API_TOKEN' not in updated_keys:
            new_lines.append(f"COMFYUI_API_TOKEN={updates['COMFYUI_API_TOKEN']}")
            
        env_path.write_text('\n'.join(new_lines) + '\n', encoding='utf-8')

    def reconstruct_env_file(self, backup: bool = True) -> bool:
        """Reconstruit le fichier .env complet à partir de modèles sûrs"""
        env_path = self.docker_config_dir / ".env"
        
        if backup and env_path.exists():
            backup_path = env_path.with_suffix(f".backup.{int(time.time())}")
            try:
                shutil.copy2(env_path, backup_path)
                logger.info(f"Backup .env créé: {backup_path}")
            except Exception as e:
                logger.error(f"Erreur backup .env: {e}")
                return False

        config = self.load_config()
        if not config:
            logger.error("Config auth manquante pour reconstruction .env")
            return False

        # Modèle par défaut
        content = f"""# ComfyUI + Qwen Configuration (Reconstruit par AuthManager)
# Date: {datetime.now().isoformat()}

# --- API KEYS ---
CIVITAI_TOKEN=c39ba121e12e5b40ac67a87836431e34
HF_TOKEN=HF_TOKEN_REDACTED
QWEN_API_TOKEN={config.get('bcrypt_hash')}

# --- GPU ---
GPU_DEVICE_ID=0
CUDA_VISIBLE_DEVICES=0
NVIDIA_VISIBLE_DEVICES=0

# --- COMFYUI ---
COMFYUI_PORT=8188
COMFYUI_LOGIN_ENABLED=true
COMFYUI_WORKSPACE_PATH=./workspace
TZ=Europe/Paris
COMFYUI_URL=http://localhost:8188

# --- AUTH ---
COMFYUI_USERNAME=admin
COMFYUI_PASSWORD={config.get('raw_token')}
COMFYUI_BEARER_TOKEN={config.get('bcrypt_hash')}
GUEST_MODE_ENABLED=false
SECRET_KEY={self.generate_secure_token(40)}

# --- SYSTEM ---
CORS_ENABLED=true
VERBOSE_LOGGING=false
API_TIMEOUT=30
MAX_LOGIN_ATTEMPTS=3
SESSION_EXPIRE_HOURS=24
"""
        try:
            env_path.parent.mkdir(parents=True, exist_ok=True)
            env_path.write_text(content, encoding='utf-8')
            logger.info(f"✅ Fichier .env reconstruit: {env_path}")
            return True
        except Exception as e:
            logger.error(f"Erreur écriture .env: {e}")
            return False

    # =========================================================================
    # 4. AUDIT & VALIDATION
    # =========================================================================

    def audit_security(self) -> AuditReport:
        """Audite l'état de sécurité des tokens"""
        logger.info("🔍 Audit de sécurité en cours...")
        
        config = self.load_config()
        if not config:
            return AuditReport(datetime.now().isoformat(), [], [], ["Initialiser la configuration avec 'init'"])
            
        ref_hash = config.get('bcrypt_hash')
        locations = []
        inconsistencies = []
        
        # Scanner les emplacements configurés
        for service, details in config.get('services', {}).items():
            for loc in details.get('locations', []):
                path = Path(loc['path'])
                exists = path.exists()
                content = None
                is_valid = False
                
                if exists:
                    try:
                        raw_content = path.read_text(encoding='utf-8').strip()
                        
                        if loc['type'] == 'env_file':
                            # Analyse simple .env
                            if f"={ref_hash}" in raw_content:
                                is_valid = True
                                content = "[ENV_MATCH]"
                            else:
                                content = "[ENV_MISMATCH]"
                        else:
                            content = raw_content
                            is_valid = (content == ref_hash)
                    except:
                        content = "[READ_ERROR]"
                
                locations.append(TokenLocation(
                    path=str(path),
                    type=loc['type'],
                    description=f"{service} - {loc['type']}",
                    exists=exists,
                    content=content[:20]+"..." if content and len(content)>20 else content,
                    is_valid=is_valid
                ))
                
                if exists and not is_valid:
                    inconsistencies.append({
                        'path': str(path),
                        'issue': 'Content mismatch with reference hash'
                    })
        
        recommendations = []
        if inconsistencies:
            recommendations.append("Exécuter 'sync' pour corriger les incohérences")
            
        return AuditReport(
            timestamp=datetime.now().isoformat(),
            locations=locations,
            inconsistencies=inconsistencies,
            recommendations=recommendations
        )

    # =========================================================================
    # 5. UTILITAIRES PUBLICS
    # =========================================================================

    def get_auth_header(self) -> Dict[str, str]:
        """Retourne le header Authorization prêt à l'emploi pour les clients API"""
        config = self.load_config()
        if not config or 'bcrypt_hash' not in config:
            raise ValueError("Authentification non configurée")
        
        token = config['bcrypt_hash']
        # Si le token stocké n'a pas le préfixe Bearer, on l'ajoute. 
        # Mais attention, certains systèmes stockent déjà "Bearer <token>" ? 
        # Dans notre cas, on stocke le hash brut.
        return {
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json"
        }

# =========================================================================
# CLI
# =========================================================================

def main():
    parser = argparse.ArgumentParser(description="GenAI Authentication Manager")
    subparsers = parser.add_subparsers(dest='command', help='Commandes disponibles')
    
    # Init / Generate
    cmd_init = subparsers.add_parser('init', help='Initialiser/Générer nouvelle configuration')
    cmd_init.add_argument('--force', action='store_true', help='Écraser configuration existante')
    
    # Sync
    subparsers.add_parser('sync', help='Synchroniser les credentials partout')
    
    # Audit
    cmd_audit = subparsers.add_parser('audit', help='Auditer la sécurité')
    cmd_audit.add_argument('--json', action='store_true', help='Sortie JSON')
    
    # Get Token (pour scripts shell)
    cmd_get = subparsers.add_parser('get-token', help='Récupérer le token (pour scripts)')
    cmd_get.add_argument('--raw', action='store_true', help='Retourner le token brut au lieu du hash')
    
    # Reconstruct Env
    subparsers.add_parser('reconstruct-env', help='Reconstruire le fichier .env')

    args = parser.parse_args()
    manager = GenAIAuthManager()
    
    if args.command == 'init':
        if manager.config_file.exists() and not args.force:
            print("⚠️ Configuration existante. Utilisez --force pour écraser.")
            sys.exit(1)
        manager.create_unified_config()
        manager.synchronize_credentials() # Auto-sync after init
        
    elif args.command == 'sync':
        manager.synchronize_credentials()
        
    elif args.command == 'audit':
        report = manager.audit_security()
        if args.json:
            print(json.dumps(report.to_dict(), indent=2))
        else:
            print(f"\n🔍 RAPPORT D'AUDIT ({report.timestamp})")
            print("="*60)
            for loc in report.locations:
                status = "✅" if loc.is_valid else "❌" if loc.exists else "⚠️ MISSING"
                print(f"{status} {loc.description}")
                print(f"   Path: {loc.path}")
            
            if report.inconsistencies:
                print("\n❌ INCOHÉRENCES DÉTECTÉES!")
                for inc in report.inconsistencies:
                    print(f" - {inc['path']}: {inc['issue']}")
            else:
                print("\n✅ Tous les systèmes sont cohérents.")
                
    elif args.command == 'get-token':
        config = manager.load_config()
        if not config:
            sys.exit(1)
        print(config.get('raw_token' if args.raw else 'bcrypt_hash', ''))
        
    elif args.command == 'reconstruct-env':
        if manager.reconstruct_env_file():
            sys.exit(0)
        else:
            sys.exit(1)

    else:
        parser.print_help()

if __name__ == "__main__":
    main()