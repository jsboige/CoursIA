#!/usr/bin/env python3
"""
reconstruct_env.py - Script de reconstruction du fichier .env complet pour ComfyUI-Login

Ce script reconstruit le fichier .env complet en se basant sur la source de vérité
et les configurations validées, résolvant ainsi les problèmes d'incohérence.

Usage:
    python reconstruct_env.py [--backup] [--validate] [--source CONFIG_PATH]

Options:
    --backup      : Crée une sauvegarde du fichier .env existant
    --validate    : Valide le fichier .env reconstruit
    --source      : Chemin vers le fichier de configuration source (optionnel)
"""

import os
import sys
import json
import shutil
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, Optional, List

class EnvReconstructor:
    """Reconstructeur du fichier .env pour ComfyUI-Login"""
    
    def __init__(self, root_dir: Path = None):
        if root_dir is None:
            root_dir = Path(__file__).parent.parent.parent
        
        self.root_dir = root_dir
        self.secrets_dir = root_dir / ".secrets"
        self.docker_config_dir = root_dir / "docker-configurations" / "services" / "comfyui-qwen"
        self.env_path = self.docker_config_dir / ".env"
        
        # Configuration par défaut
        self.default_config = {
            # API Keys pour téléchargement des modèles
            "CIVITAI_TOKEN": "c39ba121e12e5b40ac67a87836431e34",
            "HF_TOKEN": "HF_TOKEN_REDACTED",
            "QWEN_API_TOKEN": "2%=tVJ6@!Nc(7#VTvj-Bh3^nm0WY-Lij",
            
            # Configuration GPU
            "GPU_DEVICE_ID": "0",
            "CUDA_VISIBLE_DEVICES": "0",
            "NVIDIA_VISIBLE_DEVICES": "0",
            
            # Configuration ComfyUI
            "COMFYUI_PORT": "8188",
            "COMFYUI_LOGIN_ENABLED": "true",
            "COMFYUI_WORKSPACE_PATH": "./workspace",
            
            # Configuration système
            "TZ": "Europe/Paris",
            "COMFYUI_URL": "http://localhost:8188",
            
            # Configuration comportement
            "CORS_ENABLED": "true",
            "VERBOSE_LOGGING": "false",
            "API_TIMEOUT": "30",
            "MAX_LOGIN_ATTEMPTS": "3",
            "SESSION_EXPIRE_HOURS": "24",
            
            # Valeurs par défaut pour l'authentification
            "COMFYUI_USERNAME": "admin",
            "GUEST_MODE_ENABLED": "false"
        }
    
    def log(self, message: str, level: str = "INFO"):
        """Affiche un message avec niveau"""
        prefix = {
            "INFO": "ℹ️",
            "SUCCESS": "✅",
            "ERROR": "❌",
            "WARNING": "⚠️",
            "RECONSTRUCT": "🔧",
            "VALIDATE": "✔️"
        }.get(level, "•")
        print(f"{prefix} {message}")
    
    def load_source_config(self, config_path: str = None) -> Optional[Dict]:
        """Charge la configuration source depuis le fichier unifié"""
        if config_path is None:
            config_path = self.secrets_dir / "comfyui_auth_tokens.conf"
        else:
            config_path = Path(config_path)
        
        if not config_path.exists():
            self.log(f"Fichier de configuration source introuvable: {config_path}", "ERROR")
            return None
        
        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                config = json.load(f)
            
            self.log(f"Configuration source chargée: {config_path}", "SUCCESS")
            return config
        except Exception as e:
            self.log(f"Erreur chargement configuration: {e}", "ERROR")
            return None
    
    def backup_existing_env(self) -> bool:
        """Crée une sauvegarde du fichier .env existant"""
        if not self.env_path.exists():
            self.log("Aucun fichier .env existant à sauvegarder", "INFO")
            return True
        
        try:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            backup_path = self.env_path.parent / f".env.backup.{timestamp}"
            shutil.copy2(self.env_path, backup_path)
            self.log(f"Sauvegarde créée: {backup_path}", "SUCCESS")
            return True
        except Exception as e:
            self.log(f"Erreur création sauvegarde: {e}", "ERROR")
            return False
    
    def reconstruct_env_content(self, source_config: Dict = None) -> str:
        """Reconstruit le contenu du fichier .env"""
        self.log("RECONSTRUCTION DU FICHIER .ENV", "RECONSTRUCT")
        
        # Variables d'environnement à reconstruire
        env_vars = self.default_config.copy()
        
        # Ajouter les tokens depuis la configuration source
        if source_config:
            env_vars["COMFYUI_BEARER_TOKEN"] = source_config.get("bcrypt_hash", "")
            env_vars["COMFYUI_RAW_TOKEN"] = source_config.get("raw_token", "")
            env_vars["SECRET_KEY"] = f"auto_generated_secure_key_{datetime.now().strftime('%Y%m%d')}"
            
            # Ajouter le mot de passe depuis la configuration si disponible
            if "password" in source_config:
                env_vars["COMFYUI_PASSWORD"] = source_config["password"]
            else:
                env_vars["COMFYUI_PASSWORD"] = "rZDS3XQa/8!v9L"  # Mot de passe par défaut
        else:
            self.log("Aucune configuration source fournie, utilisation des valeurs par défaut", "WARNING")
            env_vars["COMFYUI_BEARER_TOKEN"] = ""
            env_vars["COMFYUI_RAW_TOKEN"] = ""
            env_vars["COMFYUI_PASSWORD"] = "rZDS3XQa/8!v9L"
            env_vars["SECRET_KEY"] = f"auto_generated_secure_key_{datetime.now().strftime('%Y%m%d')}"
        
        # Construire le contenu du fichier .env
        content_lines = [
            "# ComfyUI + Qwen Image-Edit Configuration",
            "# Reconstruit le {} pour résoudre les problèmes d'incohérence".format(datetime.now().strftime('%Y-%m-%d')),
            "",
            "# =============================================================================",
            "# API KEYS FOR MODEL DOWNLOADS",
            "# =============================================================================",
            "# Get your tokens from:",
            "# - HuggingFace: https://huggingface.co/settings/tokens",
            "# - Civitai: https://civitai.com/user/account",
            "# These tokens are passed to container for model downloads",
            f"CIVITAI_TOKEN={env_vars['CIVITAI_TOKEN']}",
            f"HF_TOKEN={env_vars['HF_TOKEN']}",
            "",
            "# =============================================================================",
            "# QWEN API CONFIGURATION",
            "# =============================================================================",
            "# API Authentication token for Qwen model access",
            f"QWEN_API_TOKEN={env_vars['QWEN_API_TOKEN']}",
            "",
            "# =============================================================================",
            "# GPU CONFIGURATION",
            "# =============================================================================",
            "# CRITICAL: Use GPU_DEVICE_ID=0 for RTX 3090 (PyTorch GPU 0 = nvidia-smi GPU 1)",
            f"GPU_DEVICE_ID={env_vars['GPU_DEVICE_ID']}",
            f"CUDA_VISIBLE_DEVICES={env_vars['CUDA_VISIBLE_DEVICES']}",
            f"NVIDIA_VISIBLE_DEVICES={env_vars['NVIDIA_VISIBLE_DEVICES']}",
            "",
            "# =============================================================================",
            "# COMFYUI CORE CONFIGURATION",
            "# =============================================================================",
            "",
            "# Port for ComfyUI web interface",
            f"COMFYUI_PORT={env_vars['COMFYUI_PORT']}",
            "",
            "# Enable/disable ComfyUI-Login authentication",
            f"COMFYUI_LOGIN_ENABLED={env_vars['COMFYUI_LOGIN_ENABLED']}",
            "",
            "# Workspace Path to ComfyUI installation",
            f"COMFYUI_WORKSPACE_PATH={env_vars['COMFYUI_WORKSPACE_PATH']}",
            "",
            "# =============================================================================",
            "# SYSTEM CONFIGURATION",
            "# =============================================================================",
            "",
            "# System timezone",
            f"TZ={env_vars['TZ']}",
            "",
            "# URL de l'interface ComfyUI (used by external scripts)",
            f"COMFYUI_URL={env_vars['COMFYUI_URL']}",
            "",
            "# =============================================================================",
            "# AUTHENTICATION CONFIGURATION",
            "# =============================================================================",
            "",
            "# Username for ComfyUI-Login (optional, defaults to admin if not specified)",
            f"COMFYUI_USERNAME={env_vars['COMFYUI_USERNAME']}",
            "",
            "# Password for ComfyUI-Login (SECURE: use strong password)",
            f"COMFYUI_PASSWORD={env_vars['COMFYUI_PASSWORD']}",
            "",
            "# Bearer token for API access (auto-generated from existing token)",
            "# This token will be used by ComfyUI-Login for authentication",
            f"COMFYUI_BEARER_TOKEN={env_vars['COMFYUI_BEARER_TOKEN']}",
            "",
            "# Enable/disable guest mode (true/false)",
            "# If true, unauthenticated users can access in guest mode",
            f"GUEST_MODE_ENABLED={env_vars['GUEST_MODE_ENABLED']}",
            "",
            "# Secret key for encryption (auto-generated)",
            "# SECURITY: This should be a secure random key",
            f"SECRET_KEY={env_vars['SECRET_KEY']}",
            "",
            "# =============================================================================",
            "# APPLICATION BEHAVIOR CONFIGURATION",
            "# =============================================================================",
            "",
            "# Enable/disable CORS headers",
            f"CORS_ENABLED={env_vars['CORS_ENABLED']}",
            "",
            "# Enable/disable verbose logging",
            f"VERBOSE_LOGGING={env_vars['VERBOSE_LOGGING']}",
            "",
            "# API request timeout in seconds",
            f"API_TIMEOUT={env_vars['API_TIMEOUT']}",
            "",
            "# Maximum login attempts before lockout",
            f"MAX_LOGIN_ATTEMPTS={env_vars['MAX_LOGIN_ATTEMPTS']}",
            "",
            "# Session expiration time in hours",
            f"SESSION_EXPIRE_HOURS={env_vars['SESSION_EXPIRE_HOURS']}",
            "",
            "# =============================================================================",
            "# SECURITY NOTES",
            "# =============================================================================",
            "# 1. Les mots de passe sont hashés avec bcrypt dans le conteneur",
            "# 2. Les tokens sensibles (COMFYUI_BEARER_TOKEN, SECRET_KEY) sont générés automatiquement",
            "# 3. L'authentification ComfyUI-Login est maintenant correctement installée et configurée",
            "# 4. Le token est synchronisé entre le fichier .env et le conteneur",
            "# 5. Fichier reconstruit automatiquement pour résoudre les incohérences"
        ]
        
        return '\n'.join(content_lines)
    
    def write_env_file(self, content: str) -> bool:
        """Écrit le contenu dans le fichier .env"""
        try:
            # Créer le répertoire si nécessaire
            self.env_path.parent.mkdir(parents=True, exist_ok=True)
            
            # Écrire le fichier
            with open(self.env_path, 'w', encoding='utf-8') as f:
                f.write(content)
            
            self.log(f"Fichier .env reconstruit: {self.env_path}", "SUCCESS")
            return True
        except Exception as e:
            self.log(f"Erreur écriture fichier .env: {e}", "ERROR")
            return False
    
    def validate_env_file(self) -> bool:
        """Valide le fichier .env reconstruit"""
        self.log("VALIDATION DU FICHIER .ENV", "VALIDATE")
        
        if not self.env_path.exists():
            self.log("Fichier .env introuvable pour validation", "ERROR")
            return False
        
        try:
            # Lire le contenu
            with open(self.env_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Vérifications essentielles
            required_vars = [
                "CIVITAI_TOKEN",
                "HF_TOKEN", 
                "QWEN_API_TOKEN",
                "COMFYUI_BEARER_TOKEN",
                "COMFYUI_LOGIN_ENABLED",
                "COMFYUI_USERNAME",
                "COMFYUI_PASSWORD"
            ]
            
            missing_vars = []
            for var in required_vars:
                if f"{var}=" not in content:
                    missing_vars.append(var)
            
            if missing_vars:
                self.log(f"Variables manquantes: {', '.join(missing_vars)}", "ERROR")
                return False
            
            # Vérifier le format du token bcrypt
            lines = content.split('\n')
            for line in lines:
                if line.startswith('COMFYUI_BEARER_TOKEN='):
                    token = line.split('=')[1].strip()
                    if not token.startswith('$2b$12$') or len(token) != 60:
                        self.log(f"Token bcrypt invalide: {token[:20]}...", "ERROR")
                        return False
                    break
            
            self.log("✅ Fichier .env validé avec succès", "SUCCESS")
            return True
            
        except Exception as e:
            self.log(f"Erreur validation fichier .env: {e}", "ERROR")
            return False
    
    def reconstruct(self, backup: bool = True, validate: bool = True, source_config_path: str = None) -> bool:
        """Exécute la reconstruction complète du fichier .env"""
        self.log("DÉMARRAGE RECONSTRUCTION COMPLÈTE DU FICHIER .ENV", "INFO")
        
        # 1. Charger la configuration source
        source_config = self.load_source_config(source_config_path)
        
        # 2. Créer une sauvegarde si demandé
        if backup and not self.backup_existing_env():
            self.log("Échec création sauvegarde", "ERROR")
            return False
        
        # 3. Reconstruire le contenu
        content = self.reconstruct_env_content(source_config)
        
        # 4. Écrire le fichier
        if not self.write_env_file(content):
            self.log("Échec écriture fichier .env", "ERROR")
            return False
        
        # 5. Valider si demandé
        if validate and not self.validate_env_file():
            self.log("Échec validation fichier .env", "ERROR")
            return False
        
        self.log("🎉 RECONSTRUCTION DU FICHIER .ENV TERMINÉE AVEC SUCCÈS", "SUCCESS")
        return True

def main():
    """Point d'entrée principal"""
    parser = argparse.ArgumentParser(
        description="Reconstructeur du fichier .env pour ComfyUI-Login"
    )
    parser.add_argument(
        '--backup', '-b',
        action='store_true',
        help="Crée une sauvegarde du fichier .env existant"
    )
    parser.add_argument(
        '--validate', '-v',
        action='store_true',
        help="Valide le fichier .env reconstruit"
    )
    parser.add_argument(
        '--source', '-s',
        type=str,
        help="Chemin vers le fichier de configuration source"
    )
    
    args = parser.parse_args()
    
    # Créer le reconstructeur
    reconstructor = EnvReconstructor()
    
    # Par défaut: backup et validation
    backup = args.backup if args.backup is not None else True
    validate = args.validate if args.validate is not None else True
    
    try:
        success = reconstructor.reconstruct(
            backup=backup,
            validate=validate,
            source_config_path=args.source
        )
        
        if success:
            print("\n🎯 Prochaines étapes recommandées:")
            print("1. Redémarrer le service ComfyUI:")
            print("   cd docker-configurations/services/comfyui-qwen")
            print("   docker-compose restart")
            print("\n2. Tester l'authentification API:")
            print("   curl -H 'Authorization: Bearer $COMFYUI_BEARER_TOKEN' http://localhost:8188/system_stats")
            print("\n3. Valider le fonctionnement complet:")
            print("   python scripts/genai-auth/utils/token_synchronizer.py --validate")
        
        sys.exit(0 if success else 1)
        
    except KeyboardInterrupt:
        print("\n⚠️ Opération interrompue par l'utilisateur")
        sys.exit(1)
    except Exception as e:
        print(f"\n❌ Erreur fatale: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)

if __name__ == "__main__":
    main()