# scripts/genai-auth/utils/token_manager.py
"""
Gestionnaire centralisé des tokens d'authentification Qwen ComfyUI
Simplifie l'accès aux tokens pour tous les scripts
"""

import os
import json
from pathlib import Path
from typing import Optional, Dict, Any

class TokenManager:
    """Gestionnaire centralisé des tokens Qwen ComfyUI"""
    
    def __init__(self):
        # Remonter de utils -> genai-auth -> scripts -> racine du projet
        self.project_root = Path(__file__).parent.parent.parent.parent
        self.secrets_dir = self.project_root / ".secrets"
        self.token_file = self.secrets_dir / "qwen-api-user.token"
        self.env_file = self.secrets_dir / ".env.generated"
    
    def get_bcrypt_hash(self) -> str:
        """Récupère le hash bcrypt depuis le fichier token"""
        if not self.token_file.exists():
            raise FileNotFoundError(f"Fichier token non trouvé: {self.token_file}")
        
        return self.token_file.read_text().strip()
    
    def get_raw_token(self) -> str:
        """Récupère le token brut depuis le fichier .env"""
        if not self.env_file.exists():
            raise FileNotFoundError(f"Fichier .env non trouvé: {self.env_file}")
        
        with open(self.env_file) as f:
            for line in f:
                if line.startswith('QWEN_API_USER_TOKEN='):
                    return line.split('=', 1)[1].strip()
        
        raise ValueError("QWEN_API_USER_TOKEN non trouvé dans .env.generated")
    
    def get_auth_headers(self) -> Dict[str, str]:
        """Génère les headers d'authentification avec le HASH BCRYPT pour les requêtes API"""
        token = self.get_bcrypt_hash()
        return {
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json"
        }
    
    def validate_tokens(self) -> bool:
        """Valide que les fichiers de token existent et sont lisibles"""
        try:
            self.get_bcrypt_hash()
            self.get_raw_token()
            return True
        except Exception as e:
            print(f"❌ Erreur validation tokens: {e}")
            return False

# Instance globale pour faciliter l'utilisation
token_manager = TokenManager()