#!/usr/bin/env python3
"""
validate-comfyui-auth.py - Script de validation one-liner pour ComfyUI-Login

Ce script teste l'ensemble de la chaîne d'authentification :
1. Vérification de la disponibilité du service
2. Récupération du token valide (Source de vérité)
3. Test de connexion (Login)
4. Test d'accès API protégé
5. Rapport de diagnostic

Usage:
    python scripts/genai-auth/validate-comfyui-auth.py

Auteur: Roo Code Mode (Phase 32)
Date: 2025-11-30
"""

import argparse
import logging
import sys
import json
import requests
import time
from pathlib import Path

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("ValidateComfyUI")

# Constantes
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
SECRETS_DIR = PROJECT_ROOT / ".secrets"
COMFYUI_URL = "http://localhost:8188"

class ValidationManager:
    def __init__(self):
        self.session = requests.Session()
        self.token = None
        self.raw_token = None

    def log_step(self, message: str):
        logger.info(f"\n{'='*50}")
        logger.info(f"🔍 TEST: {message}")
        logger.info(f"{'='*50}")

    def get_valid_token(self) -> bool:
        self.log_step("Récupération du token valide")
        
        config_path = SECRETS_DIR / "comfyui_auth_tokens.conf"
        if not config_path.exists():
            logger.error(f"❌ Configuration des tokens introuvable: {config_path}")
            return False
            
        try:
            with open(config_path, 'r') as f:
                config = json.load(f)
                self.token = config.get('bcrypt_hash')
                self.raw_token = config.get('raw_token')
                
            if not self.token:
                logger.error("❌ Token bcrypt manquant dans la configuration")
                return False
                
            logger.info("✅ Token récupéré depuis la source de vérité")
            return True
            
        except Exception as e:
            logger.error(f"❌ Erreur lecture configuration: {e}")
            return False

    def check_service_health(self) -> bool:
        self.log_step("Vérification de la santé du service")
        
        try:
            # Test sans auth (devrait retourner 401 ou 403 si auth active, 200 sinon)
            response = self.session.get(COMFYUI_URL, timeout=5)
            
            if response.status_code == 200:
                logger.warning("⚠️ Service accessible SANS authentification (Auth désactivée ?)")
                return True
            elif response.status_code in [401, 403]:
                logger.info(f"✅ Service actif et protégé (HTTP {response.status_code})")
                return True
            else:
                logger.error(f"❌ Code statut inattendu: {response.status_code}")
                return False
                
        except requests.ConnectionError:
            logger.error("❌ Impossible de se connecter à ComfyUI (Service éteint ?)")
            return False
        except Exception as e:
            logger.error(f"❌ Erreur connexion: {e}")
            return False

    def test_login(self) -> bool:
        self.log_step("Test de connexion (Login)")
        
        if not self.token:
            logger.error("❌ Pas de token disponible pour le test")
            return False

        # Essayer avec le token en Bearer (méthode standard API)
        headers = {
            "Authorization": f"Bearer {self.token}"
        }
        
        try:
            # Endpoint système pour vérifier l'auth
            response = self.session.get(f"{COMFYUI_URL}/system_stats", headers=headers, timeout=5)
            
            if response.status_code == 200:
                logger.info("✅ Authentification réussie (Bearer Token)")
                return True
            else:
                logger.error(f"❌ Échec authentification (HTTP {response.status_code})")
                logger.error(f"Réponse: {response.text[:200]}")
                
                # Tentative de diagnostic : essayer avec le raw token (ne devrait pas marcher mais instructif)
                if self.raw_token:
                    logger.info("Diagnostic: Tentative avec token brut...")
                    headers_raw = {"Authorization": f"Bearer {self.raw_token}"}
                    resp_raw = self.session.get(f"{COMFYUI_URL}/system_stats", headers=headers_raw, timeout=5)
                    if resp_raw.status_code == 200:
                        logger.error("🚨 ALERTE SÉCURITÉ: Le token brut est accepté ! (Mauvaise config bcrypt)")
                    else:
                        logger.info("ℹ️ Le token brut est correctement rejeté")
                
                return False
                
        except Exception as e:
            logger.error(f"❌ Erreur lors du test de login: {e}")
            return False

    def test_api_access(self) -> bool:
        self.log_step("Test d'accès API (Prompt)")
        
        headers = {
            "Authorization": f"Bearer {self.token}"
        }
        
        # Workflow minimal de test (juste pour valider que l'API accepte le JSON)
        prompt = {
            "3": {
                "class_type": "KSampler",
                "inputs": {
                    "seed": 1,
                    "steps": 1,
                    "cfg": 1.0,
                    "sampler_name": "euler",
                    "scheduler": "normal",
                    "denoise": 1.0,
                    "model": ["4", 0],
                    "positive": ["6", 0],
                    "negative": ["7", 0],
                    "latent_image": ["5", 0]
                }
            }
        }
        
        try:
            # On ne s'attend pas à ce que ça marche (pas de modèles chargés), 
            # mais on veut voir si l'API accepte la requête (pas de 401/403)
            response = self.session.post(
                f"{COMFYUI_URL}/prompt", 
                json={"prompt": prompt}, 
                headers=headers, 
                timeout=5
            )
            
            if response.status_code == 200:
                logger.info("✅ API Prompt accessible (HTTP 200)")
                return True
            elif response.status_code == 400:
                # 400 est bon signe ici : l'auth est passée, c'est le prompt qui est invalide (normal)
                logger.info("✅ API Prompt atteinte (HTTP 400 - Erreur de validation attendue)")
                return True
            else:
                logger.error(f"❌ Échec accès API (HTTP {response.status_code})")
                return False
                
        except Exception as e:
            logger.error(f"❌ Erreur lors du test API: {e}")
            return False

    def run(self) -> bool:
        logger.info("🚀 DÉMARRAGE DE LA VALIDATION COMFYUI-AUTH")
        
        if not self.get_valid_token():
            return False
            
        if not self.check_service_health():
            return False
            
        login_success = self.test_login()
        api_success = self.test_api_access()
        
        if login_success and api_success:
            logger.info("\n✨ VALIDATION RÉUSSIE : SYSTÈME OPÉRATIONNEL ✨")
            return True
        else:
            logger.error("\n❌ VALIDATION ÉCHOUÉE : PROBLÈMES DÉTECTÉS")
            return False

def main():
    manager = ValidationManager()
    success = manager.run()
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()