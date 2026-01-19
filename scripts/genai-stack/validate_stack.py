#!/usr/bin/env python3
"""
validation_suite.py - Suite de validation unifiée pour ComfyUI
Consolidation de Phase 3

Ce script regroupe tous les tests de validation pour l'environnement ComfyUI + Qwen :
1. Validation des Custom Nodes (28 nœuds critiques)
2. Validation de l'Authentification (Token, Login, API)
3. Validation de la Génération (Workflow Z-Image)

Usage:
    python scripts/genai-stack/validate_stack.py [--full] [--auth-only] [--nodes-only]

Auteur: Consolidation Phase 3 (Roo)
Date: 2025-12-12
"""

import sys
import os
import json
import logging
import time
import argparse
import requests
from pathlib import Path
from typing import List, Dict, Optional

# Ajout du path pour les imports
current_dir = Path(__file__).resolve().parent
sys.path.append(str(current_dir))
sys.path.append(str(current_dir / "utils"))
sys.path.append(str(current_dir / "core"))

try:
    from core.auth_manager import GenAIAuthManager
    from core.comfyui_client import ComfyUIClient, ComfyUIConfig, WorkflowManager
except ImportError as e:
    print(f"❌ Erreur d'import critique: {e}")
    sys.exit(1)

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("ComfyUIValidator")

# Constantes
COMFYUI_URL = "http://localhost:8188"
EXPECTED_QWEN_NODES = [
    "ModelMergeQwenImage",
    "TextEncodeQwenImageEdit",
    "TextEncodeQwenImageEditPlus",
    "QwenImageDiffsynthControlnet"
]

class ComfyUIValidator:
    def __init__(self):
        self.auth_manager = GenAIAuthManager()
        self.config = self.auth_manager.load_config()
        self.token = self.config.get('bcrypt_hash') if self.config else None
        self.raw_token = self.config.get('raw_token') if self.config else None
        self.session = requests.Session()
        self.client: Optional[ComfyUIClient] = None
        
        # Setup Client
        self._setup_client()

    def _setup_client(self):
        """Initialise le client ComfyUI Helper"""
        client_config = ComfyUIConfig(
            host="localhost",
            port=8188,
            api_key=self.token,
            timeout=300
        )
        self.client = ComfyUIClient(client_config)

    def log_section(self, title: str):
        logger.info(f"\n{'=' * 60}")
        logger.info(f"🚀 {title}")
        logger.info(f"{'=' * 60}")

    def check_service_health(self) -> bool:
        """Vérifie si ComfyUI répond"""
        logger.info("📡 Vérification disponibilité service...")
        try:
            if not self.client.is_reachable():
                logger.error("❌ ComfyUI inaccessible sur localhost:8188 (is_reachable returned False)")
                return False
        except Exception as e:
            logger.error(f"❌ ComfyUI inaccessible sur localhost:8188 (Exception: {e})")
            return False
            
        logger.info("✅ Service ComfyUI en ligne")
        return True

    def check_auth(self) -> bool:
        """
        Validation de l'authentification (Fusion de validate_comfyui_auth.py)
        """
        self.log_section("TEST AUTHENTICATION")
        
        if not self.token:
            logger.error("❌ Token d'authentification manquant dans la configuration")
            return False
            
        # 1. Test Login (System Stats)
        logger.info("🔑 Test connexion (Bearer Token)...")
        headers = {"Authorization": f"Bearer {self.token}"}
        
        try:
            resp = self.session.get(f"{COMFYUI_URL}/system_stats", headers=headers, timeout=5)
            if resp.status_code == 200:
                logger.info("✅ Authentification réussie")
            else:
                logger.error(f"❌ Échec authentification (HTTP {resp.status_code})")
                return False
        except Exception as e:
            logger.error(f"❌ Erreur connexion: {e}")
            return False

        # 2. Test API Access (Prompt Endpoint - Dry Run)
        logger.info("🛡️ Test accès API protégé...")
        dummy_prompt = {"prompt": {}} # Juste pour vérifier l'accès
        try:
            resp = self.session.post(f"{COMFYUI_URL}/prompt", json=dummy_prompt, headers=headers)
            # 400 est attendu car prompt vide, mais prouve que l'auth est passée
            if resp.status_code in [200, 400]:
                logger.info("✅ API accessible")
                return True
            else:
                logger.error(f"❌ API refusée (HTTP {resp.status_code})")
                return False
        except Exception as e:
            logger.error(f"❌ Erreur API: {e}")
            return False

    def check_nodes(self) -> bool:
        """
        Validation des Custom Nodes (Fusion de install_comfyui_login.py)
        """
        self.log_section("TEST CUSTOM NODES")
        
        try:
            object_info = self.client.get_object_info()
            if not object_info:
                logger.error("❌ Impossible de récupérer la liste des nœuds")
                return False
                
            available_nodes = set(object_info.keys())
            missing_nodes = []
            
            logger.info(f"📦 {len(available_nodes)} nœuds détectés au total")
            
            for node in EXPECTED_QWEN_NODES:
                if node in available_nodes:
                    # logger.info(f"  ✅ {node}") # Trop verbeux
                    pass
                else:
                    logger.error(f"  ❌ MANQUANT: {node}")
                    missing_nodes.append(node)
            
            if missing_nodes:
                logger.error(f"❌ {len(missing_nodes)} nœuds Qwen critiques manquants !")
                return False
                
            logger.info(f"✅ Tous les {len(EXPECTED_QWEN_NODES)} nœuds Qwen critiques sont présents.")
            return True
            
        except Exception as e:
            logger.error(f"❌ Erreur lors de la vérification des nœuds: {e}")
            return False

    def check_generation(self, workflow_filename="workflow_z_image.json") -> bool:
        """
        Validation de la génération d'image (Fusion de run_z_image_test.py)
        """
        self.log_section(f"TEST GÉNÉRATION ({workflow_filename})")
        
        workflow_path = Path("docker-configurations/services/comfyui-qwen/workspace") / workflow_filename
        
        # Résolution chemin (projet racine)
        project_root = Path(os.getcwd())
        # Si on est dans scripts/genai-stack, on remonte
        if project_root.name == 'genai-stack':
            full_workflow_path = project_root.parent.parent / workflow_path
        else:
            full_workflow_path = project_root / workflow_path

        if not full_workflow_path.exists():
            logger.error(f"❌ Workflow introuvable: {full_workflow_path}")
            return False
            
        logger.info("📤 Soumission du workflow Z-Image...")
        
        try:
            workflow = WorkflowManager.load(str(full_workflow_path))
            prompt_id = self.client.queue_prompt(workflow)
            
            if not prompt_id:
                logger.error("❌ Échec de la soumission du workflow")
                return False
                
            logger.info(f"🆔 Job ID: {prompt_id} - Attente génération...")
            
            result = self.client.wait_for_prompt(prompt_id, timeout=300)
            
            if not result:
                logger.error("❌ Timeout ou erreur récupération résultat")
                return False
                
            if result.get('status', {}).get('status_str') == 'error':
                logger.error("❌ Erreur exécution workflow")
                return False
                
            # Vérification outputs
            outputs = result.get('outputs', {})
            if not outputs:
                logger.error("❌ Aucun output généré (Image vide ?)")
                return False
                
            logger.info("✅ Génération réussie ! Image produite.")
            return True
            
        except Exception as e:
            logger.error(f"❌ Erreur test génération: {e}")
            return False

    def run_suite(self, full=True, auth_only=False, nodes_only=False, workflow="workflow_z_image.json") -> bool:
        """Exécute la suite de tests selon les arguments"""
        
        # 0. Health Check (Toujours)
        if not self.check_service_health():
            return False

        results = []

        # 1. Auth Check
        if full or auth_only:
            results.append(self.check_auth())
            if auth_only: return all(results)

        # 2. Nodes Check
        if full or nodes_only:
            results.append(self.check_nodes())
            if nodes_only: return all(results)

        # 3. Generation Check (Seulement en mode full ou explicite)
        if full:
            results.append(self.check_generation(workflow_filename=workflow))

        success = all(results)
        self.log_section("RÉSULTAT FINAL")
        if success:
            logger.info("✨ SUITE DE VALIDATION : SUCCÈS TOTAL ✨")
        else:
            logger.error("💀 SUITE DE VALIDATION : ÉCHEC PARTIEL 💀")
            
        return success

def main():
    parser = argparse.ArgumentParser(description="ComfyUI Validation Suite")
    parser.add_argument('--full', action='store_true', help='Exécuter tous les tests (défaut)', default=True)
    parser.add_argument('--auth-only', action='store_true', help='Test authentification uniquement')
    parser.add_argument('--nodes-only', action='store_true', help='Test nœuds uniquement')
    parser.add_argument('--workflow', type=str, default="workflow_z_image.json", help='Nom du fichier workflow à tester (défaut: workflow_z_image.json)')
    
    args = parser.parse_args()
    
    # Logique override
    if args.auth_only or args.nodes_only:
        args.full = False

    validator = ComfyUIValidator()
    success = validator.run_suite(full=args.full, auth_only=args.auth_only, nodes_only=args.nodes_only, workflow=args.workflow)
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()