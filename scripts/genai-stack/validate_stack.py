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
from typing import List, Dict, Optional, Any

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

# Nodes Qwen natifs (fournis par ComfyUI core)
EXPECTED_QWEN_NODES = [
    "ModelMergeQwenImage",
    "TextEncodeQwenImageEdit",
    "TextEncodeQwenImageEditPlus",
    "QwenImageDiffsynthControlnet"
]

# Nodes natifs ComfyUI requis pour le workflow Qwen Phase 29
REQUIRED_NATIVE_NODES = [
    "VAELoader",
    "CLIPLoader",
    "UNETLoader",
    "ModelSamplingAuraFlow",
    "CFGNorm",
    "ConditioningZeroOut",
    "EmptySD3LatentImage",
    "KSampler",
    "VAEDecode",
    "SaveImage"
]

# Mapping notebooks -> services requis (noms reels des fichiers)
NOTEBOOK_SERVICE_MAP = {
    # Cloud-only (pas de GPU local requis)
    "cloud": [
        "00-1-Environment-Setup.ipynb",
        "00-2-Docker-Services-Management.ipynb",
        "00-3-API-Endpoints-Configuration.ipynb",
        "00-4-Environment-Validation.ipynb",
        "00-5-ComfyUI-Local-Test.ipynb",
        "01-1-OpenAI-DALL-E-3.ipynb",
        "01-2-GPT-5-Image-Generation.ipynb",
        "01-3-Basic-Image-Operations.ipynb",
    ],
    # Forge-Turbo (GPU 1 - RTX 3080 Ti)
    "forge": [
        "01-4-Forge-SD-XL-Turbo.ipynb",
    ],
    # ComfyUI-Qwen (GPU 0 - RTX 3090, ~29GB VRAM)
    "qwen": [
        "01-5-Qwen-Image-Edit.ipynb",
        "02-1-Qwen-Image-Edit-2509.ipynb",
    ],
    # ComfyUI Z-Image (GPU 0 - RTX 3090, ~10GB VRAM)
    "zimage": [
        "02-4-Z-Image-Lumina2.ipynb",
    ],
    # Multi-model (necessite switching)
    "multi": [
        "02-2-FLUX-1-Advanced-Generation.ipynb",
        "02-3-Stable-Diffusion-3-5.ipynb",
        "03-1-Multi-Model-Comparison.ipynb",
        "03-2-Workflow-Orchestration.ipynb",
        "03-3-Performance-Optimization.ipynb",
    ],
    # Applications (mixte)
    "apps": [
        "04-1-Educational-Content-Generation.ipynb",
        "04-2-Creative-Workflows.ipynb",
        "04-3-Production-Integration.ipynb",
    ],
}

# Services externes
FORGE_URL = "http://localhost:17861"


class VRAMManager:
    """Gestion VRAM via ComfyUI /free endpoint."""

    def __init__(self, comfyui_client: 'ComfyUIClient'):
        self.client = comfyui_client

    def free_vram(self, unload_models: bool = True) -> dict:
        """Libere la VRAM via POST /free."""
        try:
            return self.client.free_memory(unload_models=unload_models)
        except Exception as e:
            logger.error(f"Erreur liberation VRAM: {e}")
            return {"error": str(e)}

    def get_vram_stats(self) -> dict:
        """Recupere stats VRAM via /system_stats."""
        try:
            stats = self.client.get_system_stats()
            devices = stats.get('devices', [])
            if devices:
                gpu = devices[0]
                return {
                    "vram_total": gpu.get('vram_total', 0),
                    "vram_free": gpu.get('vram_free', 0),
                    "torch_vram_total": gpu.get('torch_vram_total', 0),
                    "torch_vram_free": gpu.get('torch_vram_free', 0),
                }
            return {}
        except Exception as e:
            logger.error(f"Erreur stats VRAM: {e}")
            return {"error": str(e)}


class ModelSwitcher:
    """Switch entre modeles Qwen et Z-Image avec gestion VRAM."""

    MODEL_CONFIGS = {
        # Qwen 2511 Q4_K_M - Version recommandee (compatible RTX 3090)
        "qwen": {
            "unet": "qwen-image-edit-2511-Q4_K_M.gguf",
            "clip": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
            "vae": "qwen_image_vae.safetensors",
            "lora": "Qwen-Image-Edit-2511-Lightning-4steps-V1.0-bf16.safetensors",
            "vram_required_mb": 13100,  # Q4_K_M: ~13GB
            "steps": 4,  # Avec Lightning LoRA
            "cfg": 1.0,
        },
        # Qwen 2509 FP8 - Version legacy (necessite offload)
        "qwen_fp8": {
            "unet": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
            "clip": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
            "vae": "qwen_image_vae.safetensors",
            "vram_required_mb": 29000,  # FP8: ~29GB
            "steps": 20,
            "cfg": 1.0,
        },
        # Z-Image Lumina
        "zimage": {
            "checkpoint": "Lumina-Next-SFT",
            "unet": "z_image_turbo-Q5_K_M.gguf",
            "vae": "sdxl_vae.safetensors",
            "vram_required_mb": 10000,
        },
    }

    def __init__(self, vram_manager: VRAMManager):
        self.vram = vram_manager
        self.current_model: Optional[str] = None

    def switch_to(self, model_name: str) -> bool:
        """Change de modele avec liberation VRAM prealable."""
        if model_name not in self.MODEL_CONFIGS:
            logger.error(f"Modele inconnu: {model_name}")
            return False

        if self.current_model == model_name:
            logger.info(f"Modele {model_name} deja charge")
            return True

        logger.info(f"Switch vers modele: {model_name}")

        # Liberer VRAM actuelle
        logger.info("Liberation VRAM...")
        result = self.vram.free_vram(unload_models=True)
        if "error" in result:
            logger.warning(f"Attention lors liberation VRAM: {result['error']}")

        # Attendre liberation effective
        time.sleep(2)

        # Verifier VRAM disponible
        stats = self.vram.get_vram_stats()
        if stats and "error" not in stats:
            vram_free_mb = stats.get('vram_free', 0) / (1024 * 1024)
            required_mb = self.MODEL_CONFIGS[model_name]['vram_required_mb']
            logger.info(f"VRAM libre: {vram_free_mb:.0f}MB, requis: {required_mb}MB")

        self.current_model = model_name
        return True


class BatchNotebookValidator:
    """Validation batch de notebooks avec switching automatique de modeles."""

    def __init__(self, model_switcher: ModelSwitcher, notebooks_dir: Path = None):
        self.switcher = model_switcher
        self.notebooks_dir = notebooks_dir or Path("MyIA.AI.Notebooks/GenAI")
        self.results: Dict[str, Dict[str, Any]] = {}

    def _find_notebook(self, notebook_name: str) -> Optional[Path]:
        """Recherche un notebook dans l'arborescence."""
        for path in self.notebooks_dir.rglob(notebook_name):
            return path
        # Recherche pattern partiel
        for path in self.notebooks_dir.rglob(f"*{notebook_name}*"):
            if path.suffix == ".ipynb":
                return path
        return None

    def _validate_notebook_syntax(self, notebook_path: Path) -> Dict[str, Any]:
        """Validation syntaxique basique (JSON valide, structure notebook)."""
        try:
            with open(notebook_path, 'r', encoding='utf-8') as f:
                nb = json.load(f)

            if 'cells' not in nb:
                return {"valid": False, "error": "Missing 'cells' key"}
            if 'metadata' not in nb:
                return {"valid": False, "error": "Missing 'metadata' key"}

            cell_count = len(nb['cells'])
            code_cells = sum(1 for c in nb['cells'] if c.get('cell_type') == 'code')

            return {
                "valid": True,
                "cell_count": cell_count,
                "code_cells": code_cells,
                "path": str(notebook_path)
            }
        except json.JSONDecodeError as e:
            return {"valid": False, "error": f"JSON invalide: {e}"}
        except Exception as e:
            return {"valid": False, "error": str(e)}

    def validate_group(self, group: str) -> Dict[str, Any]:
        """Valide un groupe de notebooks."""
        if group not in NOTEBOOK_SERVICE_MAP:
            return {"error": f"Groupe inconnu: {group}"}

        notebooks = NOTEBOOK_SERVICE_MAP[group]
        logger.info(f"Validation groupe '{group}': {len(notebooks)} notebooks")

        # Switch modele si necessaire
        if group in ["qwen", "zimage"]:
            self.switcher.switch_to(group)

        results = {}
        for nb_name in notebooks:
            nb_path = self._find_notebook(nb_name)
            if nb_path:
                results[nb_name] = self._validate_notebook_syntax(nb_path)
            else:
                results[nb_name] = {"valid": False, "error": "Notebook introuvable"}

        self.results[group] = results
        return results

    def run_full_validation(self) -> Dict[str, Dict[str, Any]]:
        """Execute validation complete dans l'ordre optimal."""
        # Ordre: cloud -> forge -> qwen -> zimage -> multi -> apps
        sequence = ["cloud", "forge", "qwen", "zimage", "multi", "apps"]

        for group in sequence:
            self.validate_group(group)

        return self.results

    def print_summary(self):
        """Affiche un resume des resultats."""
        total = 0
        valid = 0

        for group, notebooks in self.results.items():
            group_valid = sum(1 for r in notebooks.values() if r.get("valid", False))
            group_total = len(notebooks)
            total += group_total
            valid += group_valid

            status = "OK" if group_valid == group_total else "PARTIEL"
            logger.info(f"  {group}: {group_valid}/{group_total} {status}")

        logger.info(f"TOTAL: {valid}/{total} notebooks valides")
        return valid == total


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
        Validation des Custom Nodes et Nodes Natifs requis pour Qwen Phase 29
        """
        self.log_section("TEST NODES (Qwen + Natifs)")

        try:
            object_info = self.client.get_object_info()
            if not object_info:
                logger.error("Impossible de recuperer la liste des noeuds")
                return False

            available_nodes = set(object_info.keys())
            missing_qwen = []
            missing_native = []

            logger.info(f"{len(available_nodes)} noeuds detectes au total")

            # 1. Verification nodes Qwen natifs
            logger.info("Verification nodes Qwen natifs...")
            for node in EXPECTED_QWEN_NODES:
                if node in available_nodes:
                    pass
                else:
                    logger.error(f"  MANQUANT (Qwen): {node}")
                    missing_qwen.append(node)

            # 2. Verification nodes natifs requis pour workflow
            logger.info("Verification nodes natifs requis...")
            for node in REQUIRED_NATIVE_NODES:
                if node in available_nodes:
                    pass
                else:
                    logger.error(f"  MANQUANT (natif): {node}")
                    missing_native.append(node)

            # Resultat
            if missing_qwen:
                logger.error(f"{len(missing_qwen)} noeuds Qwen manquants: {missing_qwen}")
            else:
                logger.info(f"OK: {len(EXPECTED_QWEN_NODES)} noeuds Qwen presents")

            if missing_native:
                logger.error(f"{len(missing_native)} noeuds natifs manquants: {missing_native}")
            else:
                logger.info(f"OK: {len(REQUIRED_NATIVE_NODES)} noeuds natifs presents")

            return len(missing_qwen) == 0 and len(missing_native) == 0

        except Exception as e:
            logger.error(f"Erreur lors de la verification des noeuds: {e}")
            return False

    def check_generation(self, workflow_filename="workflow_qwen_native_t2i.json") -> bool:
        """
        Validation de la generation d'image avec workflow Qwen natif Phase 29
        """
        self.log_section(f"TEST GENERATION ({workflow_filename})")

        # Chercher le workflow dans plusieurs emplacements
        workflow_paths = [
            Path("scripts/genai-stack/workflows") / workflow_filename,
            Path("docker-configurations/services/comfyui-qwen/workspace") / workflow_filename
        ]
        workflow_path = None
        for wp in workflow_paths:
            if wp.exists():
                workflow_path = wp
                break
        if not workflow_path:
            workflow_path = workflow_paths[0]  # Default
        
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
            
        logger.info(f"Soumission du workflow {workflow_filename}...")
        
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

    def run_suite(self, full=True, auth_only=False, nodes_only=False, workflow="workflow_qwen_native_t2i.json") -> bool:
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

def check_forge_api() -> bool:
    """Verifie si Forge-Turbo est accessible."""
    try:
        resp = requests.get(f"{FORGE_URL}/sdapi/v1/sd-models", timeout=5)
        if resp.status_code == 200:
            logger.info(f"OK Forge-Turbo accessible sur {FORGE_URL}")
            return True
        else:
            logger.warning(f"Forge-Turbo repond avec HTTP {resp.status_code}")
            return False
    except Exception as e:
        logger.warning(f"Forge-Turbo inaccessible: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description="ComfyUI Validation Suite avec Model Switching",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples:
  python validate_stack.py --full              # Validation ComfyUI complete
  python validate_stack.py --notebooks         # Validation syntaxe notebooks
  python validate_stack.py --with-switching    # Validation notebooks + switching modeles
  python validate_stack.py --group qwen        # Validation groupe specifique
  python validate_stack.py --dry-run           # Check syntax seulement
        """
    )

    # Mode ComfyUI (existant)
    parser.add_argument('--full', action='store_true', help='Executer tous les tests ComfyUI (defaut)', default=True)
    parser.add_argument('--auth-only', action='store_true', help='Test authentification uniquement')
    parser.add_argument('--nodes-only', action='store_true', help='Test noeuds uniquement')
    parser.add_argument('--workflow', type=str, default="workflow_qwen_native_t2i.json",
                        help='Workflow a tester (defaut: workflow_qwen_native_t2i.json)')

    # Mode Notebooks (nouveau)
    parser.add_argument('--notebooks', action='store_true', help='Validation syntaxe notebooks GenAI')
    parser.add_argument('--with-switching', action='store_true',
                        help='Validation notebooks avec switching modeles automatique')
    parser.add_argument('--group', type=str, choices=['cloud', 'forge', 'qwen', 'zimage', 'multi', 'apps'],
                        help='Valider un groupe specifique de notebooks')
    parser.add_argument('--dry-run', action='store_true', help='Check syntax seulement (pas de generation)')
    parser.add_argument('--check-forge', action='store_true', help='Verifier aussi Forge-Turbo API')

    args = parser.parse_args()

    # Logique mode
    if args.auth_only or args.nodes_only:
        args.full = False

    success = True

    # Mode Notebooks
    if args.notebooks or args.with_switching or args.group:
        logger.info("\n" + "=" * 60)
        logger.info("VALIDATION NOTEBOOKS GENAI")
        logger.info("=" * 60)

        # Setup validation chain
        validator = ComfyUIValidator()

        if args.with_switching and not validator.check_service_health():
            logger.error("ComfyUI requis pour --with-switching")
            sys.exit(1)

        vram_mgr = VRAMManager(validator.client) if validator.client else None
        model_switcher = ModelSwitcher(vram_mgr) if vram_mgr else None

        # Utiliser un ModelSwitcher factice si pas de client
        if model_switcher is None:
            class DummySwitcher:
                current_model = None
                def switch_to(self, m): return True
            model_switcher = DummySwitcher()

        batch_validator = BatchNotebookValidator(model_switcher)

        if args.group:
            results = batch_validator.validate_group(args.group)
            valid_count = sum(1 for r in results.values() if r.get("valid", False))
            success = valid_count == len(results)
        else:
            batch_validator.run_full_validation()
            success = batch_validator.print_summary()

    # Mode ComfyUI standard
    elif args.full or args.auth_only or args.nodes_only:
        validator = ComfyUIValidator()
        success = validator.run_suite(
            full=args.full,
            auth_only=args.auth_only,
            nodes_only=args.nodes_only,
            workflow=args.workflow
        )

    # Check Forge supplementaire
    if args.check_forge:
        forge_ok = check_forge_api()
        success = success and forge_ok

    # Resume final
    logger.info("\n" + "=" * 60)
    if success:
        logger.info("VALIDATION TERMINEE: SUCCES")
    else:
        logger.info("VALIDATION TERMINEE: ECHECS DETECTES")
    logger.info("=" * 60)

    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()