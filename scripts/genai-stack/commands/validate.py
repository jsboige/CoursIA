#!/usr/bin/env python3
"""
commands/validate.py - Validation de la stack ComfyUI + services externes

Sous-commandes :
    genai.py validate [--full]               # Validation complete ComfyUI
    genai.py validate --auth-only            # Auth uniquement
    genai.py validate --nodes-only           # Nodes uniquement
    genai.py validate --nunchaku             # Test Nunchaku INT4
    genai.py validate --notebooks [--group G] # Validation syntaxe notebooks
    genai.py validate --check-forge --check-vllm
"""

import sys
import os
import json
import logging
import time
from pathlib import Path
from typing import Dict, Optional, Any

import requests

_script_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_script_dir))

from config import (
    COMFYUI_URL, FORGE_URL, VLLM_ZIMAGE_URL, WHISPER_URL, COMFYUI_VIDEO_URL,
    EXPECTED_QWEN_NODES, EXPECTED_NUNCHAKU_NODES, REQUIRED_NATIVE_NODES,
    NOTEBOOK_SERVICE_MAP, NOTEBOOK_SERIES, NOTEBOOK_SEARCH_DIRS,
    MODEL_CONFIGS, WORKFLOWS_DIR, GENAI_DIR,
)
from core.auth_manager import GenAIAuthManager
from core.comfyui_client import ComfyUIClient, ComfyUIConfig, WorkflowManager

logger = logging.getLogger("ComfyUIValidator")


class VRAMManager:
    """Gestion VRAM via ComfyUI /free endpoint."""

    def __init__(self, comfyui_client: ComfyUIClient):
        self.client = comfyui_client

    def free_vram(self, unload_models: bool = True) -> dict:
        try:
            return self.client.free_memory(unload_models=unload_models)
        except Exception as e:
            logger.error("Erreur liberation VRAM: %s", e)
            return {"error": str(e)}

    def get_vram_stats(self) -> dict:
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
            logger.error("Erreur stats VRAM: %s", e)
            return {"error": str(e)}


class ModelSwitcher:
    """Switch entre modeles avec gestion VRAM."""

    def __init__(self, vram_manager: VRAMManager):
        self.vram = vram_manager
        self.current_model: Optional[str] = None

    def switch_to(self, model_name: str) -> bool:
        if model_name not in MODEL_CONFIGS:
            logger.error("Modele inconnu: %s", model_name)
            return False

        if self.current_model == model_name:
            logger.info("Modele %s deja charge", model_name)
            return True

        logger.info("Switch vers modele: %s", model_name)
        logger.info("Liberation VRAM...")
        result = self.vram.free_vram(unload_models=True)
        if "error" in result:
            logger.warning("Attention lors liberation VRAM: %s", result['error'])

        time.sleep(2)

        stats = self.vram.get_vram_stats()
        if stats and "error" not in stats:
            vram_free_mb = stats.get('vram_free', 0) / (1024 * 1024)
            required_mb = MODEL_CONFIGS[model_name]['vram_required_mb']
            logger.info("VRAM libre: %.0fMB, requis: %dMB", vram_free_mb, required_mb)

        self.current_model = model_name
        return True


class BatchNotebookValidator:
    """Validation batch de notebooks avec switching automatique."""

    def __init__(self, model_switcher: Any, notebooks_dir: Optional[Path] = None) -> None:
        self.switcher = model_switcher
        self.notebooks_dir = notebooks_dir or GENAI_DIR
        self.results: Dict[str, Dict[str, Any]] = {}

    def _find_notebook(self, notebook_name: str) -> Optional[Path]:
        for path in self.notebooks_dir.rglob(notebook_name):
            return path
        for path in self.notebooks_dir.rglob(f"*{notebook_name}*"):
            if path.suffix == ".ipynb":
                return path
        return None

    def _validate_notebook_syntax(self, notebook_path: Path) -> Dict[str, Any]:
        try:
            with open(notebook_path, 'r', encoding='utf-8') as f:
                nb = json.load(f)
            if 'cells' not in nb:
                return {"valid": False, "error": "Missing 'cells' key"}
            if 'metadata' not in nb:
                return {"valid": False, "error": "Missing 'metadata' key"}
            cell_count = len(nb['cells'])
            code_cells = sum(1 for c in nb['cells'] if c.get('cell_type') == 'code')
            return {"valid": True, "cell_count": cell_count, "code_cells": code_cells, "path": str(notebook_path)}
        except json.JSONDecodeError as e:
            return {"valid": False, "error": f"JSON invalide: {e}"}
        except Exception as e:
            return {"valid": False, "error": str(e)}

    def validate_group(self, group: str) -> Dict[str, Any]:
        if group not in NOTEBOOK_SERVICE_MAP:
            return {"error": f"Groupe inconnu: {group}"}
        notebooks = NOTEBOOK_SERVICE_MAP[group]
        logger.info("Validation groupe '%s': %d notebooks", group, len(notebooks))
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

    def run_full_validation(self, series: Optional[str] = None) -> Dict:
        """Validation de tous les groupes (ou d'une serie specifique).

        Args:
            series: Nom de la serie (image, audio, video) ou None pour tout
        """
        if series and series in NOTEBOOK_SERIES:
            groups = NOTEBOOK_SERIES[series]
        elif series is None:
            groups = list(NOTEBOOK_SERVICE_MAP.keys())
        else:
            groups = [series]

        for group in groups:
            if group in NOTEBOOK_SERVICE_MAP:
                self.validate_group(group)
        return self.results

    def print_summary(self) -> bool:
        total = 0
        valid = 0
        for group, notebooks in self.results.items():
            group_valid = sum(1 for r in notebooks.values() if r.get("valid", False))
            group_total = len(notebooks)
            total += group_total
            valid += group_valid
            status = "OK" if group_valid == group_total else "PARTIEL"
            logger.info("  %s: %d/%d %s", group, group_valid, group_total, status)
        logger.info("TOTAL: %d/%d notebooks valides", valid, total)
        return valid == total


class ComfyUIValidator:
    """Suite de validation ComfyUI."""

    def __init__(self):
        self.auth_manager = GenAIAuthManager()
        self.config = self.auth_manager.load_config()
        self.token = self.config.get('bcrypt_hash') if self.config else None
        self.session = requests.Session()
        client_config = ComfyUIConfig(host="localhost", port=8188, api_key=self.token, timeout=300)
        self.client = ComfyUIClient(client_config)

    def check_service_health(self) -> bool:
        logger.info("Verification disponibilite service...")
        try:
            if not self.client.is_reachable():
                logger.error("ComfyUI inaccessible sur localhost:8188")
                return False
        except Exception as e:
            logger.error("ComfyUI inaccessible: %s", e)
            return False
        logger.info("Service ComfyUI en ligne")
        return True

    def check_auth(self) -> bool:
        logger.info("\n" + "=" * 60)
        logger.info("TEST AUTHENTICATION")
        logger.info("=" * 60)

        if not self.token:
            logger.error("Token d'authentification manquant")
            return False

        headers = {"Authorization": f"Bearer {self.token}"}
        try:
            resp = self.session.get(f"{COMFYUI_URL}/system_stats", headers=headers, timeout=5)
            if resp.status_code == 200:
                logger.info("Authentification reussie")
            else:
                logger.error("Echec authentification (HTTP %d)", resp.status_code)
                return False
        except Exception as e:
            logger.error("Erreur connexion: %s", e)
            return False

        logger.info("Test acces API protege...")
        try:
            resp = self.session.post(f"{COMFYUI_URL}/prompt", json={"prompt": {}}, headers=headers)
            if resp.status_code in [200, 400]:
                logger.info("API accessible")
                return True
            logger.error("API refusee (HTTP %d)", resp.status_code)
            return False
        except Exception as e:
            logger.error("Erreur API: %s", e)
            return False

    def check_nodes(self, check_nunchaku: bool = False) -> bool:
        logger.info("\n" + "=" * 60)
        label = "TEST NODES (Qwen + Natifs" + (" + Nunchaku)" if check_nunchaku else ")")
        logger.info(label)
        logger.info("=" * 60)

        try:
            object_info = self.client.get_object_info()
            if not object_info:
                logger.error("Impossible de recuperer la liste des noeuds")
                return False

            available_nodes = set(object_info.keys())
            logger.info("%d noeuds detectes au total", len(available_nodes))

            missing_qwen = [n for n in EXPECTED_QWEN_NODES if n not in available_nodes]
            missing_native = [n for n in REQUIRED_NATIVE_NODES if n not in available_nodes]

            for node in missing_qwen:
                logger.error("  MANQUANT (Qwen): %s", node)
            if not missing_qwen:
                logger.info("OK: %d noeuds Qwen presents", len(EXPECTED_QWEN_NODES))

            for node in missing_native:
                logger.error("  MANQUANT (natif): %s", node)
            if not missing_native:
                logger.info("OK: %d noeuds natifs presents", len(REQUIRED_NATIVE_NODES))

            if check_nunchaku:
                missing_nunchaku = [n for n in EXPECTED_NUNCHAKU_NODES if n not in available_nodes]
                for node in missing_nunchaku:
                    logger.warning("  MANQUANT (Nunchaku): %s", node)
                if not missing_nunchaku:
                    logger.info("OK: %d noeuds Nunchaku presents", len(EXPECTED_NUNCHAKU_NODES))

            return len(missing_qwen) == 0 and len(missing_native) == 0
        except Exception as e:
            logger.error("Erreur verification noeuds: %s", e)
            return False

    def check_generation(self, workflow_filename="workflow_qwen_native_t2i.json") -> bool:
        logger.info("\n" + "=" * 60)
        logger.info("TEST GENERATION (%s)", workflow_filename)
        logger.info("=" * 60)

        workflow_path = WORKFLOWS_DIR / workflow_filename
        if not workflow_path.exists():
            logger.error("Workflow introuvable: %s", workflow_path)
            return False

        logger.info("Soumission du workflow %s...", workflow_filename)
        try:
            workflow = WorkflowManager.load(str(workflow_path))
            prompt_id = self.client.queue_prompt(workflow)
            if not prompt_id:
                logger.error("Echec soumission workflow")
                return False
            logger.info("Job ID: %s - Attente generation...", prompt_id)
            result = self.client.wait_for_prompt(prompt_id, timeout=300)
            if not result:
                logger.error("Timeout ou erreur recuperation resultat")
                return False
            if result.get('status', {}).get('status_str') == 'error':
                logger.error("Erreur execution workflow")
                return False
            outputs = result.get('outputs', {})
            if not outputs:
                logger.error("Aucun output genere")
                return False
            logger.info("Generation reussie!")
            return True
        except Exception as e:
            logger.error("Erreur test generation: %s", e)
            return False

    def run_suite(self, full=True, auth_only=False, nodes_only=False,
                  workflow="workflow_qwen_native_t2i.json", check_nunchaku=False) -> bool:
        if not self.check_service_health():
            return False
        results = []
        if full or auth_only:
            results.append(self.check_auth())
            if auth_only:
                return all(results)
        if full or nodes_only:
            results.append(self.check_nodes(check_nunchaku=check_nunchaku))
            if nodes_only:
                return all(results)
        if full:
            if "nunchaku" in workflow.lower():
                logger.info("Test generation avec Nunchaku INT4 Lightning...")
            results.append(self.check_generation(workflow_filename=workflow))
        success = all(results)
        logger.info("\n" + "=" * 60)
        logger.info("RESULTAT: " + ("SUCCES" if success else "ECHEC PARTIEL"))
        logger.info("=" * 60)
        return success


def check_forge_api() -> bool:
    """Verifie si Forge-Turbo est accessible."""
    try:
        resp = requests.get(f"{FORGE_URL}/sdapi/v1/sd-models", timeout=5)
        if resp.status_code == 200:
            logger.info("OK Forge-Turbo accessible sur %s", FORGE_URL)
            return True
        logger.warning("Forge-Turbo repond avec HTTP %d", resp.status_code)
        return False
    except Exception as e:
        logger.warning("Forge-Turbo inaccessible: %s", e)
        return False


def check_vllm_api() -> bool:
    """Verifie si vLLM Z-Image API est accessible."""
    try:
        resp = requests.get(f"{VLLM_ZIMAGE_URL}/health", timeout=5)
        if resp.status_code == 200:
            logger.info("OK vLLM Z-Image accessible sur %s", VLLM_ZIMAGE_URL)
            models_resp = requests.get(f"{VLLM_ZIMAGE_URL}/v1/models", timeout=5)
            if models_resp.status_code == 200:
                models = models_resp.json().get('data', [])
                model_names = [m.get('id', 'unknown') for m in models]
                logger.info("  Modeles disponibles: %s", model_names)
            return True
        logger.warning("vLLM Z-Image repond avec HTTP %d", resp.status_code)
        return False
    except Exception as e:
        logger.warning("vLLM Z-Image inaccessible: %s", e)
        return False


def check_whisper_api() -> bool:
    """Verifie si Whisper-WebUI (Gradio) est accessible."""
    try:
        resp = requests.get(f"{WHISPER_URL}/", timeout=10)
        if resp.status_code == 200:
            logger.info("OK Whisper-WebUI accessible sur %s", WHISPER_URL)
            return True
        elif resp.status_code == 401:
            logger.info("OK Whisper-WebUI accessible (auth requise) sur %s", WHISPER_URL)
            return True
        logger.warning("Whisper-WebUI repond avec HTTP %d", resp.status_code)
        return False
    except Exception as e:
        logger.warning("Whisper-WebUI inaccessible: %s", e)
        return False


def check_comfyui_video_api() -> bool:
    """Verifie si ComfyUI-Video est accessible."""
    try:
        resp = requests.get(f"{COMFYUI_VIDEO_URL}/system_stats", timeout=10)
        if resp.status_code == 200:
            logger.info("OK ComfyUI-Video accessible sur %s", COMFYUI_VIDEO_URL)
            data = resp.json()
            devices = data.get('devices', [])
            if devices:
                dev = devices[0]
                vram_total = dev.get('vram_total', 0) / (1024**3)
                logger.info("  GPU: %s (%.1fGB)", dev.get('name', '?'), vram_total)
            return True
        elif resp.status_code == 401:
            logger.info("OK ComfyUI-Video accessible (auth requise) sur %s", COMFYUI_VIDEO_URL)
            return True
        logger.warning("ComfyUI-Video repond avec HTTP %d", resp.status_code)
        return False
    except Exception as e:
        logger.warning("ComfyUI-Video inaccessible: %s", e)
        return False


# --- CLI ---

def register(subparsers):
    """Enregistre la sous-commande validate."""
    parser = subparsers.add_parser('validate', help='Validation stack ComfyUI + services')
    parser.add_argument('--full', action='store_true', default=True)
    parser.add_argument('--auth-only', action='store_true')
    parser.add_argument('--nodes-only', action='store_true')
    parser.add_argument('--workflow', type=str, default="workflow_qwen_native_t2i.json")
    parser.add_argument('--nunchaku', action='store_true',
                       help='Test Nunchaku INT4 Lightning')
    parser.add_argument('--check-nunchaku-nodes', action='store_true')
    parser.add_argument('--notebooks', action='store_true',
                       help='Validation syntaxe notebooks GenAI')
    parser.add_argument('--with-switching', action='store_true')
    parser.add_argument('--group', type=str,
                       choices=list(NOTEBOOK_SERVICE_MAP.keys()),
                       help='Groupe de notebooks a valider')
    parser.add_argument('--series', type=str,
                       choices=list(NOTEBOOK_SERIES.keys()),
                       help='Serie complete a valider (image, audio, video)')
    parser.add_argument('--dry-run', action='store_true')
    parser.add_argument('--check-forge', action='store_true')
    parser.add_argument('--check-vllm', '--vllm', action='store_true')
    parser.add_argument('--check-whisper', action='store_true',
                       help='Verifier la sante de Whisper-WebUI')
    parser.add_argument('--check-comfyui-video', action='store_true',
                       help='Verifier la sante de ComfyUI-Video')


def execute(args) -> int:
    """Execute la commande validate."""
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
                       datefmt='%H:%M:%S')

    if args.auth_only or args.nodes_only:
        args.full = False

    if args.nunchaku:
        args.workflow = "workflow_qwen_nunchaku_t2i.json"
        logger.info("Mode Nunchaku INT4 Lightning active")

    success = True

    # Mode Notebooks
    series = getattr(args, 'series', None)
    if args.notebooks or args.with_switching or args.group or series:
        logger.info("\n" + "=" * 60)
        logger.info("VALIDATION NOTEBOOKS GENAI")
        logger.info("=" * 60)

        validator = ComfyUIValidator()
        if args.with_switching and not validator.check_service_health():
            logger.error("ComfyUI requis pour --with-switching")
            return 1

        vram_mgr = VRAMManager(validator.client) if validator.client else None
        model_switcher = ModelSwitcher(vram_mgr) if vram_mgr else None

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
        elif series:
            batch_validator.run_full_validation(series=series)
            success = batch_validator.print_summary()
        else:
            batch_validator.run_full_validation()
            success = batch_validator.print_summary()

    # Mode ComfyUI standard
    elif args.full or args.auth_only or args.nodes_only:
        validator = ComfyUIValidator()
        check_nunchaku = args.check_nunchaku_nodes or args.nunchaku or "nunchaku" in args.workflow.lower()
        success = validator.run_suite(
            full=args.full,
            auth_only=args.auth_only,
            nodes_only=args.nodes_only,
            workflow=args.workflow,
            check_nunchaku=check_nunchaku,
        )

    # Check Forge
    if args.check_forge:
        success = success and check_forge_api()

    # Check vLLM
    if args.check_vllm:
        success = success and check_vllm_api()

    # Check Whisper-WebUI
    if getattr(args, 'check_whisper', False):
        success = success and check_whisper_api()

    # Check ComfyUI-Video
    if getattr(args, 'check_comfyui_video', False):
        success = success and check_comfyui_video_api()

    logger.info("\n" + "=" * 60)
    logger.info("VALIDATION TERMINEE: " + ("SUCCES" if success else "ECHECS DETECTES"))
    logger.info("=" * 60)

    return 0 if success else 1


def main():
    """Point d'entree standalone (retrocompatibilite validate_stack.py)."""
    import argparse
    parser = argparse.ArgumentParser(description="ComfyUI Validation Suite")
    parser.add_argument('--full', action='store_true', default=True)
    parser.add_argument('--auth-only', action='store_true')
    parser.add_argument('--nodes-only', action='store_true')
    parser.add_argument('--workflow', type=str, default="workflow_qwen_native_t2i.json")
    parser.add_argument('--nunchaku', action='store_true')
    parser.add_argument('--check-nunchaku-nodes', action='store_true')
    parser.add_argument('--notebooks', action='store_true')
    parser.add_argument('--with-switching', action='store_true')
    parser.add_argument('--group', type=str,
                       choices=list(NOTEBOOK_SERVICE_MAP.keys()))
    parser.add_argument('--series', type=str,
                       choices=list(NOTEBOOK_SERIES.keys()))
    parser.add_argument('--dry-run', action='store_true')
    parser.add_argument('--check-forge', action='store_true')
    parser.add_argument('--check-vllm', '--vllm', action='store_true')
    parser.add_argument('--check-whisper', action='store_true')
    parser.add_argument('--check-comfyui-video', action='store_true')
    args = parser.parse_args()
    sys.exit(execute(args))


def main_nunchaku():
    """Point d'entree standalone pour test Nunchaku (retrocompatibilite)."""
    import argparse
    parser = argparse.ArgumentParser(description="Test Nunchaku INT4 Lightning")
    args = parser.parse_args()
    args.full = True
    args.auth_only = False
    args.nodes_only = False
    args.workflow = "workflow_qwen_nunchaku_t2i.json"
    args.nunchaku = True
    args.check_nunchaku_nodes = True
    args.notebooks = False
    args.with_switching = False
    args.group = None
    args.dry_run = False
    args.check_forge = False
    args.check_vllm = False
    sys.exit(execute(args))


if __name__ == "__main__":
    main()
