#!/usr/bin/env python3
"""
commands/notebooks.py - Validation de notebooks via Papermill

Sous-commandes :
    genai.py notebooks [target]      # Valider notebooks (dossier ou fichier)
    genai.py notebooks --cleanup     # Nettoyer apres validation
"""

import sys
import os
import json
import logging
import shutil
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Optional

import papermill as pm

_script_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_script_dir))

from config import (
    GENAI_DIR, NOTEBOOK_SERVICE_MAP, NOTEBOOK_SERIES, NOTEBOOK_SEARCH_DIRS,
    EXECUTION_BATCHES, GROUP_GPU_PROFILE,
)
from core.auth_manager import GenAIAuthManager

logger = logging.getLogger("NotebookValidator")


class NotebookValidator:
    """Validation de notebooks via Papermill avec injection auth."""

    def __init__(self, target_path: str):
        self.target_path = Path(target_path)
        self.auth_manager = GenAIAuthManager()
        self.config = self.auth_manager.load_config()
        self.token = self.config.get('bcrypt_hash') if self.config else None

        if not self.token:
            logger.warning("Token d'authentification non trouve via AuthManager.")
            self.token = os.getenv("COMFYUI_AUTH_TOKEN")

        self.env_vars = {
            "COMFYUI_URL": "http://localhost:8188",
            "COMFYUI_AUTH_TOKEN": self.token if self.token else "",
            "JUPYTER_PLATFORM_DIRS": "1",
            # Audio/Video env vars
            "BATCH_MODE": "true",
            "WHISPER_DEVICE": "cuda",
            "WHISPER_MODEL_SIZE": os.getenv("WHISPER_MODEL_SIZE", "large-v3-turbo"),
            "MUSICGEN_MODEL": os.getenv("MUSICGEN_MODEL", "facebook/musicgen-medium"),
            "DEMUCS_MODEL": os.getenv("DEMUCS_MODEL", "htdemucs_ft"),
            "DEFAULT_TTS_MODEL": os.getenv("DEFAULT_TTS_MODEL", "tts-1"),
            "DEFAULT_TTS_VOICE": os.getenv("DEFAULT_TTS_VOICE", "alloy"),
            "DEFAULT_STT_MODEL": os.getenv("DEFAULT_STT_MODEL", "whisper-1"),
            "AUDIO_OUTPUT_DIR": os.getenv("AUDIO_OUTPUT_DIR", "outputs/audio"),
            "VIDEO_OUTPUT_DIR": os.getenv("VIDEO_OUTPUT_DIR", "outputs/video"),
            "HUNYUANVIDEO_QUANTIZE": os.getenv("HUNYUANVIDEO_QUANTIZE", "true"),
            "WAN_QUANTIZE": os.getenv("WAN_QUANTIZE", "true"),
            "COMFYUI_VIDEO_TIMEOUT": os.getenv("COMFYUI_VIDEO_TIMEOUT", "600"),
        }

    def find_notebooks(self) -> List[Path]:
        """Liste les fichiers .ipynb."""
        if self.target_path.is_file():
            if self.target_path.suffix == '.ipynb':
                return [self.target_path]
            return []
        return list(self.target_path.rglob("*.ipynb"))

    def find_notebooks_by_group(self, group: str) -> List[Path]:
        """Trouve les notebooks d'un groupe specifique."""
        if group not in NOTEBOOK_SERVICE_MAP:
            logger.error(f"Groupe inconnu: {group}")
            return []

        nb_names = NOTEBOOK_SERVICE_MAP[group]
        found = []

        # Determiner le repertoire de recherche
        search_dirs = list(NOTEBOOK_SEARCH_DIRS.values())

        for nb_name in nb_names:
            nb_found = False
            for search_dir in search_dirs:
                if not search_dir.exists():
                    continue
                matches = list(search_dir.rglob(nb_name))
                if matches:
                    found.append(matches[0])
                    nb_found = True
                    break
            if not nb_found:
                # Fallback: recherche globale
                matches = list(GENAI_DIR.rglob(nb_name))
                if matches:
                    found.append(matches[0])
                else:
                    logger.warning(f"Notebook introuvable: {nb_name}")

        return found

    def find_notebooks_by_batch(self, batch_num: int) -> List[Path]:
        """Trouve les notebooks d'un batch d'execution."""
        if batch_num not in EXECUTION_BATCHES:
            logger.error(f"Batch inconnu: {batch_num}. Disponibles: {list(EXECUTION_BATCHES.keys())}")
            return []

        batch = EXECUTION_BATCHES[batch_num]
        all_notebooks = []
        for group in batch['groups']:
            all_notebooks.extend(self.find_notebooks_by_group(group))
        return all_notebooks

    def validate_notebook(self, notebook_path: Path, output_dir: Path) -> Dict:
        """Execute un notebook via papermill."""
        if self.target_path.is_file():
            rel_path = notebook_path.name
        else:
            try:
                rel_path = notebook_path.relative_to(self.target_path)
            except ValueError:
                rel_path = notebook_path.name

        output_path = output_dir / rel_path
        output_path.parent.mkdir(parents=True, exist_ok=True)

        logger.info(f"Validation de : {rel_path}")

        start_time = datetime.now()
        status = "success"
        error_msg = None

        original_env = os.environ.copy()
        os.environ.update(self.env_vars)

        # Add ffmpeg to PATH if available locally
        ffmpeg_paths = [
            "D:/Dev/CoursIA/tools/ffmpeg/bin",  # Local installation
            "C:/Program Files/ffmpeg/bin",
            "C:/tools/ffmpeg/bin",
        ]
        for ffmpeg_path in ffmpeg_paths:
            if Path(ffmpeg_path).exists():
                os.environ["PATH"] = f"{ffmpeg_path};{os.environ.get('PATH', '')}"
                logger.info(f"Added ffmpeg to PATH: {ffmpeg_path}")
                break

        try:
            pm.execute_notebook(
                input_path=str(notebook_path),
                output_path=str(output_path),
                cwd=str(notebook_path.parent),
                kernel_name="python3",
                progress_bar=False,
                log_output=True,
            )
        except Exception as e:
            status = "failed"
            error_msg = str(e)
            logger.error(f"Echec de {rel_path}: {e}")
        finally:
            os.environ.clear()
            os.environ.update(original_env)

        duration = (datetime.now() - start_time).total_seconds()
        return {
            "notebook": str(rel_path),
            "status": status,
            "duration": duration,
            "error": error_msg,
            "output_path": str(output_path),
        }

    def run_validation(self) -> List[Dict]:
        """Lance la validation sur tous les notebooks."""
        notebooks = self.find_notebooks()
        logger.info(f"{len(notebooks)} notebooks trouves dans {self.target_path}")

        output_dir = Path("rapports/notebook_validation")
        output_dir.mkdir(parents=True, exist_ok=True)

        results = []
        for nb in notebooks:
            if ".ipynb_checkpoints" in str(nb):
                continue
            results.append(self.validate_notebook(nb, output_dir))
        return results

    def save_report(self, results: List[Dict]):
        """Sauvegarde le rapport JSON."""
        report = {
            "timestamp": datetime.now().isoformat(),
            "total_notebooks": len(results),
            "passed": len([r for r in results if r["status"] == "success"]),
            "failed": len([r for r in results if r["status"] == "failed"]),
            "results": results,
        }

        report_path = Path("notebook_validation_report.json")
        with open(report_path, "w", encoding="utf-8") as f:
            json.dump(report, f, indent=2, ensure_ascii=False)

        logger.info(f"Rapport genere : {report_path.absolute()}")

        print("\n" + "=" * 40)
        print("RESUME VALIDATION NOTEBOOKS")
        print("=" * 40)
        print(f"Total: {report['total_notebooks']}")
        print(f"Succes: {report['passed']}")
        print(f"Echecs: {report['failed']}")

        if report['failed'] > 0:
            print("\nNotebooks en echec:")
            for r in results:
                if r['status'] == 'failed':
                    print(f"  - {r['notebook']} ({r['error'][:100]}...)")
        print("=" * 40)


# --- CLI ---

def register(subparsers):
    """Enregistre la sous-commande notebooks."""
    parser = subparsers.add_parser('notebooks', help='Validation notebooks via Papermill')
    parser.add_argument('target', nargs='?', type=str, default=str(GENAI_DIR),
                       help='Dossier ou fichier cible')
    parser.add_argument('--group', type=str,
                       choices=list(NOTEBOOK_SERVICE_MAP.keys()),
                       help='Groupe de notebooks a executer')
    parser.add_argument('--series', type=str,
                       choices=list(NOTEBOOK_SERIES.keys()),
                       help='Serie complete a executer (image, audio, video)')
    parser.add_argument('--batch', type=int,
                       choices=list(EXECUTION_BATCHES.keys()),
                       help='Batch d\'execution (1-8)')
    parser.add_argument('--gpu-profile', type=str,
                       help='Profil GPU a appliquer avant execution')
    parser.add_argument('--cleanup', action='store_true',
                       help='Supprimer les notebooks executes apres validation')


def execute(args) -> int:
    """Execute la commande notebooks."""
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
                       datefmt='%H:%M:%S')

    # Appliquer le profil GPU si demande
    gpu_profile = getattr(args, 'gpu_profile', None)
    batch_num = getattr(args, 'batch', None)
    group = getattr(args, 'group', None)
    series = getattr(args, 'series', None)

    # Determiner le profil GPU automatiquement si batch specifie
    if batch_num and not gpu_profile:
        batch_info = EXECUTION_BATCHES.get(batch_num, {})
        gpu_profile = batch_info.get('profile')

    if gpu_profile:
        from commands.gpu import profile_apply
        logger.info(f"Application du profil GPU: {gpu_profile}")
        if not profile_apply(gpu_profile, wait_health=True):
            logger.warning("Profil GPU applique partiellement, execution continue...")

    validator = NotebookValidator(args.target)

    # Mode batch
    if batch_num:
        batch_info = EXECUTION_BATCHES[batch_num]
        logger.info(f"\n{'=' * 60}")
        logger.info(f"  BATCH {batch_num}: {batch_info['name']}")
        logger.info(f"  Profil GPU: {batch_info['profile']}")
        logger.info(f"  Groupes: {', '.join(batch_info['groups'])}")
        logger.info(f"{'=' * 60}")

        notebooks = validator.find_notebooks_by_batch(batch_num)
        if not notebooks:
            logger.error("Aucun notebook trouve pour ce batch")
            return 1

        output_dir = Path("rapports/notebook_validation")
        output_dir.mkdir(parents=True, exist_ok=True)

        results = []
        for nb in notebooks:
            results.append(validator.validate_notebook(nb, output_dir))
        validator.save_report(results)

    # Mode groupe
    elif group:
        notebooks = validator.find_notebooks_by_group(group)
        if not notebooks:
            logger.error(f"Aucun notebook trouve pour le groupe '{group}'")
            return 1

        output_dir = Path("rapports/notebook_validation")
        output_dir.mkdir(parents=True, exist_ok=True)

        results = []
        for nb in notebooks:
            results.append(validator.validate_notebook(nb, output_dir))
        validator.save_report(results)

    # Mode serie
    elif series:
        if series not in NOTEBOOK_SERIES:
            logger.error(f"Serie inconnue: {series}")
            return 1

        all_results = []
        output_dir = Path("rapports/notebook_validation")
        output_dir.mkdir(parents=True, exist_ok=True)

        for grp in NOTEBOOK_SERIES[series]:
            notebooks = validator.find_notebooks_by_group(grp)
            for nb in notebooks:
                all_results.append(validator.validate_notebook(nb, output_dir))

        results = all_results
        validator.save_report(results)

    # Mode classique (dossier/fichier)
    else:
        results = validator.run_validation()
        validator.save_report(results)

    if getattr(args, 'cleanup', False):
        output_dir = Path("rapports/notebook_validation")
        if output_dir.exists():
            shutil.rmtree(output_dir)
            logger.info(f"Nettoyage: {output_dir} supprime")

    return 1 if any(r['status'] == 'failed' for r in results) else 0


def main():
    """Point d'entree standalone (retrocompatibilite validate_notebooks.py)."""
    import argparse
    parser = argparse.ArgumentParser(description="Notebook Validation Suite")
    parser.add_argument('target', nargs='?', type=str, default=str(GENAI_DIR))
    parser.add_argument('--group', type=str, choices=list(NOTEBOOK_SERVICE_MAP.keys()))
    parser.add_argument('--series', type=str, choices=list(NOTEBOOK_SERIES.keys()))
    parser.add_argument('--batch', type=int, choices=list(EXECUTION_BATCHES.keys()))
    parser.add_argument('--gpu-profile', type=str)
    parser.add_argument('--cleanup', action='store_true')
    args = parser.parse_args()
    sys.exit(execute(args))


if __name__ == "__main__":
    main()
