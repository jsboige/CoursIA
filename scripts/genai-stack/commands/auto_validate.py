#!/usr/bin/env python3
"""
auto_validate.py - Script utilitaire pour l'exécution autonome de notebooks

Usage:
    python scripts/genai-stack/commands/auto_validate.py --batch 1 --list
    python scripts/genai-stack/commands/auto_validate.py --batch 1
    python scripts/genai-stack/commands/auto_validate.py --group audio_api
    python scripts/genai-stack/commands/auto_validate.py --notebook path/to/notebook.ipynb
    python scripts/genai-stack/commands/auto_validate.py --status
"""

import sys
import json
import logging
import subprocess
import time
from pathlib import Path
from typing import Optional, List

_script_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_script_dir))

from config import GENAI_DIR, EXECUTION_BATCHES, NOTEBOOK_SERVICE_MAP, GROUP_GPU_PROFILE, GPU_PROFILES
from commands.notebooks import NotebookValidator
from commands.gpu import profile_apply, profile_current

logger = logging.getLogger("AutoValidate")


def execute_notebook(notebook_path: Path) -> dict:
    """Exécute un notebook et retourne le résultat."""
    validator = NotebookValidator(str(notebook_path.parent))

    print(f"\n{'='*60}")
    print(f"Exécution: {notebook_path.relative_to(GENAI_DIR)}")
    print(f"{'='*60}")

    result = validator.validate_notebook(notebook_path, notebook_path.parent)

    if result["status"] == "success":
        print(f"  Succès ({result['duration']:.1f}s)")
    else:
        print(f"  Erreur: {result['error'][:200]}...")

    return result


def extract_images_from_notebook(notebook_path: Path) -> list[Path]:
    """Extrait les chemins des images dans les outputs."""
    images = []

    with open(notebook_path, "r", encoding="utf-8") as f:
        nb = json.load(f)

    for cell_idx, cell in enumerate(nb.get("cells", [])):
        if cell["cell_type"] != "code":
            continue

        for output in cell.get("outputs", []):
            # Références fichiers
            for text in output.get("text", []):
                import re
                for match in re.finditer(r'outputs/[^\s"\']+\.(png|jpg|jpeg|gif|webp|mp4)', str(text)):
                    img_path = notebook_path.parent / match.group(0)
                    if img_path.exists():
                        images.append(img_path)

    return sorted(set(images))


def get_batch_notebooks(batch_num: int) -> list[Path]:
    """Retourne les notebooks d'un batch."""
    batch_info = EXECUTION_BATCHES[batch_num]
    notebooks = []

    for group in batch_info["groups"]:
        if group not in NOTEBOOK_SERVICE_MAP:
            continue

        for nb_name in NOTEBOOK_SERVICE_MAP[group]:
            for series_dir in [GENAI_DIR / "Image", GENAI_DIR / "Audio", GENAI_DIR / "Video", GENAI_DIR / "Texte", GENAI_DIR / "00-GenAI-Environment"]:
                matches = list(series_dir.rglob(nb_name))
                if matches:
                    notebooks.append(matches[0])
                    break

    return sorted(set(notebooks))


def prepare_batch(batch_num: int):
    """Prépare le batch: applique le profil GPU."""
    batch_info = EXECUTION_BATCHES[batch_num]
    profile = batch_info.get("profile")

    if profile:
        print(f"\nApplication du profil GPU: {profile}")
        try:
            profile_apply(profile, wait_health=True)
        except Exception as e:
            print(f"  Warning: Could not apply profile: {e}")

    notebooks = get_batch_notebooks(batch_num)
    print(f"\nBatch {batch_num}: {len(notebooks)} notebooks")
    for nb in notebooks:
        print(f"  - {nb.relative_to(GENAI_DIR)}")

    return notebooks


def get_group_notebooks(group_name: str) -> list[Path]:
    """Retourne les notebooks d'un groupe spécifique."""
    if group_name not in NOTEBOOK_SERVICE_MAP:
        logger.error(f"Groupe inconnu: {group_name}")
        return []

    notebooks = []
    series_dirs = [
        GENAI_DIR / "Image",
        GENAI_DIR / "Audio",
        GENAI_DIR / "Video",
        GENAI_DIR / "Texte",
        GENAI_DIR / "00-GenAI-Environment",
    ]

    for nb_name in NOTEBOOK_SERVICE_MAP[group_name]:
        found = False
        for series_dir in series_dirs:
            if not series_dir.exists():
                continue
            matches = list(series_dir.rglob(nb_name))
            if matches:
                notebooks.append(matches[0])
                found = True
                break
        if not found:
            logger.warning(f"Notebook introuvable: {nb_name}")

    return sorted(set(notebooks))


def validate_single_notebook(notebook_path: Path, gpu_profile: Optional[str] = None) -> dict:
    """Valide un notebook unique avec application de profil GPU optionnel."""
    if not notebook_path.exists():
        return {
            "status": "failed",
            "error": f"Notebook non trouvé: {notebook_path}",
            "duration": 0
        }

    # Appliquer le profil GPU si spécifié
    if gpu_profile:
        print(f"\nApplication du profil GPU: {gpu_profile}")
        try:
            profile_apply(gpu_profile, wait_health=True)
        except Exception as e:
            print(f"  Warning: Could not apply profile: {e}")

    return execute_notebook(notebook_path)


def print_status():
    """Affiche le statut actuel de la validation."""
    print("\n" + "=" * 70)
    print("  STATUT VALIDATION NOTEBOOKS")
    print("=" * 70)

    # Profil GPU actuel
    print("\n--- Profil GPU actuel ---")
    profile_current()

    # Notebooks par série
    print("\n--- Notebooks par série ---")
    for series in ["Image", "Audio", "Video", "Texte", "00-GenAI-Environment"]:
        series_path = GENAI_DIR / series
        if series_path.exists():
            notebooks = list(series_path.rglob("*.ipynb"))
            notebooks = [n for n in notebooks if ".ipynb_checkpoints" not in str(n)]
            print(f"  {series}: {len(notebooks)} notebooks")

    print("\n" + "=" * 70)


def main():
    import argparse
    parser = argparse.ArgumentParser(
        description="Exécution autonome de notebooks GenAI",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples:
  auto_validate.py --status                    Afficher le statut
  auto_validate.py --batch 1 --list            Lister notebooks du batch 1
  auto_validate.py --batch 1                   Exécuter batch 1
  auto_validate.py --group audio_api           Exécuter groupe audio_api
  auto_validate.py --notebook path/to/nb.ipynb Exécuter un notebook
  auto_validate.py --series audio              Exécuter toute la série Audio
        """
    )
    parser.add_argument('--batch', type=int, help='Numéro de batch (1-8)')
    parser.add_argument('--group', type=str, help='Groupe de notebooks')
    parser.add_argument('--series', type=str, choices=['image', 'audio', 'video', 'texte', 'environment'],
                       help='Série complète à exécuter')
    parser.add_argument('--notebook', type=str, help='Chemin vers un notebook spécifique')
    parser.add_argument('--list', action='store_true', help='Lister les notebooks')
    parser.add_argument('--status', action='store_true', help='Afficher le statut')
    parser.add_argument('--no-gpu', action='store_true', help='Ne pas appliquer le profil GPU')
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')

    # Statut
    if args.status:
        print_status()
        return

    # Notebook unique
    if args.notebook:
        notebook_path = Path(args.notebook)
        if not notebook_path.is_absolute():
            notebook_path = GENAI_DIR / notebook_path

        result = validate_single_notebook(notebook_path, gpu_profile=None if args.no_gpu else None)
        print(f"\nRésultat: {result['status']}")
        return 0 if result['status'] == 'success' else 1

    # Batch
    if args.batch:
        if args.list:
            notebooks = get_batch_notebooks(args.batch)
            for nb in notebooks:
                print(nb.relative_to(GENAI_DIR))
            return

        notebooks = prepare_batch(args.batch)

    # Groupe
    elif args.group:
        if args.group not in NOTEBOOK_SERVICE_MAP:
            print(f"Erreur: groupe '{args.group}' inconnu.")
            print(f"Groupes disponibles: {', '.join(sorted(NOTEBOOK_SERVICE_MAP.keys()))}")
            return 1

        if args.list:
            notebooks = get_group_notebooks(args.group)
            for nb in notebooks:
                print(nb.relative_to(GENAI_DIR))
            return

        # Appliquer le profil GPU pour le groupe
        profile = GROUP_GPU_PROFILE.get(args.group)
        notebooks = get_group_notebooks(args.group)

        if profile and not args.no_gpu:
            print(f"\nApplication du profil GPU: {profile}")
            try:
                profile_apply(profile, wait_health=True)
            except Exception as e:
                print(f"  Warning: Could not apply profile: {e}")

        print(f"\nGroupe {args.group}: {len(notebooks)} notebooks")
        for nb in notebooks:
            print(f"  - {nb.relative_to(GENAI_DIR)}")

    # Série complète
    elif args.series:
        from config import NOTEBOOK_SERIES
        series_name = args.series.capitalize()
        if series_name not in NOTEBOOK_SERIES:
            # Fallback pour environment
            if args.series == 'environment':
                series_name = 'environment'
                groups = []
                env_dir = GENAI_DIR / "00-GenAI-Environment"
                if env_dir.exists():
                    notebooks = sorted(list(env_dir.rglob("*.ipynb")))
                    notebooks = [n for n in notebooks if ".ipynb_checkpoints" not in str(n)]
                else:
                    notebooks = []
            else:
                print(f"Erreur: série '{args.series}' inconnue.")
                return 1
        else:
            groups = NOTEBOOK_SERIES[series_name]
            notebooks = []
            for grp in groups:
                notebooks.extend(get_group_notebooks(grp))

        if args.list:
            for nb in notebooks:
                print(nb.relative_to(GENAI_DIR))
            return

        print(f"\nSérie {args.series}: {len(notebooks)} notebooks")
        for nb in notebooks:
            print(f"  - {nb.relative_to(GENAI_DIR)}")

    else:
        parser.print_help()
        return 0

    # Exécution
    if not notebooks:
        print("Aucun notebook à exécuter.")
        return 0

    results = []
    for i, notebook in enumerate(notebooks, 1):
        print(f"\n[{i}/{len(notebooks)}]", end=" ")
        result = execute_notebook(notebook)
        results.append(result)

        # Pause entre notebooks pour laisser le GPU refroidir
        if i < len(notebooks):
            time.sleep(2)

    # Résumé
    print(f"\n{'='*60}")
    print("RÉSUMÉ")
    print(f"{'='*60}")
    print(f"Total: {len(results)}")
    print(f"Succès: {sum(1 for r in results if r['status'] == 'success')}")
    print(f"Échecs: {sum(1 for r in results if r['status'] == 'failed')}")

    if any(r['status'] == 'failed' for r in results):
        print("\nNotebooks en échec:")
        for r in results:
            if r['status'] == 'failed':
                print(f"  - {r.get('notebook', 'unknown')}")
        return 1

    return 0


if __name__ == "__main__":
    main()
