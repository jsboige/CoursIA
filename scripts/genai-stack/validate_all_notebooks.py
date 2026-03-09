#!/usr/bin/env python3
"""
validate_all_notebooks.py - Exécution complète de tous les notebooks GenAI

Usage:
    python validate_all_notebooks.py [--category CATEGORY] [--timeout N]

Categories: Environment, Texte, Audio, Video, Image, all
"""

import os
import sys
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent.parent
GENAI_DIR = PROJECT_ROOT / "MyIA.AI.Notebooks" / "GenAI"
ENV_FILE = GENAI_DIR / ".env"

# Catégories et leurs chemins
CATEGORIES = {
    "Environment": GENAI_DIR / "Image" / "00-Environment",
    "Texte": GENAI_DIR / "Texte",
    "Audio": GENAI_DIR / "Audio",
    "Video": GENAI_DIR / "Video",
    "Image": GENAI_DIR / "Image",
}

def find_notebooks(category_dir: Path) -> List[Path]:
    """Trouve tous les notebooks .ipynb dans un répertoire."""
    if not category_dir.exists():
        return []
    return sorted(category_dir.rglob("*.ipynb"))

def load_env_file(env_file: Path = ENV_FILE) -> Dict[str, str]:
    """Charge les variables d'environnement depuis le fichier .env GenAI."""
    env_vars = {}
    if env_file.exists():
        with open(env_file, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#') and '=' in line:
                    key, value = line.split('=', 1)
                    env_vars[key.strip()] = value.strip().strip('"').strip("'")
    return env_vars

def execute_notebook(notebook_path: Path, timeout: int = 300) -> Tuple[bool, str, float]:
    """
    Exécute un notebook avec Papermill en mode batch.

    Returns:
        (success, message, duration)
    """
    start_time = time.time()

    # Charger l'environnement: variables système + .env GenAI + BATCH_MODE
    env = os.environ.copy()
    env_vars = load_env_file()
    env.update(env_vars)
    env["BATCH_MODE"] = "true"

    # Output temporaire
    output_path = Path("C:\\Users\\jsboi\\AppData\\Local\\Temp\\temp_output.ipynb")

    cmd = [
        sys.executable, "-m", "papermill",
        str(notebook_path),
        str(output_path),
        "-k", "python3",
        "--cwd", str(notebook_path.parent),
        "--execution-timeout", str(timeout),
    ]

    try:
        result = subprocess.run(
            cmd,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout + 30,  # Marge pour Papermill lui-même
            encoding="utf-8",
            errors="replace",
        )

        duration = time.time() - start_time

        if result.returncode == 0:
            return True, "OK", duration
        else:
            error_msg = result.stderr[-500:] if result.stderr else "Unknown error"
            return False, error_msg.strip(), duration

    except subprocess.TimeoutExpired:
        duration = time.time() - start_time
        return False, f"Timeout after {timeout}s", duration
    except Exception as e:
        duration = time.time() - start_time
        return False, str(e), duration
    finally:
        # Nettoyer le fichier de sortie
        if output_path.exists():
            try:
                output_path.unlink()
            except:
                pass

def main():
    import argparse

    parser = argparse.ArgumentParser(description="Validation complète des notebooks GenAI")
    parser.add_argument("--category", "-c", default="all",
                        choices=["all", "Environment", "Texte", "Audio", "Video", "Image"],
                        help="Catégorie à valider")
    parser.add_argument("--timeout", "-t", type=int, default=300,
                        help="Timeout par notebook en secondes")
    parser.add_argument("--quick", "-q", action="store_true",
                        help="Mode rapide (timeout 60s)")

    args = parser.parse_args()

    if args.quick:
        args.timeout = 60

    print("=" * 70)
    print("  VALIDATION GENAI - EXECUTION NOTEBOOKS")
    print("=" * 70)
    print(f"Category: {args.category}")
    print(f"Timeout: {args.timeout}s per notebook")
    print()

    # Sélectionner les catégories
    categories_to_validate = (
        list(CATEGORIES.keys()) if args.category == "all"
        else [args.category]
    )

    results = {}
    total_success = 0
    total_fail = 0

    for category in categories_to_validate:
        category_dir = CATEGORIES[category]
        notebooks = find_notebooks(category_dir)

        if not notebooks:
            print(f"\n[{category}] No notebooks found")
            continue

        print(f"\n{'=' * 70}")
        print(f"  CATEGORY: {category} ({len(notebooks)} notebooks)")
        print(f"{'=' * 70}")

        category_results = []

        for nb_path in notebooks:
            rel_path = nb_path.relative_to(PROJECT_ROOT)
            nb_name = nb_path.name

            print(f"\n[{category}] {nb_name}...", end=" ", flush=True)

            success, message, duration = execute_notebook(nb_path, args.timeout)

            status_icon = "[+]" if success else "[X]"
            duration_str = f"{duration:.1f}s"

            print(f"{status_icon} {duration_str}")

            if not success:
                print(f"  ERROR: {message[:200]}")

            category_results.append({
                "path": str(rel_path),
                "name": nb_name,
                "success": success,
                "message": message,
                "duration": duration,
            })

            if success:
                total_success += 1
            else:
                total_fail += 1

        results[category] = category_results

    # Résumé final
    print("\n" + "=" * 70)
    print("  SUMMARY")
    print("=" * 70)

    for category, cat_results in results.items():
        success_count = sum(1 for r in cat_results if r["success"])
        total_count = len(cat_results)
        print(f"\n{category}: {success_count}/{total_count}")

        # Afficher les échecs
        failures = [r for r in cat_results if not r["success"]]
        for f in failures:
            print(f"  [X] {f['name']} - {f['message'][:100]}")

    total = total_success + total_fail
    rate = (total_success / total * 100) if total > 0 else 0

    print(f"\n{'=' * 70}")
    print(f"  TOTAL: {total_success}/{total} ({rate:.1f}%)")
    print(f"{'=' * 70}")

    return 0 if total_fail == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
