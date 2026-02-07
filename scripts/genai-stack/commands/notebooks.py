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

from config import GENAI_DIR
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
        }

    def find_notebooks(self) -> List[Path]:
        """Liste les fichiers .ipynb."""
        if self.target_path.is_file():
            if self.target_path.suffix == '.ipynb':
                return [self.target_path]
            return []
        return list(self.target_path.rglob("*.ipynb"))

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
    parser.add_argument('--cleanup', action='store_true',
                       help='Supprimer les notebooks executes apres validation')


def execute(args) -> int:
    """Execute la commande notebooks."""
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
                       datefmt='%H:%M:%S')

    validator = NotebookValidator(args.target)
    results = validator.run_validation()
    validator.save_report(results)

    if args.cleanup:
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
    parser.add_argument('--cleanup', action='store_true')
    args = parser.parse_args()
    sys.exit(execute(args))


if __name__ == "__main__":
    main()
