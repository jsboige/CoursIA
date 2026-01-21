#!/usr/bin/env python3
"""
validate_notebooks.py - Validation massive des notebooks pédagogiques

Objectif : Valider que tous les notebooks fonctionnent avec la nouvelle stack unifiée.
- Utilise papermill pour l'exécution
- Injecte l'authentification
- Génère un rapport JSON

Usage:
    python scripts/genai-stack/validate_notebooks.py [--target-dir DIR]
"""

import sys
import os
import json
import logging
import argparse
import papermill as pm
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Optional

# Ajout du path pour les imports
current_dir = Path(__file__).resolve().parent
sys.path.append(str(current_dir))
sys.path.append(str(current_dir / "utils"))
sys.path.append(str(current_dir / "core"))

try:
    from core.auth_manager import GenAIAuthManager
except ImportError as e:
    print(f"❌ Erreur d'import critique: {e}")
    sys.exit(1)

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("NotebookValidator")

class NotebookValidator:
    def __init__(self, target_path: str):
        self.target_path = Path(target_path)
        self.auth_manager = GenAIAuthManager()
        self.config = self.auth_manager.load_config()
        self.token = self.config.get('bcrypt_hash') if self.config else None
        
        if not self.token:
            logger.warning("⚠️ Token d'authentification non trouvé via AuthManager. Les notebooks nécessitant une auth pourraient échouer.")
            # Tentative de récupération via env var classique au cas où
            self.token = os.getenv("COMFYUI_AUTH_TOKEN")
            
        self.env_vars = {
            "COMFYUI_URL": "http://localhost:8188",
            "COMFYUI_AUTH_TOKEN": self.token if self.token else "",
            # Pour éviter les problèmes d'affichage interactif
            "JUPYTER_PLATFORM_DIRS": "1"
        }

    def find_notebooks(self) -> List[Path]:
        """Liste les fichiers .ipynb (unique ou dossier récursif)"""
        if self.target_path.is_file():
            if self.target_path.suffix == '.ipynb':
                return [self.target_path]
            return []
        return list(self.target_path.rglob("*.ipynb"))

    def validate_notebook(self, notebook_path: Path, output_dir: Path) -> Dict:
        """Exécute un notebook via papermill"""
        
        # Calcul du chemin relatif pour l'output
        if self.target_path.is_file():
            rel_path = notebook_path.name
        else:
            try:
                rel_path = notebook_path.relative_to(self.target_path)
            except ValueError:
                rel_path = notebook_path.name
                
        output_path = output_dir / rel_path
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        logger.info(f"📓 Validation de : {rel_path}")
        
        start_time = datetime.now()
        status = "success"
        error_msg = None
        
        # Préparation des paramètres
        # On injecte les variables d'environnement dans le processus
        # papermill n'injecte pas directement dans os.environ du notebook, 
        # mais on peut passer des paramètres si le notebook a une cellule taggée 'parameters'
        # Cependant, la plupart des notebooks utilisent os.getenv().
        # Donc on va modifier os.environ pour le processus actuel (si papermill lance un sous-process, il hérite)
        
        original_env = os.environ.copy()
        os.environ.update(self.env_vars)
        
        try:
            pm.execute_notebook(
                input_path=str(notebook_path),
                output_path=str(output_path),
                cwd=str(notebook_path.parent), # Exécuter dans le dossier du notebook pour les imports relatifs
                kernel_name="python3", # Assumer python3 par défaut
                progress_bar=False,
                log_output=True
            )
        except Exception as e:
            status = "failed"
            error_msg = str(e)
            logger.error(f"❌ Échec de {rel_path}: {e}")
        finally:
            # Restauration env
            os.environ.clear()
            os.environ.update(original_env)
            
        duration = (datetime.now() - start_time).total_seconds()
        
        return {
            "notebook": str(rel_path),
            "status": status,
            "duration": duration,
            "error": error_msg,
            "output_path": str(output_path)
        }

    def run_validation(self) -> List[Dict]:
        """Lance la validation sur tous les notebooks trouvés"""
        notebooks = self.find_notebooks()
        logger.info(f"🔍 {len(notebooks)} notebooks trouvés dans {self.target_path}")
        
        output_dir = Path("rapports/notebook_validation")
        output_dir.mkdir(parents=True, exist_ok=True)
        
        results = []
        for nb in notebooks:
            # Skip des notebooks temporaires ou checkpoints
            if ".ipynb_checkpoints" in str(nb):
                continue
                
            result = self.validate_notebook(nb, output_dir)
            results.append(result)
            
        return results

    def save_report(self, results: List[Dict]):
        """Sauvegarde le rapport JSON"""
        report = {
            "timestamp": datetime.now().isoformat(),
            "total_notebooks": len(results),
            "passed": len([r for r in results if r["status"] == "success"]),
            "failed": len([r for r in results if r["status"] == "failed"]),
            "results": results
        }
        
        report_path = Path("notebook_validation_report.json")
        with open(report_path, "w", encoding="utf-8") as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
            
        logger.info(f"📝 Rapport généré : {report_path.absolute()}")
        
        # Affichage résumé console
        print("\n" + "="*40)
        print("📊 RÉSUMÉ VALIDATION NOTEBOOKS")
        print("="*40)
        print(f"Total: {report['total_notebooks']}")
        print(f"✅ Succès: {report['passed']}")
        print(f"❌ Échecs: {report['failed']}")
        
        if report['failed'] > 0:
            print("\n❌ Notebooks en échec:")
            for r in results:
                if r['status'] == 'failed':
                    print(f" - {r['notebook']} ({r['error'][:100]}...)")
        print("="*40)

def main():
    parser = argparse.ArgumentParser(description="Notebook Validation Suite")
    parser.add_argument('target', nargs='?', type=str, default="MyIA.AI.Notebooks/GenAI", help='Dossier ou fichier cible')
    parser.add_argument('--cleanup', action='store_true',
                        help='Supprimer les notebooks executes apres validation (conserve uniquement le rapport JSON)')

    args = parser.parse_args()

    validator = NotebookValidator(args.target)
    results = validator.run_validation()
    validator.save_report(results)

    # Nettoyage des notebooks executes si demande
    if args.cleanup:
        import shutil
        output_dir = Path("rapports/notebook_validation")
        if output_dir.exists():
            shutil.rmtree(output_dir)
            logger.info(f"🧹 Nettoyage: {output_dir} supprime")

    if any(r['status'] == 'failed' for r in results):
        sys.exit(1)

    sys.exit(0)

if __name__ == "__main__":
    main()