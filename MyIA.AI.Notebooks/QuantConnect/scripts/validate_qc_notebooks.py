"""
QuantConnect Notebooks Validator

Valide la structure et le contenu des notebooks QuantConnect (Python + C#).

Usage:
    python validate_qc_notebooks.py <path> [--quick] [--all] [--fix] [--verbose]

Arguments:
    path        : Chemin vers notebook ou répertoire (Python/, CSharp/, ou QuantConnect/)
    --quick     : Validation rapide (structure uniquement, pas d'exécution)
    --all       : Valider tous les notebooks (Python + C#)
    --fix       : Tenter corrections automatiques
    --verbose   : Affichage détaillé
    --python-only : Valider uniquement Python
    --csharp-only : Valider uniquement C#

Examples:
    python validate_qc_notebooks.py ../Python --quick
    python validate_qc_notebooks.py ../Python/QC-Py-01-Setup.ipynb --verbose
    python validate_qc_notebooks.py .. --all --quick
"""

import json
import sys
import os
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import re

# Ajouter le répertoire racine au path pour imports
script_dir = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(script_dir))


class NotebookValidator:
    """Validateur de notebooks QuantConnect"""

    EXPECTED_KERNELS = {
        'python': ['python3', 'quantconnect'],
        'csharp': ['.net-csharp', 'csharp']
    }

    REQUIRED_IMPORTS_PYTHON = [
        'from AlgorithmImports import *',
        'import pandas',
        'import numpy'
    ]

    REQUIRED_USING_CSHARP = [
        'using QuantConnect;',
        'using QuantConnect.Data;',
        'using QuantConnect.Algorithm;'
    ]

    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.errors = []
        self.warnings = []
        self.fixes_applied = []

    def log(self, message: str, level: str = 'INFO'):
        """Log message avec niveau"""
        if self.verbose or level in ['ERROR', 'WARNING']:
            prefix = {
                'INFO': '✓',
                'WARNING': '⚠',
                'ERROR': '✗',
                'FIX': '🔧'
            }.get(level, ' ')
            print(f"{prefix} {message}")

    def validate_notebook(self, notebook_path: Path, fix: bool = False) -> Tuple[bool, List[str], List[str]]:
        """
        Valide un notebook QuantConnect

        Returns:
            (is_valid, errors, warnings)
        """
        self.errors = []
        self.warnings = []
        self.fixes_applied = []

        if not notebook_path.exists():
            self.errors.append(f"Fichier non trouvé : {notebook_path}")
            return False, self.errors, self.warnings

        # Charger notebook
        try:
            with open(notebook_path, 'r', encoding='utf-8') as f:
                nb = json.load(f)
        except json.JSONDecodeError as e:
            self.errors.append(f"JSON invalide : {e}")
            return False, self.errors, self.warnings
        except Exception as e:
            self.errors.append(f"Erreur lecture : {e}")
            return False, self.errors, self.warnings

        # Détecter langage depuis nom fichier
        language = self._detect_language(notebook_path.name)
        if not language:
            self.errors.append(f"Impossible de détecter le langage depuis : {notebook_path.name}")
            return False, self.errors, self.warnings

        self.log(f"Validation de {notebook_path.name} (langage: {language})")

        # Validations
        self._validate_metadata(nb, language, fix)
        self._validate_cells(nb, language, fix)
        self._validate_structure(nb, language)
        self._validate_naming(notebook_path, language)

        # Appliquer fixes si demandé
        if fix and self.fixes_applied:
            try:
                with open(notebook_path, 'w', encoding='utf-8') as f:
                    json.dump(nb, f, indent=1, ensure_ascii=False)
                self.log(f"Fixes appliqués : {len(self.fixes_applied)}", 'FIX')
                for fix_msg in self.fixes_applied:
                    self.log(f"  - {fix_msg}", 'FIX')
            except Exception as e:
                self.errors.append(f"Erreur écriture fixes : {e}")

        is_valid = len(self.errors) == 0
        return is_valid, self.errors, self.warnings

    def _detect_language(self, filename: str) -> Optional[str]:
        """Détecter langage depuis nom fichier"""
        if 'Py' in filename or 'py' in filename.lower():
            return 'python'
        elif 'CS' in filename or 'csharp' in filename.lower():
            return 'csharp'
        return None

    def _validate_metadata(self, nb: dict, language: str, fix: bool):
        """Valider métadonnées notebook"""
        metadata = nb.get('metadata', {})

        # Vérifier kernel
        kernelspec = metadata.get('kernelspec', {})
        kernel_name = kernelspec.get('name', '')

        if kernel_name not in self.EXPECTED_KERNELS[language]:
            self.warnings.append(
                f"Kernel inattendu : {kernel_name}, attendu : {self.EXPECTED_KERNELS[language]}"
            )

            if fix:
                # Correction kernel
                if language == 'python':
                    kernelspec['name'] = 'python3'
                    kernelspec['display_name'] = 'Python 3 (QuantConnect)'
                else:
                    kernelspec['name'] = '.net-csharp'
                    kernelspec['display_name'] = '.NET (C#)'

                metadata['kernelspec'] = kernelspec
                nb['metadata'] = metadata
                self.fixes_applied.append(f"Kernel corrigé : {kernelspec['name']}")

        # Vérifier language_info
        if 'language_info' not in metadata:
            self.warnings.append("language_info manquant dans metadata")

            if fix:
                if language == 'python':
                    metadata['language_info'] = {
                        'name': 'python',
                        'version': '3.11.0'
                    }
                else:
                    metadata['language_info'] = {
                        'name': 'C#',
                        'version': '9.0'
                    }
                nb['metadata'] = metadata
                self.fixes_applied.append("language_info ajouté")

    def _validate_cells(self, nb: dict, language: str, fix: bool):
        """Valider cellules notebook"""
        cells = nb.get('cells', [])

        if len(cells) == 0:
            self.errors.append("Notebook vide (aucune cellule)")
            return

        # Vérifier première cellule (doit être markdown avec titre)
        first_cell = cells[0]
        if first_cell.get('cell_type') != 'markdown':
            self.warnings.append("Première cellule devrait être markdown (titre)")
        else:
            source = ''.join(first_cell.get('source', []))
            if not source.startswith('#'):
                self.warnings.append("Première cellule markdown devrait commencer par # (titre)")

        # Vérifier cellules de code
        code_cells = [c for c in cells if c.get('cell_type') == 'code']

        if len(code_cells) == 0:
            self.errors.append("Aucune cellule de code trouvée")
            return

        # Vérifier imports/using
        first_code_cell = code_cells[0]
        source = ''.join(first_code_cell.get('source', []))

        if language == 'python':
            required = self.REQUIRED_IMPORTS_PYTHON
        else:
            required = self.REQUIRED_USING_CSHARP

        missing_imports = []
        for imp in required:
            if imp not in source and not any(imp in ''.join(c.get('source', [])) for c in code_cells[:3]):
                missing_imports.append(imp)

        if missing_imports:
            self.warnings.append(f"Imports manquants (dans les 3 premières cellules) : {missing_imports}")

        # Vérifier cellules avec outputs (exécutées)
        executed_cells = [c for c in code_cells if c.get('outputs') or c.get('execution_count')]

        if len(executed_cells) > 0:
            self.warnings.append(
                f"{len(executed_cells)} cellules avec outputs (notebook exécuté). "
                "Recommandé : nettoyer avant commit"
            )

    def _validate_structure(self, nb: dict, language: str):
        """Valider structure générale"""
        # Vérifier nbformat
        nbformat_version = nb.get('nbformat', 0)
        if nbformat_version < 4:
            self.errors.append(f"nbformat obsolète : {nbformat_version}, requis : >= 4")

        # Vérifier taille raisonnable
        nb_str = json.dumps(nb)
        size_mb = len(nb_str) / (1024 * 1024)

        if size_mb > 10:
            self.warnings.append(f"Notebook très volumineux : {size_mb:.1f}MB (probablement outputs)")

    def _validate_naming(self, notebook_path: Path, language: str):
        """Valider convention de nommage"""
        filename = notebook_path.name

        # Pattern attendu : QC-Py-01-Setup.ipynb ou QC-CS-01-Setup.ipynb
        if language == 'python':
            pattern = r'^QC-Py-\d{2}-.+\.ipynb$'
            prefix = 'QC-Py-'
        else:
            pattern = r'^QC-CS-\d{2}-.+\.ipynb$'
            prefix = 'QC-CS-'

        if not re.match(pattern, filename):
            self.warnings.append(
                f"Nom fichier non conforme : {filename}, "
                f"attendu : {prefix}XX-Description.ipynb"
            )


def validate_directory(directory: Path, quick: bool = False, fix: bool = False,
                      verbose: bool = False, python_only: bool = False,
                      csharp_only: bool = False) -> Dict[str, any]:
    """
    Valide tous les notebooks dans un répertoire

    Returns:
        {
            'total': int,
            'valid': int,
            'invalid': int,
            'results': [{'notebook': Path, 'valid': bool, 'errors': [], 'warnings': []}]
        }
    """
    validator = NotebookValidator(verbose=verbose)
    results = {
        'total': 0,
        'valid': 0,
        'invalid': 0,
        'results': []
    }

    # Trouver tous les notebooks
    notebooks = []

    if directory.is_file() and directory.suffix == '.ipynb':
        notebooks = [directory]
    else:
        # Chercher dans Python/ et/ou CSharp/
        if not python_only and not csharp_only:
            # Les deux
            python_dir = directory / 'Python'
            csharp_dir = directory / 'CSharp'

            if python_dir.exists():
                notebooks.extend(python_dir.glob('*.ipynb'))
            if csharp_dir.exists():
                notebooks.extend(csharp_dir.glob('*.ipynb'))
        elif python_only:
            python_dir = directory if directory.name == 'Python' else directory / 'Python'
            if python_dir.exists():
                notebooks.extend(python_dir.glob('*.ipynb'))
        else:  # csharp_only
            csharp_dir = directory if directory.name == 'CSharp' else directory / 'CSharp'
            if csharp_dir.exists():
                notebooks.extend(csharp_dir.glob('*.ipynb'))

    if not notebooks:
        print(f"✗ Aucun notebook trouvé dans {directory}")
        return results

    # Valider chaque notebook
    for nb_path in sorted(notebooks):
        results['total'] += 1
        is_valid, errors, warnings = validator.validate_notebook(nb_path, fix=fix)

        results['results'].append({
            'notebook': nb_path,
            'valid': is_valid,
            'errors': errors,
            'warnings': warnings
        })

        if is_valid:
            results['valid'] += 1
            print(f"✓ {nb_path.name}")
        else:
            results['invalid'] += 1
            print(f"✗ {nb_path.name}")
            for err in errors:
                print(f"  ERROR: {err}")

        if warnings and verbose:
            for warn in warnings:
                print(f"  WARNING: {warn}")

    return results


def main():
    import argparse

    parser = argparse.ArgumentParser(description='Valider notebooks QuantConnect')
    parser.add_argument('path', type=str, help='Chemin vers notebook ou répertoire')
    parser.add_argument('--quick', action='store_true', help='Validation rapide')
    parser.add_argument('--all', action='store_true', help='Valider tous les notebooks')
    parser.add_argument('--fix', action='store_true', help='Tenter corrections automatiques')
    parser.add_argument('--verbose', action='store_true', help='Affichage détaillé')
    parser.add_argument('--python-only', action='store_true', help='Valider uniquement Python')
    parser.add_argument('--csharp-only', action='store_true', help='Valider uniquement C#')

    args = parser.parse_args()

    # Résoudre chemin
    path = Path(args.path).resolve()

    if not path.exists():
        print(f"✗ Chemin non trouvé : {path}")
        sys.exit(1)

    print("=" * 70)
    print("QuantConnect Notebooks Validator")
    print("=" * 70)
    print(f"Chemin : {path}")
    print(f"Mode : {'Quick' if args.quick else 'Full'}")
    print(f"Fix : {'Enabled' if args.fix else 'Disabled'}")
    print(f"Verbose : {'Yes' if args.verbose else 'No'}")
    print("=" * 70)
    print()

    # Valider
    results = validate_directory(
        path,
        quick=args.quick,
        fix=args.fix,
        verbose=args.verbose,
        python_only=args.python_only,
        csharp_only=args.csharp_only
    )

    # Résumé
    print()
    print("=" * 70)
    print("Résumé")
    print("=" * 70)
    print(f"Total notebooks : {results['total']}")
    print(f"✓ Valides : {results['valid']}")
    print(f"✗ Invalides : {results['invalid']}")

    if results['total'] > 0:
        success_rate = (results['valid'] / results['total']) * 100
        print(f"Taux de succès : {success_rate:.1f}%")

    # Exit code
    sys.exit(0 if results['invalid'] == 0 else 1)


if __name__ == '__main__':
    main()
