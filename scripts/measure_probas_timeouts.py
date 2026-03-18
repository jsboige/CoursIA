#!/usr/bin/env python3
"""
Mesure les temps d'exécution des notebooks Probas (C# .NET Interactive)

Pour ECE TP #49 - Identifier les notebooks qui dépassent 5 minutes
"""

import json
import subprocess
import time
from pathlib import Path
from datetime import datetime

PROBAS_DIR = Path("MyIA.AI.Notebooks/Probas")
TIMEOUT_WARNING = 300  # 5 minutes en secondes

def get_notebooks():
    """Liste tous les notebooks Probas"""
    notebooks = []
    for nb_file in PROBAS_DIR.rglob("*.ipynb"):
        notebooks.append(nb_file)
    return sorted(notebooks)

def has_outputs(nb_path):
    """Vérifie si le notebook a des outputs"""
    try:
        with open(nb_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
        for cell in nb.get('cells', []):
            if cell.get('cell_type') == 'code' and cell.get('outputs'):
                return True
        return False
    except:
        return None

def execute_with_dotnet(nb_path):
    """
    Exécute un notebook .NET avec dotnet interactive
    Retourne (success, duration_seconds, error)
    """
    start = time.time()
    try:
        # Utiliser dotnet interactive pour exécuter
        # Note: Ceci est une approche simplifiée
        # En production, on utiliserait Microsoft.DotNet.Interactive.CSharp
        result = subprocess.run(
            ['dotnet', 'interactive', 'run', str(nb_path)],
            capture_output=True,
            text=True,
            timeout=TIMEOUT_WARNING + 60  # Marge de sécurité
        )
        duration = time.time() - start
        return (result.returncode == 0, duration, result.stderr)
    except subprocess.TimeoutExpired:
        duration = time.time() - start
        return (False, duration, "TIMEOUT")
    except Exception as e:
        duration = time.time() - start
        return (False, duration, str(e))

def main():
    print("🔍 Mesure des timeouts des notebooks Probas")
    print("=" * 60)

    notebooks = get_notebooks()
    print(f"📊 {len(notebooks)} notebooks trouvés\n")

    results = []

    for nb_path in notebooks:
        rel_path = nb_path.relative_to(PROBAS_DIR.parent)
        has_out = has_outputs(nb_path)

        print(f"📝 {rel_path}")
        print(f"   Outputs: {'✅' if has_out else '❌'}")

        # Si pas d'outputs, on tente l'exécution
        if not has_out:
            print(f"   ⏱️  Exécution en cours...")
            success, duration, error = execute_with_dotnet(nb_path)
            status = "✅" if success else "❌"
            print(f"   {status} Temps: {duration:.1f}s")

            if duration > TIMEOUT_WARNING:
                print(f"   ⚠️  WARNING: Dépasse 5 minutes!")
        else:
            # Estimation basée sur le nombre de cells
            with open(nb_path, 'r', encoding='utf-8') as f:
                nb = json.load(f)
            code_cells = sum(1 for c in nb.get('cells', []) if c.get('cell_type') == 'code')
            print(f"   📊 {code_cells} cellules de code")

            # Estimation très grossière: ~5s par cellule pour .NET
            estimated = code_cells * 5
            if estimated > TIMEOUT_WARNING:
                print(f"   ⚠️  Estimation: {estimated}s (> 5 min)")

        results.append({
            'path': str(rel_path),
            'has_outputs': has_out,
            'cells': code_cells if has_out else None
        })

    print("\n" + "=" * 60)
    print("📋 RÉSUMÉ")
    print("=" * 60)

    # Compter les notebooks potentiellement problématiques
    problem_count = sum(1 for r in results if r.get('cells', 0) > 60)
    print(f"⚠️  Notebooks potentiellement > 5 min: {problem_count}/{len(results)}")

if __name__ == "__main__":
    main()
