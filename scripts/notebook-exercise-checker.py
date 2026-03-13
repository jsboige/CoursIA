#!/usr/bin/env python3
"""
Script pour analyser les notebooks et detecter les cellules d'exercice.

Pour le TP ECE (issue #49), chaque notebook doit avoir des cellules d'exercice
clairement identifiables pour le systeme de bonus (0.5 pt par notebook correct).

Patterns de cellules d'exercice:
- Titres contenant: "Exercice", "A vous de jouer", "Your turn", "TP", "DEVOIR"
- Cellules vides ou avec placeholders
"""

import json
import sys
from pathlib import Path
from typing import Dict, List, Tuple
from collections import defaultdict

EXERCISE_PATTERNS = [
    "exercice", "à vous de jouer", "a vous de jouer", "your turn",
    "tp", "devoir", "practical", "workshop", "challenge",
    "quiz", "question", "problème", "probleme"
]

def analyze_notebook(path: Path) -> Dict:
    """Analyse un notebook et retourne les stats."""
    try:
        with open(path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
    except Exception as e:
        return {"error": str(e), "path": str(path)}

    stats = {
        "path": str(path),
        "name": path.name,
        "total_cells": len(nb.get("cells", [])),
        "code_cells": 0,
        "markdown_cells": 0,
        "exercise_cells": [],
        "has_outputs": False,
        "all_outputs": True,
        "empty_outputs": 0,
        "executable": True
    }

    cells = nb.get("cells", [])

    for i, cell in enumerate(cells):
        cell_type = cell.get("cell_type", "")
        source = "".join(cell.get("source", []))

        if cell_type == "code":
            stats["code_cells"] += 1
            has_output = bool(cell.get("outputs"))
            stats["has_outputs"] = stats["has_outputs"] or has_output

            if not has_output:
                stats["all_outputs"] = False
                stats["empty_outputs"] += 1

        elif cell_type == "markdown":
            stats["markdown_cells"] += 1
            # Chercher patterns d'exercice dans les titres
            lines = source.lower().split('\n')
            for line in lines:
                line_clean = line.strip().lstrip('#').strip()
                for pattern in EXERCISE_PATTERNS:
                    if pattern in line_clean:
                        stats["exercise_cells"].append({
                            "index": i,
                            "type": "markdown",
                            "title": line.strip(),
                            "pattern": pattern
                        })
                        break

        # Chercher les cellules de code vides (exercices à compléter)
        if cell_type == "code":
            source_stripped = source.strip()
            # Cellule vide ou avec placeholder
            if (not source_stripped or
                any(p in source.lower() for p in ["# votre code", "# your code", "todo", "fill in"])):
                # Vérifier si c'est potentiellement un exercice
                # (markdown précédent avec "exercice")
                if i > 0:
                    prev_cell = cells[i-1]
                    if prev_cell.get("cell_type") == "markdown":
                        prev_source = "".join(prev_cell.get("source", [])).lower()
                        if any(p in prev_source for p in EXERCISE_PATTERNS):
                            stats["exercise_cells"].append({
                                "index": i,
                                "type": "code",
                                "title": "Code cell to complete",
                                "empty": not source_stripped
                            })

    stats["has_exercises"] = len(stats["exercise_cells"]) > 0
    stats["exercise_count"] = len(stats["exercise_cells"])

    return stats

def generate_report(stats_list: List[Dict], series_name: str) -> str:
    """Génère un rapport Markdown."""
    report = [f"# Audit série {series_name} - Issue #49\n"]
    report.append(f"**Date**: {json.dumps(stats_list)}\n")

    total = len(stats_list)
    with_exercises = sum(1 for s in stats_list if s.get("has_exercises"))
    with_outputs = sum(1 for s in stats_list if s.get("all_outputs"))
    executable = sum(1 for s in stats_list if s.get("executable"))

    report.append("## Résumé\n")
    report.append(f"- **Total notebooks**: {total}\n")
    report.append(f"- **Avec exercices**: {with_exercises}/{total} ({100*with_exercises//total}%)\n")
    report.append(f"- **Avec sorties complètes**: {with_outputs}/{total} ({100*with_outputs//total}%)\n")
    report.append(f"- **Exécutables**: {executable}/{total} ({100*executable//total}%)\n")

    report.append("\n## Détail par notebook\n\n")

    for stats in sorted(stats_list, key=lambda x: x["name"]):
        name = stats["name"]
        status = "✅" if stats.get("has_exercises") else "❌"
        output_status = "✅" if stats.get("all_outputs") else "⚠️"

        report.append(f"### {status} {name} {output_status}\n")
        report.append(f"- **Cellules**: {stats.get('code_cells', 0)} code, {stats.get('markdown_cells', 0)} markdown\n")
        report.append(f"- **Exercices**: {stats.get('exercise_count', 0)}\n")

        if stats.get("exercise_cells"):
            report.append(f"  ```\n")
            for ex in stats["exercise_cells"]:
                report.append(f"  - Cell {ex['index']}: {ex.get('title', 'N/A')}\n")
            report.append(f"  ```\n")

        if not stats.get("all_outputs"):
            report.append(f"- **⚠️ Sorties manquantes**: {stats.get('empty_outputs', 0)} cellules\n")

        report.append("\n")

    # Notebooks sans exercices
    no_exercises = [s for s in stats_list if not s.get("has_exercises")]
    if no_exercises:
        report.append("## ⚠️ Notebooks SANS exercices (à compléter)\n\n")
        for stats in no_exercises:
            report.append(f"- [{stats['name']}]({stats['path']})\n")
        report.append("\n")

    # Notebooks avec sorties manquantes
    missing_outputs = [s for s in stats_list if not s.get("all_outputs")]
    if missing_outputs:
        report.append("## ⚠️ Notebooks avec sorties MANQUANTES\n\n")
        for stats in missing_outputs:
            report.append(f"- [{stats['name']}]({stats['path']}) - {stats.get('empty_outputs', 0)} cellules\n")
        report.append("\n")

    return "".join(report)

def main():
    if len(sys.argv) < 2:
        print("Usage: python notebook-exercise-checker.py <notebook_path>")
        sys.exit(1)

    path = Path(sys.argv[1])

    if path.is_file() and path.suffix == ".ipynb":
        notebooks = [path]
    elif path.is_dir():
        notebooks = list(path.rglob("*.ipynb"))
    else:
        print(f"Erreur: {path} n'est pas un notebook ou un dossier")
        sys.exit(1)

    print(f"Analyse de {len(notebooks)} notebooks...")

    stats_list = []
    for nb_path in sorted(notebooks):
        stats = analyze_notebook(nb_path)
        if "error" not in stats:
            stats_list.append(stats)
            print(f"  ✅ {stats['name']}: {stats['exercise_count']} exercices, outputs: {stats['all_outputs']}")
        else:
            print(f"  ❌ Erreur: {stats['path']} - {stats['error']}")

    # Générer le rapport
    series_name = path.parent.name if path.is_file() else path.name
    report = generate_report(stats_list, series_name)

    # Sauvegarder
    output_path = Path("scripts/ECE_TP_audit_report.md")
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(report)

    print(f"\n✅ Rapport sauvegardé: {output_path}")
    print("\n## Résumé:")
    print(f"- Total: {len(stats_list)} notebooks")
    print(f"- Avec exercices: {sum(1 for s in stats_list if s.get('has_exercises'))}")
    print(f"- Sorties complètes: {sum(1 for s in stats_list if s.get('all_outputs'))}")

if __name__ == "__main__":
    main()
