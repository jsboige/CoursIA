#!/usr/bin/env python3
"""Inventaire de preuves sous le carnet pour le futur graphe du cursus.

L'index de cellule est relatif à la révision lue, et l'id Jupyter facultatif
n'est pas un identifiant d'entité du graphe. Plusieurs exercices peuvent être
regroupés dans une cellule ; le compteur ne fournit pas leurs positions
individuelles. Les exemples non crédités ne sont pas recensés par cet organe.
Aucun identifiant durable ou lien RDF n'est attribué ici : les noms du cursus
attendent encore leurs arbitrages (#24993).
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from check_credited_examples import is_credited_example_header
from count_exercises import count_exercises_in_notebook


def inventory(path: Path, notebook_path: str) -> dict:
    """Retourne des localisateurs et les preuves des organes existants.

    ``notebook_path`` est le chemin fourni par l'appelant, relatif au dépôt.
    Les localisateurs ne sont valables que pour cette version du carnet. Une
    erreur de lecture ou d'analyse est propagée, jamais convertie en inventaire
    vide. Les comptes et exclusions restent ceux des organes propriétaires.
    """
    with path.open(encoding="utf-8-sig") as stream:
        notebook = json.load(stream)
    cells = notebook["cells"]
    count = count_exercises_in_notebook(path)
    if count.parse_error:
        raise ValueError(count.parse_error)

    def location(index: int) -> dict:
        cell_id = cells[index].get("id")
        return {"cell_index": index, "cell_id": cell_id if isinstance(cell_id, str) and cell_id else None}

    grouped = Counter((hit.cell_index, hit.detected_by) for hit in count.exercises)
    exercises = [
        {**location(index), "detected_by": detected_by, "count": n}
        for (index, detected_by), n in sorted(grouped.items())
    ]
    examples = [location(index) for index, cell in enumerate(cells)
                if is_credited_example_header(cell)]
    return {
        "schema_version": 1,
        "notebook": notebook_path,
        "exercises": exercises,
        "unpaired_markdown_instances": count.unpaired_markdown_instances,
        "credited_examples": examples,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("notebook", type=Path, help="Chemin du carnet à inventorier")
    args = parser.parse_args()
    print(json.dumps(inventory(args.notebook, args.notebook.as_posix()), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
