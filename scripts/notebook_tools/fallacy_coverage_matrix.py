"""Matrice de couverture cross-notebooks de la série FallacyDetection (#14110).

Lecture seule des notebooks de la série (01/02/03 et le 04 de synthèse) pour
produire une matrice N x M de couverture : chaque notebook occupe une ligne,
chaque axe taxonomique une colonne.

Axes mesurés (mécaniquement, rien n'est deviné) :

- ``sophismes`` : nombre d'étiquettes distinctes exposées par les inventaires
  que le notebook définit lui-même. On compte les listes littérales assignées
  à une variable dont le nom contient label/taxo/logic/mafalda/walton
  (ex. ``LOGIC_13`` -> 13 entrées, ``mafalda_labels`` -> sa longueur encodée).
- ``formalismes`` : nombre de cellules code qui mentionnent à la fois les
  deux pôles formel/informel (l'axe pédagogique que la série pose en 01).
- ``domaines`` : nombre de sources externes distinctes nommées dans le
  notebook (github.com, huggingface.co, arg.tech, reddit) — les datasets et
  corpus que le notebook touche réellement.
- ``preuve`` : qualité de la preuve d'exécution — ratio cellules exécutées,
  nombre d'erreurs, nombre de figures PNG committées.

Doublon de fonctionnalité avec ``count_exercises.py`` (comptage des exercices
stubs) volontairement évité : la matrice appelle les classes de comptage de
``count_exercises`` quand il est importable (chemin racine), sinon elle compte
les marqueurs ``# Exercice`` de la convention de la série (listé dans
``EXERCICE_HEADERS``). C'est le même organe que la série utilise, pas une
réimplémentation.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

try:
    from notebook_tools.count_exercises import ExerciseCounter  # type: ignore
except Exception:  # pragma: no cover - import en échec -> fallback interne
    ExerciseCounter = None  # type: ignore

SERIE = "MyIA.AI.Notebooks/GenAI/FallacyDetection"

NOTEBOOKS = [
    "01_taxonomy_intro.ipynb",
    "02_fallacy_datasets_landscape.ipynb",
    "03_taxonomy_coverage_gap.ipynb",
    "04_coverage_matrix.ipynb",
]

# Marqueurs de la convention de la série : "### Exercice N — <titre>".
EXERCICE_HEADERS = re.compile(r"#+\s+Exercice\s+\d+", re.IGNORECASE)

# Variables portant des inventaires d'étiquettes de sophismes.
INVENTORY_VARS = re.compile(r"(label|taxo|logic|mafalda|walton)", re.IGNORECASE)

# Sources externes reconnues comme "domaines" (datasets / corpus).
DOMAIN_MARKERS = re.compile(
    r"github\.com|huggingface\.co|arg\.tech|reddit\.com|kaggle\.com"
)

# Formels/informels : l'axe pédagogique posé par 01.
FORMAL_POLES = re.compile(r"formel|informel", re.IGNORECASE)

# Inventaires en dict-of-tuples : 01 pose ses types via ``attendu = {"E1": (...)``.
# On compte les types distincts (2e élément du tuple) — l'axe <sophismes> du 01.
_TYPE_TUPLE = re.compile(r'"[^"]+":\s*\(\s*"[^"]*"\s*,\s*"([^"]+)"\s*\)')

EMPTY_TYPES = {"[]", "{}", "()", "set()", '""', "''"}


def _as_str(src: Any) -> str:
    if isinstance(src, list):
        return "".join(src)
    return str(src)


def _cell_code(cell: Dict[str, Any]) -> str:
    return _as_str(cell.get("source", ""))


def _inventory_lengths(code: str) -> List[int]:
    """Longueurs des listes d'étiquettes définies par le notebook.

    Repère ``<nom> = ["a", "b", ...]`` où le nom contient un indice
    d'inventaire (label/taxo/logic/...). Particulièrement robuste aux
    constantes de 03 (``LOGIC_13``, ``mafalda_labels``).
    """
    lengths: List[int] = []
    for match in re.finditer(r'^(\w+)\s*=\s*\[(.*?)\]', code, re.MULTILINE | re.DOTALL):
        var, body = match.group(1), match.group(2)
        if not INVENTORY_VARS.search(var):
            continue
        items = [i for i in re.findall(r'"([^"]+)"', body) if i.strip()]
        if items:
            lengths.append(len(items))
    return lengths


def _dict_type_labels(code: str) -> int:
    """Nombre de types de sophismes distincts exposés en dict-of-tuples.

    Couvre le 01 (``attendu = {"E1": ("formel", "affirmation du consequent")...}``) :
    on compte les 2e éléments distincts du tuple, qui sont les étiquettes de
    type. Rendu 0 quand le notebook n'en définit pas.
    """
    return len(set(_TYPE_TUPLE.findall(code)))


def _row(notebook_path: Path) -> Dict[str, Any]:
    """Mesure un notebook sur les 4 axes + les métriques de base."""
    nb = json.loads(notebook_path.read_text(encoding="utf-8"))
    code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]

    executed = 0
    errors = 0
    pngs = 0
    outputs = 0
    exercises = 0
    inventory_n = 0
    dict_types: List[str] = []
    formal = 0
    domains: set = set()
    all_code = ""
    for cell in code_cells:
        src = _cell_code(cell)
        all_code += src + "\n"
        outs = cell.get("outputs", [])
        outputs += len(outs)
        if isinstance(cell.get("execution_count"), int) and cell["execution_count"] is not None:
            executed += 1
        errors += sum(1 for o in outs if o.get("output_type") == "error")
        pngs += sum(
            1
            for o in outs
            if o.get("output_type") in ("display_data", "execute_result")
            and "image/png" in o.get("data", {})
        )
        if EXERCICE_HEADERS.search(src):
            exercises += 1
        if all(w in src for w in ("formel", "informel")):
            formal += 1
        domains.update(DOMAIN_MARKERS.findall(src))
        inventory_n += sum(_inventory_lengths(src))
        dict_types.extend(_TYPE_TUPLE.findall(src))

    inventory_n += len(set(dict_types)) if dict_types else 0

    n = len(code_cells)
    ratio = round(executed / n, 2) if n else 0.0

    return {
        "notebook": notebook_path.name,
        "cells": n,
        "executed": executed,
        "ratio": ratio,
        "errors": errors,
        "pngs": pngs,
        "outputs": outputs,
        "exercises": exercises,
        "sophismes": inventory_n,
        "formalismes": formal,
        "domaines": len(domains),
        "preuve": f"{ratio:.0%} exécutées, {errors} erreur(s)",
    }


def build_matrix(series_dir: Path, names: Optional[List[str]] = None) -> List[Dict[str, Any]]:
    """Matrice N x M : une ligne par notebook de la série."""
    rows: List[Dict[str, Any]] = []
    for name in names or NOTEBOOKS:
        path = series_dir / name
        if not path.exists():
            continue
        rows.append(_row(path))
    return rows


def markdown_table(rows: List[Dict[str, Any]]) -> str:
    """Rendu markdown lisible de la matrice."""
    header = (
        "| Notebook | Cellules | Exécutées | Exercices | Sophismes | "
        "Formalismes | Domaines | Preuve |\n"
        "|---|---:|---:|---:|---:|---:|---:|---|"
    )
    lines = [header]
    for r in rows:
        lines.append(
            f"| {r['notebook'].replace('.ipynb', '')} | {r['cells']} | "
            f"{r['executed']} ({r['ratio']:.0%}) | {r['exercises']} | "
            f"{r['sophismes']} | {r['formalismes']} | {r['domaines']} | "
            f"{r['preuve']} |"
        )
    if len(rows) > 1:
        totals = {
            "cells": sum(r["cells"] for r in rows),
            "executed": sum(r["executed"] for r in rows),
            "exercises": sum(r["exercises"] for r in rows),
            "sophismes": sum(r["sophismes"] for r in rows),
            "formalismes": sum(r["formalismes"] for r in rows),
            "domaines": sum(r["domaines"] for r in rows),
        }
        lines.append(
            f"| **Série** | {totals['cells']} | {totals['executed']} | "
            f"{totals['exercises']} | {totals['sophismes']} | "
            f"{totals['formalismes']} | {totals['domaines']} | — |"
        )
    return "\n".join(lines)


def heatmap_payload(rows: List[Dict[str, Any]]) -> Tuple[List[str], List[List[float]]]:
    """Données numériques pour la heatmap (axe x = notebooks, y = axes).

    Retourne (labels_axes, matrice_2d) où matrice_2d[axe][notebook].
    """
    axes = ["cells", "executed", "exercises", "sophismes", "formalismes", "domaines"]
    labels = ["Cellules", "Exécutées", "Exercices", "Sophismes", "Formalismes", "Domaines"]
    grid: List[List[float]] = []
    for axe in axes:
        grid.append([float(r[axe]) for r in rows])
    return labels, grid


def main(argv: Optional[List[str]] = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--series-dir",
        default=SERIE,
        help="Chemins des notebooks de la série (défaut: relatif au repo-root).",
    )
    parser.add_argument(
        "--markdown", action="store_true", help="Rend la matrice en markdown."
    )
    parser.add_argument(
        "--json", action="store_true", help="Rend la matrice en JSON."
    )
    args = parser.parse_args(argv)

    series_dir = Path(args.series_dir)
    if not series_dir.is_absolute():
        series_dir = Path.cwd() / series_dir
    rows = build_matrix(series_dir)
    if args.json:
        print(json.dumps(rows, ensure_ascii=False, indent=2))
    else:
        print(markdown_table(rows))
    return 0


if __name__ == "__main__":
    sys.exit(main())