#!/usr/bin/env python3
"""Extract notebook cells into the translation-sync CSV (Epic #4957 / #1650).

Implements the T1 deliverable of issue #4957 : produire le CSV initial (langue pivot)
pour une série de notebooks, avec les hashes bidirectionnels qui rendent la
désynchronisation détectable mécaniquement (cf. check_translation_sync.py, T2).

Schéma CSV (ratifié #4957 §1) :

    notebook    chemin relatif du notebook source (langue pivot)
    cell_id     id nbformat stable de la cellule
    cell_type   markdown | code  (code -> seuls les commentaires sont traduits)
    src_lang    langue pivot de la cellule (normalement fr, cf. #1650 Phase 0.5)
    src_hash    hash du texte source au moment de la dernière synchro
    text_fr ... une colonne par langue vivante côté Argumentum
    hash_<lang> hash du texte déposé dans le notebook xxx_<lang>.ipynb à la dernière synchro

En extraction initiale (T1), seule la colonne pivot est remplie ; les colonnes des
autres langues sont vides (remplies par le moteur Argumentum lors de la resync, T3).

Usage :
    python scripts/translation/extract_cells_to_csv.py <notebook.ipynb | dir/> [-o CSV]
    python scripts/translation/extract_cells_to_csv.py MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/

Le CSV est écrit par défaut sur stdout (rediriger vers translations/<famille>/<série>.csv).
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from pathlib import Path

# Langues vivantes côté Argumentum (8 langues, #4957 §1).
# Le pivot (fr en Phase 0.5) est la source ; les autres sont cibles de traduction.
PIVOT_LANG = "fr"
TARGET_LANGS = ["en", "es", "ar", "fa", "zh", "ru", "pt"]

# Colonnes du CSV, dans l'ordre ratifié #4957 §1.
COLUMNS = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash"]
COLUMNS += [f"text_{lang}" for lang in [PIVOT_LANG] + TARGET_LANGS]
COLUMNS += [f"hash_{lang}" for lang in [PIVOT_LANG] + TARGET_LANGS]


def normalize(text: str) -> str:
    """Normalise le texte d'une cellule avant hash.

    On strip l'indentation de fin de ligne et les lignes vides de tête/queue pour
    qu'une édition cosmétique (espace en fin de ligne, newline terminal) ne déclenche
    pas un faux drift. Le contenu sémantique est préservé.
    """
    lines = [line.rstrip() for line in text.splitlines()]
    return "\n".join(lines).strip("\n")


def cell_hash(text: str) -> str:
    """Hash sha256 (16 hex chars) du texte normalisé.

    16 hex = 64 bits, largement suffisant pour du drift-detection intradépôt
    (birthday bound à ~4e9 cellules).
    """
    return hashlib.sha256(normalize(text).encode("utf-8")).hexdigest()[:16]


def extract_notebook(nb_path: Path, repo_root: Path, src_lang: str) -> list[dict]:
    """Extrait les cellules d'un notebook en lignes CSV.

    Saute les cellules sans id nbformat stable (cell_id vide = non traduisible de
    façon fiable). Les cellules vides sont incluses (leur texte peut être traduit).
    """
    rows = []
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        print(f"WARNING: {nb_path} ignoré (JSON illisible: {exc})", file=sys.stderr)
        return rows

    rel = nb_path.relative_to(repo_root).as_posix()
    for cell in nb.get("cells", []):
        cell_id = cell.get("id")
        if not cell_id:
            # Pas d'id stable = on ne peut pas suivre la cellule à travers les éditions.
            continue
        cell_type = cell.get("cell_type", "unknown")
        if cell_type not in ("markdown", "code"):
            continue
        text = "".join(cell.get("source", []))
        row = {col: "" for col in COLUMNS}
        row["notebook"] = rel
        row["cell_id"] = cell_id
        row["cell_type"] = cell_type
        row["src_lang"] = src_lang
        row["src_hash"] = cell_hash(text)
        # Pivot : on dépose le texte + son hash dans la colonne pivot. À l'extraction
        # initiale (T1) le pivot EST la source, donc hash_{src_lang} == src_hash par
        # construction (c'est intentionnel, pas une invariance à tester). Les vrais
        # invariants sont : (a) déterminisme byte-identique sur re-run, (b) en T2,
        # hash_{src_lang} != hash_{autre_lang} quand les textes diffèrent.
        row[f"text_{src_lang}"] = text
        row[f"hash_{src_lang}"] = row["src_hash"]
        rows.append(row)
    return rows


def iter_notebooks(target: Path) -> list[Path]:
    """Résout un fichier .ipynb ou un répertoire en liste de notebooks.

    Exclut les artefacts `_output.ipynb` (sorties Papermill) et les variantes
    `_agent.ipynb` (auto-générées, hors périmètre traduction). On utilise
    `endswith` (et non un substring `in`) pour ne pas exclure par erreur un
    notebook légitime comme `foo_output.ipynb`.
    """
    if target.is_file():
        return [target]
    return sorted(
        p
        for p in target.rglob("*.ipynb")
        if not p.name.endswith("_output.ipynb") and not p.name.endswith("_agent.ipynb")
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extrait les cellules de notebooks vers le CSV de synchro traduction (#4957)."
    )
    parser.add_argument(
        "input",
        type=Path,
        help="Notebook .ipynb ou répertoire de série (extraction récursive).",
    )
    parser.add_argument(
        "-o", "--output", type=Path, default=None, help="Fichier CSV de sortie (défaut : stdout)."
    )
    parser.add_argument(
        "--src-lang",
        default=PIVOT_LANG,
        choices=[PIVOT_LANG] + TARGET_LANGS,
        help=f"Langue pivot des notebooks source (défaut : {PIVOT_LANG}).",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Racine du dépôt pour calculer les chemins relatifs (défaut : cwd).",
    )
    args = parser.parse_args()

    if not args.input.exists():
        print(f"ERROR : {args.input} introuvable.", file=sys.stderr)
        return 2

    repo_root = (args.repo_root or Path.cwd()).resolve()
    notebooks = iter_notebooks(args.input)
    if not notebooks:
        print(f"ERROR : aucun notebook trouvé sous {args.input}.", file=sys.stderr)
        return 2

    rows: list[dict] = []
    for nb in notebooks:
        rows.extend(extract_notebook(nb.resolve(), repo_root, args.src_lang))

    if not rows:
        print(f"WARNING : 0 cellules extraites de {len(notebooks)} notebook(s).", file=sys.stderr)
        return 1

    out = sys.stdout
    if args.output:
        # Crée le répertoire parent si nécessaire (sinon open() lève FileNotFoundError).
        args.output.parent.mkdir(parents=True, exist_ok=True)
        out = args.output.open("w", encoding="utf-8", newline="")
    try:
        writer = csv.DictWriter(out, fieldnames=COLUMNS, quoting=csv.QUOTE_MINIMAL)
        writer.writeheader()
        writer.writerows(rows)
    finally:
        if args.output:
            out.close()

    sink = str(args.output) if args.output else "stdout"
    print(
        f"OK : {len(rows)} cellules extraites de {len(notebooks)} notebook(s) -> {sink}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
