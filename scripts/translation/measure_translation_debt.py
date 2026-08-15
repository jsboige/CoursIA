#!/usr/bin/env python3
r"""measure_translation_debt.py -- etape 1 de #10329 : chiffrer la dette reelle.

## Pourquoi ce script existe

Issue #10329 a etabli qu'un run vert de `translation-sync.yml` peut pousser un
artefact **faux** : le pipeline T1 est incremental sur un etat qui n'a jamais
ete initialise (T1 ne touche que les notebooks **changes**), donc une dette
anterieure au cablage du pipeline n'est jamais rattrapee par aucun run futur.

Pour chiffrer cette dette avant de corriger, il faut un script qui, pour
chaque CSV de `translations/` :

  1. Liste les notebooks references dans le CSV.
  2. Pour chaque notebook :
       - ouvre le `.ipynb` source sur disque,
       - compte les cellules avec `id` nbformat stable ET `cell_type` in
         {markdown, code} (memes regles que `extract_cells_to_csv.py` T1),
       - calcule la dette d'indexation : cellules source absentes du CSV
         (`missing_from_csv`),
       - calcule l'inverse : lignes CSV pointant vers un `cell_id` qui
         n'existe plus dans le notebook (`extra_in_csv` = ORPHAN_ROW).
  3. Pour chaque ligne CSV :
       - si `text_fr` est rempli (texte pivot depose) ET `text_<lang>` est
         vide pour une langue cible -> dette de traduction pour cette langue.
  4. Signale les notebooks references par le CSV mais absents du disque
     (`ORPHAN_NOTEBOOK`) -- la dette est invisible depuis T2, qui n'ouvre
     que des notebooks presents.

C'est une mesure **read-only** : le script ne modifie aucun CSV, aucun
notebook. Il sert de **ligne de base** avant l'etape 2 de #10329 (un passage
T1 plein perimetre avec `--update`) et de **garde-fou** : apres correction,
un nouveau run doit faire baisser les compteurs (sinon la correction est
cosmetique).

## Sortie

- stdout : JSON consommable par CI / dashboards.
- stderr : rapport humain (par CSV, totaux agreges).
- Exit code : 0 toujours (read-only, non-bloquant comme T2).

## Usage

    # Rapport complet sur tous les CSV du repo
    python scripts/translation/measure_translation_debt.py

    # Un CSV isole
    python scripts/translation/measure_translation_debt.py translations/genai/finetuning.csv

    # Plusieurs CSV
    python scripts/translation/measure_translation_debt.py translations/genai/

    # Cible de dette differente (defaut : en, premiere langue vivante)
    python scripts/translation/measure_translation_debt.py --target-lang en
    python scripts/translation/measure_translation_debt.py --target-lang es

## Couplage

- Meme source de langues que `extract_cells_to_csv.py` (T1) et
  `check_translation_sync.py` (T2) : `check_perimeter.PIVOT_LANG` /
  `TARGET_LANGS` (source unique, #10109).
- Memes regles de comptage de cellules que `extract_cells_to_csv.py` T1
  (`id` non-vide ET `cell_type` in {markdown, code}).
- Le verbe "dette" suit la definition de #10329 section "Perimetre de la
  dette" : "lignes CSV OU `text_<lang>` est vide alors que `text_fr` est
  rempli" = traduction non deposee.
"""
from __future__ import annotations

import argparse
import csv
import io
import json
import sys
from collections import defaultdict
from pathlib import Path

# Source unique des langues (cf. check_perimeter.py #10109, design note
# "TARGET_LANGS single source of truth -- collapse 8 duplicates").
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_perimeter import PIVOT_LANG, TARGET_LANGS  # noqa: E402


# --------------------------------------------------------------------------
# Helpers -- identiques a extract_cells_to_csv.py pour rester en phase.
# --------------------------------------------------------------------------

def _iter_id_cells(nb_path: Path) -> set[str]:
    """Retourne l'ensemble des `cell_id` traductibles d'un notebook.

    Meme regle que `extract_cells_to_csv.extract_notebook` (T1) :
    - `cell_type in {"markdown", "code"}`
    - `cell["id"]` non vide (cle de suivi inter-editions)

    Silencieux sur JSON illisible (le notebook peut etre corrompu / vide /
    en cours d'edition) : retourne un ensemble vide, et le rapport agregera
    le notebook comme ERROR_JSON pour investigation separee.
    """
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError, OSError):
        return set()
    return {
        c["id"]
        for c in nb.get("cells", [])
        if c.get("id") and c.get("cell_type") in ("markdown", "code")
    }


def _csv_column(rows: list[dict], column: str) -> str:
    """Recupere une colonne du CSV (vide si absente -- compat ascendante)."""
    # DictReader garantit l'acces par cle, mais une cle manquante peut
    # survenir sur un CSV cree par une version antérieure du schema.
    for row in rows:
        row.setdefault(column, "")
    return ""  # signature : on mute rows en place


def _load_csv(csv_path: Path) -> tuple[list[str], list[dict]]:
    """Charge un CSV et garanti la presence des colonnes requises.

    Returns (fieldnames, rows). Si le CSV est vide, retourne ([], []).
    """
    with csv_path.open(encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        rows = list(reader)
        fieldnames = list(reader.fieldnames or [])
    return fieldnames, rows


def _normalize_column_order(fieldnames: list[str]) -> list[str]:
    """Reordonne les colonnes pour respecter le schema ratifie #4957 §1.

    Le CSV peut etre dans un ordre arbitraire (genere par un outil tiers,
    edite a la main, etc.). Le rapport utilise l'ordre canonique pour
    rester comparable entre CSV.
    """
    canonical = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash"]
    canonical += [f"text_{lang}" for lang in [PIVOT_LANG] + TARGET_LANGS]
    canonical += [f"hash_{lang}" for lang in [PIVOT_LANG] + TARGET_LANGS]
    # Conserve uniquement les colonnes effectivement presentes dans le CSV
    # (un CSV peut etre en schema reduit pre-T3, ou post-T3 etendu).
    return [c for c in canonical if c in fieldnames]


# --------------------------------------------------------------------------
# Coeur -- mesure pour UN CSV.
# --------------------------------------------------------------------------

def measure_csv(csv_path: Path, repo_root: Path, target_lang: str) -> dict:
    """Mesure la dette d'un CSV isole.

    Returns un dict structure :
        {
          "csv": <path>,
          "notebooks_referenced": int,
          "notebooks_present_on_disk": int,
          "orphan_notebooks": [list of notebook paths absents du disque],
          "total_source_cells": int,        # cellules avec id stable, tous notebooks presents
          "total_csv_rows": int,            # lignes CSV (toutes sources confondues)
          "indexing_debt": {
              "missing_from_csv": int,      # cellules source absentes du CSV
              "extra_in_csv": int,          # lignes CSV -> cell_id absent du notebook
              "by_notebook": {              # detail par notebook
                  "<rel_path>": {
                      "source_cells": int,
                      "csv_rows": int,
                      "missing_from_csv": int,
                      "extra_in_csv": int,
                  },
                  ...
              },
          },
          "translation_debt": {
              "rows_with_fr_filled": int,           # lignes CSV avec text_fr non-vide
              "rows_with_target_empty": int,        # lignes avec text_target vide
              "by_lang": {                         # (informatif, 1 seule target_lang par run)
                  "<lang>": int,
              },
          },
          "error_notebooks": [list de notebooks illisibles],
        }
    """
    fieldnames, rows = _load_csv(csv_path)

    # Indexation des lignes CSV par (notebook, cell_id)
    csv_index: dict[str, set[str]] = defaultdict(set)
    target_empty_rows: list[tuple[str, str]] = []  # (notebook, cell_id) ou text_target vide
    fr_filled_rows: list[tuple[str, str]] = []    # (notebook, cell_id) ou text_fr rempli
    pivot_col = f"text_{PIVOT_LANG}"
    target_col = f"text_{target_lang}"

    for row in rows:
        nb = row.get("notebook", "")
        cid = row.get("cell_id", "")
        if not nb or not cid:
            continue
        csv_index[nb].add(cid)
        # Dette de traduction : on regarde le contenu actuel de la ligne.
        if row.get(pivot_col, ""):
            fr_filled_rows.append((nb, cid))
            if not row.get(target_col, ""):
                target_empty_rows.append((nb, cid))

    # Indexation des cellules source par notebook
    source_index: dict[str, set[str]] = {}
    orphan_notebooks: list[str] = []
    error_notebooks: list[str] = []
    total_source_cells = 0

    for nb_rel in sorted(csv_index.keys()):
        nb_path = (repo_root / nb_rel).resolve()
        if not nb_path.exists():
            orphan_notebooks.append(nb_rel)
            continue
        cells = _iter_id_cells(nb_path)
        if not cells and not _is_empty_notebook(nb_path):
            error_notebooks.append(nb_rel)
        source_index[nb_rel] = cells
        total_source_cells += len(cells)

    # Calcul indexation dette par notebook
    indexing_detail: dict[str, dict] = {}
    total_missing_from_csv = 0
    total_extra_in_csv = 0
    for nb_rel in sorted(csv_index.keys()):
        if nb_rel in orphan_notebooks or nb_rel in error_notebooks:
            continue
        source_cells = source_index.get(nb_rel, set())
        csv_cells = csv_index[nb_rel]
        missing = source_cells - csv_cells
        extra = csv_cells - source_cells
        indexing_detail[nb_rel] = {
            "source_cells": len(source_cells),
            "csv_rows": len(csv_cells),
            "missing_from_csv": len(missing),
            "missing_from_csv_ids": sorted(missing),  # explicit IDs for debugging
            "extra_in_csv": len(extra),
            "extra_in_csv_ids": sorted(extra),
        }
        total_missing_from_csv += len(missing)
        total_extra_in_csv += len(extra)

    return {
        "csv": csv_path.as_posix(),
        "target_lang": target_lang,
        "notebooks_referenced": len(csv_index),
        "notebooks_present_on_disk": len(source_index),
        "orphan_notebooks": sorted(orphan_notebooks),
        "error_notebooks": sorted(error_notebooks),
        "total_source_cells": total_source_cells,
        "total_csv_rows": sum(len(s) for s in csv_index.values()),
        "indexing_debt": {
            "missing_from_csv": total_missing_from_csv,
            "extra_in_csv": total_extra_in_csv,
            "by_notebook": indexing_detail,
        },
        "translation_debt": {
            "rows_with_fr_filled": len(fr_filled_rows),
            "rows_with_target_empty": len(target_empty_rows),
            "by_lang": {target_lang: len(target_empty_rows)},
        },
        "column_order": _normalize_column_order(fieldnames),
    }


def _is_empty_notebook(nb_path: Path) -> bool:
    """Detecte un notebook vide / corrompu : 0 cellule OU JSON illisible.

    Utilise pour distinguer un notebook **vraiment vide** (en cours
    d'edition, pas encore de cellules) d'un notebook **illisibles**
    (JSON casse, encoding foireux). Le rapport agrege les illisibles
    dans `error_notebooks` pour investigation separee.
    """
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
        return len(nb.get("cells", [])) == 0
    except (json.JSONDecodeError, UnicodeDecodeError, OSError):
        return False  # _iter_id_cells aura deja leve silencieusement


# --------------------------------------------------------------------------
# Coeur -- mesure pour un set de CSV.
# --------------------------------------------------------------------------

def measure_csvs(csv_paths: list[Path], repo_root: Path, target_lang: str) -> dict:
    """Agrege la mesure de plusieurs CSV en un rapport global.

    La structure du rapport top-level :
        {
          "target_lang": str,
          "csv_count": int,
          "aggregate": {
              "notebooks_referenced": int,
              "orphan_notebooks": [list uniquee],
              "total_source_cells": int,
              "total_csv_rows": int,
              "indexing_missing_from_csv": int,
              "indexing_extra_in_csv": int,
              "translation_debt": int,
              "rows_with_fr_filled": int,
          },
          "per_csv": [mesure_csv(...) pour chaque CSV],
        }
    """
    per_csv: list[dict] = []
    agg = {
        "notebooks_referenced": 0,
        "orphan_notebooks": [],
        "total_source_cells": 0,
        "total_csv_rows": 0,
        "indexing_missing_from_csv": 0,
        "indexing_extra_in_csv": 0,
        "translation_debt": 0,
        "rows_with_fr_filled": 0,
    }
    seen_orphan: set[str] = set()

    for csv_path in sorted(csv_paths):
        m = measure_csv(csv_path, repo_root, target_lang)
        per_csv.append(m)
        agg["notebooks_referenced"] += m["notebooks_referenced"]
        agg["total_source_cells"] += m["total_source_cells"]
        agg["total_csv_rows"] += m["total_csv_rows"]
        agg["indexing_missing_from_csv"] += m["indexing_debt"]["missing_from_csv"]
        agg["indexing_extra_in_csv"] += m["indexing_debt"]["extra_in_csv"]
        agg["translation_debt"] += m["translation_debt"]["rows_with_target_empty"]
        agg["rows_with_fr_filled"] += m["translation_debt"]["rows_with_fr_filled"]
        for orphan in m["orphan_notebooks"]:
            if orphan not in seen_orphan:
                seen_orphan.add(orphan)
                agg["orphan_notebooks"].append(orphan)

    return {
        "target_lang": target_lang,
        "csv_count": len(per_csv),
        "aggregate": agg,
        "per_csv": per_csv,
    }


# --------------------------------------------------------------------------
# Rapport humain -- sortie stderr, line-oriented, facile a grep.
# --------------------------------------------------------------------------

def render_human_report(report: dict) -> str:
    """Genere le rapport texte pour stderr.

    Format : un bloc par CSV + un bloc agrege en fin. Pas de couleurs ANSI
    (consommable en CI log).
    """
    out = io.StringIO()
    target_lang = report["target_lang"]

    out.write(f"# Translation debt measurement (#10329 etape 1)\n")
    out.write(f"# Cible de dette : {target_lang} (utiliser --target-lang pour en changer)\n")
    out.write(f"# CSV scannes : {report['csv_count']}\n")
    out.write("\n")

    for m in report["per_csv"]:
        out.write(f"## {m['csv']}\n")
        out.write(f"  notebooks references : {m['notebooks_referenced']}\n")
        out.write(f"  presents sur disque   : {m['notebooks_present_on_disk']}\n")
        if m["orphan_notebooks"]:
            out.write(f"  ORPHAN_NOTEBOOK       : {len(m['orphan_notebooks'])} "
                      f"(CSV pointe vers fichier absent)\n")
        if m["error_notebooks"]:
            out.write(f"  ERROR_NOTEBOOK        : {len(m['error_notebooks'])} "
                      f"(JSON illisible ou vide)\n")
        idx = m["indexing_debt"]
        tr = m["translation_debt"]
        out.write(f"  cellules source      : {m['total_source_cells']}\n")
        out.write(f"  lignes CSV           : {m['total_csv_rows']}\n")
        out.write(f"  DETTE INDEXATION     : {idx['missing_from_csv']} "
                  f"(cellules source absentes du CSV)\n")
        out.write(f"  ORPHAN_ROW (extra)   : {idx['extra_in_csv']} "
                  f"(lignes CSV -> cell_id supprime)\n")
        out.write(f"  DETTE TRADUCTION {target_lang} : "
                  f"{tr['rows_with_target_empty']}/{tr['rows_with_fr_filled']} "
                  f"(text_{target_lang} vide alors que text_fr rempli)\n")
        # Detail par notebook -- seulement les non-zero, pour rester compact.
        for nb_rel, d in sorted(idx["by_notebook"].items()):
            if d["missing_from_csv"] or d["extra_in_csv"]:
                out.write(f"    - {nb_rel} : "
                          f"src={d['source_cells']} csv={d['csv_rows']} "
                          f"missing={d['missing_from_csv']} "
                          f"extra={d['extra_in_csv']}\n")
                if d["missing_from_csv"]:
                    out.write(f"        missing_ids = {d['missing_from_csv_ids'][:5]}"
                              f"{'...' if len(d['missing_from_csv_ids']) > 5 else ''}\n")
        out.write("\n")

    a = report["aggregate"]
    out.write("# === AGREGAT TOUS CSV ===\n")
    out.write(f"  notebooks references        : {a['notebooks_referenced']}\n")
    out.write(f"  cellules source (presentes) : {a['total_source_cells']}\n")
    out.write(f"  lignes CSV                  : {a['total_csv_rows']}\n")
    out.write(f"  DETTE INDEXATION            : {a['indexing_missing_from_csv']}\n")
    out.write(f"  ORPHAN_ROW                  : {a['indexing_extra_in_csv']}\n")
    out.write(f"  ORPHAN_NOTEBOOK             : {len(a['orphan_notebooks'])}\n")
    out.write(f"  DETTE TRADUCTION {target_lang} : "
              f"{a['translation_debt']}/{a['rows_with_fr_filled']}\n")
    return out.getvalue()


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def _resolve_csv_paths(inputs: list[Path], repo_root: Path) -> list[Path]:
    """Resout une liste de chemins (CSV ou repertoires) en CSV triés dedupliques.

    Un repertoire est scanne recursivement. Les fichiers qui ne sont pas des
    CSV ou qui n'existent pas sont silencieusement ignores (l'appelant CLI
    les a peut-etre tapes par erreur ; le rapport reste utile).
    """
    seen: set[Path] = set()
    out: list[Path] = []
    for raw in inputs:
        if not raw.exists():
            continue
        if raw.is_file():
            if raw.suffix.lower() == ".csv" and raw not in seen:
                seen.add(raw)
                out.append(raw)
        else:
            for p in sorted(raw.rglob("*.csv")):
                if p not in seen:
                    seen.add(p)
                    out.append(p)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument(
        "inputs",
        type=Path,
        nargs="*",
        help="Chemins (CSV ou repertoires) a mesurer. Defaut : translations/ du repo.",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Racine du depot (defaut : cwd). Utilise pour calculer les chemins relatifs.",
    )
    parser.add_argument(
        "--target-lang",
        default=None,
        help=(
            f"Cible de dette de traduction (defaut : premiere de TARGET_LANGS, "
            f"actuellement {TARGET_LANGS[0]})."
        ),
    )
    parser.add_argument(
        "--json-only",
        action="store_true",
        help="Ne sort que le JSON sur stdout (silencieux sur stderr). "
             "Utile pour consommation CI.",
    )
    args = parser.parse_args(argv)

    target_lang = args.target_lang or TARGET_LANGS[0]
    repo_root = (args.repo_root or Path.cwd()).resolve()
    inputs = args.inputs or [repo_root / "translations"]
    csv_paths = _resolve_csv_paths(inputs, repo_root)

    if not csv_paths:
        print(
            f"ERROR : aucun CSV trouve dans {inputs}",
            file=sys.stderr,
        )
        return 2

    report = measure_csvs(csv_paths, repo_root, target_lang)

    # Sortie JSON sur stdout (consommable CI, line-oriented pour grep).
    print(json.dumps(report, indent=2, ensure_ascii=False))

    if not args.json_only:
        # Rapport humain sur stderr (laisse stdout propre pour le JSON).
        print(render_human_report(report), file=sys.stderr)

    return 0


if __name__ == "__main__":
    sys.exit(main())