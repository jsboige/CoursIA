#!/usr/bin/env python3
"""Detect translation drift between notebooks and the sync CSV (Epic #4957 / #1650).

Implements the T2 deliverable of issue #4957 : un script NON-BLOQUANT qui detecte
quand un notebook source ou une de ses traductions est desynchronise du CSV
maintenu par `extract_cells_to_csv.py` (T1). Concu pour tourner en CI
(`.github/workflows/translation-drift.yml`) a la maniere de `catalog-drift.yml` :
read-only, signale sous forme de rapport + annotation, n'ecrit jamais sur la branche.

Verdicts par ligne CSV (cf. #4957 §2) :

    IN_SYNC      src_hash et hash_<lang> matchent les notebooks courants
    SRC_DRIFT    le notebook source a bouge depuis la derniere synchro
                 (current src hash != CSV src_hash) -> retraduction requise
    TRAD_DRIFT   une traduction a ete editee a la main sans repercussion
                 (current <lang> hash != CSV hash_<lang>)
    MISSING_LANG le notebook xxx_<lang>.ipynb n'existe plus alors qu'un hash
                 etait depose dans le CSV
    ORPHAN_ROW   la ligne CSV reference un cell_id absent du notebook source
                 (cellule supprimee)

En phase POC (T1, seule la colonne pivot est remplie), le script ne remonte
que du SRC_DRIFT eventuel ; l'absence de traductions deposees n'est pas un drift
(c'est l'etat attendu pre-T3).

Usage :
    python scripts/translation/check_translation_sync.py translations/<famille>/<serie>.csv
    python scripts/translation/check_translation_sync.py translations/   # tous les CSV
    python scripts/translation/check_translation_sync.py translations/ --check   # exit 0 toujours (CI)

Sortie : rapport lisible sur stderr + JSON sur stdout (consommable par la CI).
Exit code : 0 si --check (non-bloquant), sinon 1 si un drift detecte.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from pathlib import Path

# Doit rester coherent avec extract_cells_to_csv.py (T1).
PIVOT_LANG = "fr"
TARGET_LANGS = ["en", "es", "ar", "fa", "zh", "ru", "pt"]
ALL_LANGS = [PIVOT_LANG] + TARGET_LANGS


def normalize(text: str) -> str:
    """Meme normalisation que extract_cells_to_csv.py (anti faux-drift cosmétique)."""
    lines = [line.rstrip() for line in text.splitlines()]
    return "\n".join(lines).strip("\n")


def cell_hash(text: str) -> str:
    return hashlib.sha256(normalize(text).encode("utf-8")).hexdigest()[:16]


def load_notebook_cells(nb_path: Path) -> dict[str, str] | None:
    """Retourne {cell_id: hash} pour un notebook, ou None si illisible."""
    try:
        import json as _json

        nb = _json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    cells: dict[str, str] = {}
    for cell in nb.get("cells", []):
        cid = cell.get("id")
        if not cid or cell.get("cell_type") not in ("markdown", "code"):
            continue
        cells[cid] = cell_hash("".join(cell.get("source", [])))
    return cells


def translated_notebook_path(source_path: str, lang: str, repo_root: Path) -> Path:
    """`dir/foo.ipynb` + lang `en` -> `dir/foo_en.ipynb` (#1650 convention notebooks)."""
    p = repo_root / source_path
    return p.with_name(p.stem + f"_{lang}.ipynb")


def check_csv(csv_path: Path, repo_root: Path) -> list[dict]:
    """Verifie un CSV de synchro contre les notebooks courants. Retourne les anomalies."""
    anomalies: list[dict] = []
    with csv_path.open(encoding="utf-8") as f:
        reader = csv.DictReader(f)
        source_cache: dict[str, dict[str, str] | None] = {}
        for row in reader:
            nb_rel = row.get("notebook", "")
            cell_id = row.get("cell_id", "")
            if not nb_rel or not cell_id:
                continue

            # Notebook source (cache par chemin).
            if nb_rel not in source_cache:
                source_cache[nb_rel] = load_notebook_cells(repo_root / nb_rel)
            src_cells = source_cache[nb_rel]
            if src_cells is None:
                anomalies.append(
                    {"csv": str(csv_path), "notebook": nb_rel, "cell_id": cell_id,
                     "verdict": "ORPHAN_ROW", "detail": "notebook source illisible/absent"}
                )
                continue
            if cell_id not in src_cells:
                anomalies.append(
                    {"csv": str(csv_path), "notebook": nb_rel, "cell_id": cell_id,
                     "verdict": "ORPHAN_ROW", "detail": "cell_id absent du notebook source (cellule supprimée)"}
                )
                continue

            # SRC_DRIFT : le source a-t-il bougé depuis la dernière synchro ?
            current_src = src_cells[cell_id]
            csv_src_hash = row.get("src_hash", "")
            if csv_src_hash and current_src != csv_src_hash:
                anomalies.append(
                    {"csv": str(csv_path), "notebook": nb_rel, "cell_id": cell_id,
                     "verdict": "SRC_DRIFT",
                     "detail": f"source modifié (csv={csv_src_hash} <> actuel={current_src}) -> retraduction requise"}
                )

            # TRAD_DRIFT / MISSING_LANG par langue cible.
            # Le pivot (fr) EST le notebook source (xxx.ipynb, pas xxx_fr.ipynb) :
            # sa cohérence est déjà vérifiée par SRC_DRIFT ci-dessus -> on le skippe.
            for lang in TARGET_LANGS:
                csv_hash = row.get(f"hash_{lang}", "")
                if not csv_hash:
                    continue  # rien déposé = attendu pre-T3, pas un drift.
                trad_path = translated_notebook_path(nb_rel, lang, repo_root)
                if not trad_path.exists():
                    anomalies.append(
                        {"csv": str(csv_path), "notebook": nb_rel, "cell_id": cell_id, "lang": lang,
                         "verdict": "MISSING_LANG",
                         "detail": f"{trad_path.name} absent alors qu'un hash était déposé"}
                    )
                    continue
                trad_cells = load_notebook_cells(trad_path)
                if trad_cells is None or cell_id not in trad_cells:
                    anomalies.append(
                        {"csv": str(csv_path), "notebook": nb_rel, "cell_id": cell_id, "lang": lang,
                         "verdict": "MISSING_LANG",
                         "detail": f"cell_id {cell_id} absent de {trad_path.name}"}
                    )
                    continue
                if trad_cells[cell_id] != csv_hash:
                    anomalies.append(
                        {"csv": str(csv_path), "notebook": nb_rel, "cell_id": cell_id, "lang": lang,
                         "verdict": "TRAD_DRIFT",
                         "detail": f"traduction {lang} éditée (csv={csv_hash} <> actuel={trad_cells[cell_id]})"}
                    )
    return anomalies


def iter_csvs(target: Path) -> list[Path]:
    if target.is_file():
        return [target]
    return sorted(target.rglob("*.csv"))


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Détecte le drift de traduction vs le CSV de synchro (non-bloquant, #4957 T2)."
    )
    parser.add_argument("input", type=Path, help="Fichier CSV ou répertoire `translations/`.")
    parser.add_argument(
        "--repo-root", type=Path, default=None, help="Racine du dépôt (défaut : cwd)."
    )
    parser.add_argument(
        "--check", action="store_true",
        help="Mode CI non-bloquant : exit 0 même si drift détecté (le rapport va sur stderr/JSON).",
    )
    args = parser.parse_args()

    if not args.input.exists():
        print(f"ERROR : {args.input} introuvable.", file=sys.stderr)
        return 2

    repo_root = (args.repo_root or Path.cwd()).resolve()
    csvs = iter_csvs(args.input)
    if not csvs:
        # Pas de CSV = phase pre-T1, rien a verifier. CI verte.
        print(f"INFO : aucun CSV sous {args.input} (phase pre-T1). Rien à vérifier.", file=sys.stderr)
        print(json.dumps({"csvs_checked": 0, "anomalies": [], "anomaly_count": 0}))
        return 0

    all_anomalies: list[dict] = []
    for csv_path in csvs:
        all_anomalies.extend(check_csv(csv_path, repo_root))

    # Rapport lisible (stderr) + JSON (stdout, consommable CI).
    report = {
        "csvs_checked": len(csvs),
        "anomalies": all_anomalies,
        "anomaly_count": len(all_anomalies),
    }
    print(json.dumps(report, ensure_ascii=False, indent=2))

    if not all_anomalies:
        print(f"OK : {len(csvs)} CSV vérifié(s), 0 drift.", file=sys.stderr)
        return 0

    # Regroupement par verdict pour le rapport stderr.
    from collections import Counter

    by_verdict = Counter(a["verdict"] for a in all_anomalies)
    summary = ", ".join(f"{v}={n}" for v, n in by_verdict.items())
    print(f"DRIFT DETECTE ({len(all_anomalies)} anomalie(s) sur {len(csvs)} CSV) : {summary}", file=sys.stderr)
    for a in all_anomalies[:20]:
        print(
            f"  [{a['verdict']}] {a.get('notebook', '?')} cell={a.get('cell_id', '?')[:10]}"
            f"{(' lang=' + a['lang']) if 'lang' in a else ''} : {a['detail']}",
            file=sys.stderr,
        )
    if len(all_anomalies) > 20:
        print(f"  ... et {len(all_anomalies) - 20} autres (voir JSON stdout).", file=sys.stderr)

    return 0 if args.check else 1


if __name__ == "__main__":
    sys.exit(main())
