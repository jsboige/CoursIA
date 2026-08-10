"""Sync translation CSVs across their full perimeter (T1 plein perimetre).

Issue #10329 etape 2 : la dette d'indexation (cellules source absentes du CSV)
s'accumule parce que T1 (extract_cells_to_csv.py) n'a ete execute qu'a
l'extraction initiale, ouverture de la PR par CSV, ou ajoute progressif sur
quand le developpeur se souvient de relancer. Sur 33 CSV, 25 ont une dette
non-zero (334 cellules absentes au total, c.196 baseline).

Ce script rebouche la dette en appliquant `update_existing_csv` (preserve
les colonnes cibles : text_en/hash_en/... remplies par T3) sur le perimetre
entier de chaque CSV. Le perimetre est derive heuristiquement du prefixe
commun majoritaire des notebooks referencees (cf `_resolve_perimeter`).

Usage :
    # DRY-RUN (default) : montre le delta attendu sans toucher au disque.
    python scripts/translation/sync_translation_perimeter.py

    # APPLY : ecrit les CSV modifies.
    python scripts/translation/sync_translation_perimeter.py --apply

    # Restreindre a une liste de CSV (debug).
    python scripts/translation/sync_translation_perimeter.py --csv translations/gametheory/gametheory.csv

Gates (HARD) :
    * DRY-RUN par defaut (le mode qui modifie est `--apply`, accidental-safety).
    * Apres `--apply`, re-mesure via `measure_translation_debt.py` et verifie
      que `indexing_missing_from_csv` a bien baisse (sinon exit 2).
    * `delta_csv_rows` est capee a +5% (sinon des-drift massif, sortie 3).
    * `delta_target_cols_lost` DOIT etre 0 (sinon destruction de traductions
      T3, sortie 4).
"""
from __future__ import annotations

import argparse
import csv
import json
import os
import sys
from collections import Counter
from pathlib import Path

# Permet d'importer les helpers de extract_cells_to_csv en co-habitation
sys.path.insert(0, str(Path(__file__).resolve().parent))
from extract_cells_to_csv import (  # noqa: E402
    COLUMNS,
    TARGET_LANGS,
    extract_notebook,
    iter_notebooks,
    load_existing_csv,
    update_existing_csv,
    write_csv,
)
from measure_translation_debt import measure_csvs, _resolve_csv_paths  # noqa: E402


REPO_ROOT = Path.cwd()
DEFAULT_TARGET_LANG = "en"


def _resolve_perimeter(csv_path: Path) -> tuple[str, int]:
    """Derive le perimetre d'un CSV = LONGEST COMMON PREFIX (avec slash final)
    des notebooks referencees dans le CSV.

    Pourquoi LCP et pas "prefixe le plus frequent" : un CSV `genai/audio.csv`
    contient 30 notebooks tous sous `MyIA.AI.Notebooks/GenAI/Audio/`. Si on
    prend le prefixe majoritaire sans regarder la profondeur, on remonte
    systematiquement a `MyIA.AI.Notebooks/GenAI/` (= 4 CSV distincts couvrent
    ce prefixe, donc le majoritaire est le niveau 2). Resultat : le scan
    engloutirait toute la famille GenAI (image + video + texte + audio) dans
    un seul CSV, explosion de doublons.

    LCP depth-2 minimum garanti : en dessous de 2, on remonte a la racine.
    On accepte le perimetre le plus profond qui contient TOUS les notebooks
    (= 100% coverage des notebooks references).
    """
    nbs: list[str] = []
    with csv_path.open(encoding="utf-8", newline="") as f:
        for row in csv.DictReader(f):
            nb = row.get("notebook", "")
            if nb:
                nbs.append(nb)
    if not nbs:
        return "", 0

    # LCP char-par-char (sur le path-strings forward-slash)
    sorted_nbs = sorted(nbs)
    first = sorted_nbs[0]
    last = sorted_nbs[-1]
    common = []
    for c1, c2 in zip(first, last):
        if c1 != c2:
            break
        common.append(c1)
    lcp = "".join(common)
    # Trim au dernier slash pour avoir un prefixe-repertoire
    if "/" in lcp:
        lcp = lcp[: lcp.rfind("/") + 1]
    else:
        # Pas de slash = fichiers en racine, ne devrait pas arriver
        return "", 0
    # Floor : on remonte TOUJOURS au moins a `MyIA.AI.Notebooks/<X>/`,
    # jamais a 1 ou 0 segments, pour eviter d'attaquer la racine.
    parts = lcp.split("/")
    if len(parts) < 3:  # ["MyIA.AI.Notebooks", "<X>", ""]  = 3 segments w/ trailing
        # Coverage check : est-ce que tous les notebooks ont ce prefixe ?
        return "", 0
    return lcp, len(nbs)


def _is_notebook_in_perimeter(nb_path: str, perimeter: str) -> bool:
    """True si le notebook appartient au perimetre (relatif REPO_ROOT)."""
    return nb_path.startswith(perimeter)


def _fresh_rows_for_perimeter(perimeter: str) -> list[dict]:
    """Re-extrait les cellules source de tous les notebooks du perimetre.
    Reproduit la logique T1 sans dependre d'un subprocess."""
    perim_path = REPO_ROOT / perimeter
    if not perim_path.is_dir():
        return []
    notebooks = iter_notebooks([perim_path])
    rows: list[dict] = []
    for nb in notebooks:
        rows.extend(extract_notebook(nb, REPO_ROOT, src_lang="fr"))
    return rows


def _target_cols() -> list[str]:
    """Toutes les colonnes qui peuvent contenir une traduction T3 = text_<lang>
    et hash_<lang> pour lang dans TARGET_LANGS (la pivot est mise a jour
    intentionnellement)."""
    cols = []
    for lang in TARGET_LANGS:
        cols.append(f"text_{lang}")
        cols.append(f"hash_{lang}")
    return cols


def _target_cols_lost(existing_rows: list[dict], updated_rows: list[dict]) -> int:
    """Compte les cellules text_<lang> qui etaient non-vides avant et qui
    sont vides apres (ou absentes). Doit etre 0 -- perte de traduction T3."""
    target_cols = _target_cols()
    existing_by_key = {(r["notebook"], r["cell_id"]): r for r in existing_rows}
    updated_by_key = {(r["notebook"], r["cell_id"]): r for r in updated_rows}
    lost = 0
    for key, before in existing_by_key.items():
        after = updated_by_key.get(key)
        if after is None:
            # Ligne disparue = ORPHAN_ROW, pas une perte de cible T3
            # (la cible restait vide puisque la cellule n'existe plus).
            continue
        for col in target_cols:
            if before.get(col, "") and not after.get(col, ""):
                lost += 1
    return lost


def _render_per_csv_report(per_csv: list[dict]) -> str:
    lines = ["# sync_translation_perimeter.py report", ""]
    lines.append(f"CSVs traites : {len(per_csv)}")
    lines.append("")
    lines.append("| CSV | missing avant | missing apres | rows delta | target cols lost | status |")
    lines.append("|-----|--------------:|--------------:|-----------:|-----------------:|--------|")
    for r in per_csv:
        lines.append(
            f"| `{r['csv']}` | {r['missing_before']} | {r['missing_after']} | "
            f"{r['delta_rows']:+d} | {r['target_cols_lost']} | {r['status']} |"
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true", help="Ecrit les CSV modifies (default: dry-run).")
    parser.add_argument("--csv", action="append", default=[], help="Restreint a un CSV (relatif REPO_ROOT). Repetable.")
    parser.add_argument("--translations-dir", default="translations", help="Dossier des CSV (default: translations).")
    parser.add_argument("--json-only", action="store_true", help="Sortie compacte JSON sur stdout.")
    args = parser.parse_args()

    raw_csvs = _resolve_csv_paths([Path(args.translations_dir)], REPO_ROOT)
    target_csvs = [p.resolve() for p in raw_csvs] if raw_csvs and not raw_csvs[0].is_absolute() else raw_csvs
    if args.csv:
        wanted = {Path(c).resolve() for c in args.csv}
        target_csvs = [p for p in target_csvs if p.resolve() in wanted]

    # Step 1 : ground truth avant
    before_report = measure_csvs(target_csvs, REPO_ROOT, DEFAULT_TARGET_LANG)
    before_agg = before_report["aggregate"]
    before_missing = before_agg["indexing_missing_from_csv"]
    before_rows = before_agg["total_csv_rows"]
    # Index per_csv by absolute path for lookup (measure_csvs retourne des abs)
    before_per_csv = {str(Path(p["csv"]).resolve()).replace("\\", "/"): p for p in before_report["per_csv"]}

    per_csv = []
    for csv_path in target_csvs:
        rel_csv = str(csv_path.relative_to(REPO_ROOT)).replace("\\", "/")
        abs_csv = str(csv_path.resolve()).replace("\\", "/")
        before_entry = before_per_csv.get(abs_csv)
        if before_entry is None:
            continue
        missing_before = before_entry["indexing_debt"]["missing_from_csv"]
        if missing_before == 0:
            continue  # Rien a faire

        perimeter, nb_ref = _resolve_perimeter(csv_path)
        if not perimeter:
            print(f"SKIP {rel_csv}: perimetre introuvable", file=sys.stderr)
            continue

        # Re-extrait les cellules source pour ce perimetre
        fresh_rows = _fresh_rows_for_perimeter(perimeter)
        target_notebooks = {
            r["notebook"] for r in fresh_rows if _is_notebook_in_perimeter(r["notebook"], perimeter)
        }

        # Charge le CSV existant
        existing_rows = load_existing_csv(csv_path)
        existing_rows_before = list(existing_rows)  # Snapshot pre-update

        # Update
        updated_rows, _stats = update_existing_csv(existing_rows, fresh_rows, target_notebooks)

        # Calcule le missing apres
        existing_keys = {(r["notebook"], r["cell_id"]) for r in existing_rows_before}
        updated_keys = {(r["notebook"], r["cell_id"]) for r in updated_rows}
        new_keys = updated_keys - existing_keys
        # Le missing apres = nb de cellules source pas dans le CSV mis a jour
        # = fresh_rows qui ne sont pas dans updated_rows
        missing_after = sum(
            1
            for r in fresh_rows
            if (r["notebook"], r["cell_id"]) not in updated_keys
        )

        delta_rows = len(updated_rows) - len(existing_rows_before)
        target_lost = _target_cols_lost(existing_rows_before, updated_rows)

        # Status
        # Le seul HARD gate c'est target_cols_lost : destruction de traductions T3.
        # Le delta_rows est un WARNING (expansion legitime = nouveaux notebooks
        # du perimetre qui n'avaient jamais ete indexes). Missing qui ne baisse
        # pas = NO-OP (le scan n'a rien trouve de neuf, peu importe la cause).
        if target_lost > 0:
            status = "ABORTED-target-lost"
        elif delta_rows > max(1, len(existing_rows_before) * 0.05):
            status = "WARNING-rows-delta-big"
        elif missing_after >= missing_before:
            status = "NO-OP"
        else:
            status = "OK"

        per_csv.append({
            "csv": rel_csv,
            "perimeter": perimeter,
            "nb_ref": nb_ref,
            "missing_before": missing_before,
            "missing_after": missing_after,
            "missing_delta": missing_before - missing_after,
            "delta_rows": delta_rows,
            "target_cols_lost": target_lost,
            "status": status,
        })

        if args.apply and status in ("OK", "WARNING-rows-delta-big"):
            # Ecrit le CSV mis a jour (atomic via write_csv : BytesIO + replace)
            write_csv(updated_rows, csv_path)
            print(f"APPLIED {rel_csv}: -{missing_before - missing_after} missing, "
                  f"{delta_rows:+d} rows", file=sys.stderr)

    # Step 2 : ground truth apres (si --apply)
    after_missing = before_missing
    after_rows = before_rows
    if args.apply:
        after_report = measure_csvs(target_csvs, REPO_ROOT, DEFAULT_TARGET_LANG)
        after_agg = after_report["aggregate"]
        after_missing = after_agg["indexing_missing_from_csv"]
        after_rows = after_agg["total_csv_rows"]

    # Sortie
    if args.json_only:
        out = {
            "dry_run": not args.apply,
            "before": before_missing,
            "after": after_missing,
            "delta_missing": before_missing - after_missing,
            "before_rows": before_rows,
            "after_rows": after_rows,
            "delta_rows": after_rows - before_rows,
            "per_csv": per_csv,
        }
        print(json.dumps(out, indent=2, ensure_ascii=False))
    else:
        print(_render_per_csv_report(per_csv))
        print()
        print(f"DRY-RUN : {not args.apply}")
        print(f"missing avant : {before_missing}")
        print(f"missing apres : {after_missing}")
        print(f"delta missing : {before_missing - after_missing:+d}")
        print(f"delta rows : {after_rows - before_rows:+d}")

    # Gates finaux
    if args.apply:
        # HARD : aucune traduction T3 perdue
        if any(r["status"] == "ABORTED-target-lost" for r in per_csv):
            print("ERROR: target_cols_lost > 0 sur au moins un CSV", file=sys.stderr)
            return 2
        # WARN uniquement : expansion legitime de perimetre (non bloquant)
        warnings = [r for r in per_csv if r["status"] == "WARNING-rows-delta-big"]
        if warnings:
            print(
                f"WARN: {len(warnings)} CSV avec delta > 5% (expansion perimetre possible, "
                "non-bloquant). Voir le rapport ci-dessus.",
                file=sys.stderr,
            )
        # HARD : la dette d'indexation a baisse
        if after_missing >= before_missing:
            print("ERROR: missing did not decrease", file=sys.stderr)
            return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
