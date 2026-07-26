#!/usr/bin/env python3
"""
populate_cost_metadata.py — Peuple `nb.metadata['cost']` pour les notebooks sans matrice de coût.

Issue #8056 — matrice coût/ressource par notebook. Issue #8587 (MERGED) a ajouté le
champ `qcc_tokens_est` au schema + validator (Litmus 7) + tests. Ce qui reste :
~69 notebooks QuantConnect (QuantBook) SANS aucune `metadata.cost` — donc présentés
comme « gratuits » (Litmus 7 flag). Les 10 PR de migration précédentes (#8418..#8585)
étaient des hand-edits par notebook ; ce script déterministe clôt le gap en une passe.

But : pour chaque notebook QuantConnect utilisant `QuantBook()` et dépourvu de
`metadata['cost']`, insérer le bloc de coût canonique (profile `quantbook`) dérivé :
  - `qcc_tokens_est` via l'heuristic documentée `max(400, n_code_cells × 70)`
    (cf docs/notebook-metadata/cost-matrix.md §"Coût QCC / QuantConnect", #8056)
  - les champs obligatoires (schema cost-matrix.md) aux valeurs de consensus des
    13 quantbooks déjà migrés (#8585) ou aux défauts du schema
  - `null` pour les champs notebook-specific (`reduced_pedagogical`,
    `free_alternative`) qui exigent un jugement humain — jamais fabriqués

Idempotent : JAMAIS écrase un bloc `cost` existant (un notebook déjà peuplé est
skippé). Litmus anti-LIGHT : ce script APPLIQUE une transformation documentée et
déterministe ; le verdict final (la metadata est-elle *juste* ?) = revue humaine.
Cf `check_cost_metadata.py` (le vérificateur), `docs/notebook-metadata/cost-matrix.md`.

Usage :
  # Audit (dry-run) — liste ce qui serait peuplé, n'écrit rien
  python scripts/audit/populate_cost_metadata.py <notebook-ou-dossier>.ipynb --profile quantbook

  # Appliquer
  python scripts/audit/populate_cost_metadata.py <notebook-ou-dossier> --profile quantbook \\
      --by myia-po-2024:CoursIA-2 --apply
"""

import argparse
import datetime as _dt
import json
import re
import sys
from pathlib import Path


QUANTBOOK_RE = re.compile(r"QuantBook\(\)|self\.QuantBook")

# Champ obligatoires + defaults pour le profile `quantbook`.
# Valeurs : consensus des 13 quantbooks migrés (#8585) > défaut schema (cost-matrix.md
# §mandatory) > null honest pour les champs notebook-specific.
# NOTE doc-vs-practice : le template doc (cost-matrix.md §"QC / QuantConnect") montre
# `api_provider: qc_cloud` / `external_account: qc`, mais la PRATIQUE migrée (13/13)
# utilise `api_provider: none` / `external_account: quantconnect-organization`. On suit
# la pratique migrée (consistance intra-famille QC) ; l'écart est documenté ici, pas caché.


def _count_code_cells(nb: dict) -> int:
    """Nombre de cellules code non-vides (source non-whitespace)."""
    n = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        if src.strip():
            n += 1
    return n


def _uses_quantbook(nb: dict) -> bool:
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        if QUANTBOOK_RE.search("".join(cell.get("source", []))):
            return True
    return False


def qcc_tokens_estimate(n_code_cells: int) -> int:
    """Heuristic QCC documentée (cost-matrix.md §"Coût QCC / QuantConnect", #8056) :
    ~70 QCC par cellule code, plancher 400. Estimation (suffixe `_est`), pas mesure."""
    return max(400, n_code_cells * 70)


def build_quantbook_cost(nb: dict, by: str, today: str) -> dict:
    """Construit le bloc `metadata['cost']` canonique pour un quantbook.

    Champs dérivés : `qcc_tokens_est` (heuristic), `last_validated` (date de création
    de la metadata — pas date d'exécution QC Cloud ; `validator: qc_cloud` nomme la
    MÉTHODE canonique de validation, pas une exécution récente).
    Champs notebook-specific (`reduced_pedagogical`, `free_alternative`) : null
    (jugement humain ; QuantBook = QC uniquement → pas d'alternative locale).
    """
    n_code = _count_code_cells(nb)
    return {
        "api_usd_est": 0.0,  # QCC = quota non-USD (schema default 0)
        "api_provider": "none",  # 13/13 migrés ; schema default "none"
        "qcc_tokens_est": qcc_tokens_estimate(n_code),  # heuristic max(400, n×70)
        "cpu_min": 0,  # QC s'exécute sur le cloud (QCC) ; CPU local = 0 (schema default)
        "gpu_required": False,  # quantbook de recherche, pas de GPU local
        "network": True,  # API QuantConnect obligatoire (HTTPS) (13/13 migrés)
        "external_account": "quantconnect-organization",  # 12/13 migrés (QC user + token)
        "free_alternative": None,  # QuantBook = QC uniquement, pas d'alternative locale
        "reduced_pedagogical": None,  # notebook-specific (jugement humain) ; null = honnête
        "reproducibility": "MED",  # single-run backtest stochastique (doc template)
        "last_validated": today,  # date d'établissement de la metadata (script)
        "validator": "qc_cloud",  # Litmus 5 : qc_cloud pour QuantBook (13/13)
    }


def populate_notebook(path: Path, by: str, today: str, apply: bool) -> str:
    """Peuple metadata.cost si QuantBook + absent. Retourne un code statut.

    Returns: 'populated' | 'skipped-has-cost' | 'skipped-no-quantbook' | 'error'.
    """
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        return f"error: {e}"

    if not _uses_quantbook(nb):
        return "skipped-no-quantbook"

    meta = nb.setdefault("metadata", {})
    if "cost" in meta:  # idempotent : ne JAMAIS écraser un bloc existant
        return "skipped-has-cost"

    cost = build_quantbook_cost(nb, by=by, today=today)
    if not apply:
        return "populated"  # dry-run : on rapporte, on n'écrit pas

    meta["cost"] = cost
    # Round-trip json indent=1 (convention repo) ; LF-only ; pas de churn inutile.
    path.write_text(
        json.dumps(nb, indent=1, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return "populated"


def iter_notebooks(target: Path):
    """Énumère les .ipynb sous target (fichier unique ou dossier récursif),
    en excluant _output.ipynb, .ipynb_checkpoints/, /backtests/."""
    if target.is_file():
        yield target
        return
    for p in sorted(target.rglob("*.ipynb")):
        s = str(p).replace("\\", "/")
        if "_output" in p.name:
            continue
        if ".ipynb_checkpoints" in s:
            continue
        if "/backtests/" in s:
            continue
        yield p


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("target", type=Path, help="Notebook .ipynb ou dossier à peupler")
    ap.add_argument("--profile", choices=["quantbook"], default="quantbook",
                    help="Profile de coût (seul 'quantbook' est implémenté)")
    ap.add_argument("--by", default="anonymous",
                    help="machine:workspace (provenance, pour le rapport)")
    ap.add_argument("--apply", action="store_true",
                    help="Écrire les modifications (défaut : dry-run)")
    ap.add_argument("--today", default=None,
                    help="Date ISO pour last_validated (défaut : aujourd'hui)")
    args = ap.parse_args(argv)

    if not args.target.exists():
        print(f"ERROR: {args.target} n'existe pas", file=sys.stderr)
        return 2

    today = args.today or _dt.date.today().isoformat()
    counts = {"populated": 0, "skipped-has-cost": 0, "skipped-no-quantbook": 0}
    errors = []

    for nb_path in iter_notebooks(args.target):
        status = populate_notebook(nb_path, by=args.by, today=today, apply=args.apply)
        if status.startswith("error"):
            errors.append((nb_path, status))
        elif status in counts:
            counts[status] += 1
            if status == "populated":
                print(f"  {'WRITE' if args.apply else 'DRY-RUN'}  {nb_path}")
        else:
            errors.append((nb_path, f"unexpected: {status}"))

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"\n[{mode}] profile={args.profile} by={args.by} today={today}")
    print(f"  populated (QuantBook sans cost) : {counts['populated']}")
    print(f"  skipped-has-cost (déjà peuplé)   : {counts['skipped-has-cost']}")
    print(f"  skipped-no-quantbook             : {counts['skipped-no-quantbook']}")
    if errors:
        print(f"  errors                           : {len(errors)}", file=sys.stderr)
        for p, e in errors:
            print(f"    {p}: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
