#!/usr/bin/env python3
"""Strip fabricated text/PNG outputs from quantbook.ipynb notebooks (cf #6891, Side A).

Pourquoi cet outil existe
-------------------------
Le detecteur `detect_fabricated_outputs.py` (axe 2, registre #3801) identifie
les cellules code dont les `outputs` contiennent des placeholders fabriques
(`Row N`) ou des dataframes backtest-entierement-a-0.0. Pour les 8 quantbooks
QuantConnect de #6891 (AllWeather / DualMomentum / FuturesTrend / TurnOfMonth /
RiskParity / MomentumStrategy / SectorMomentum / EMA-Cross-Alpha), ces sorties
sont de la **fabrication documentee** -- le code source de la cellule ne peut
pas les avoir produites (def pure, plt.subplots sans show, etc.).

Action legitime scope quantbook QC (exception explicite a secrets-hygiene regle
6 "JAMAIS hand-editer une SORTIE de cellule") parce que :

  1. Les quantbooks QC utilisent l'API QuantBook() (qb.add_equity, qb.history)
     non-executable via Papermill local (cf [[feedback-qc-cloud-exec-modalities]]).
  2. Le moteur d'execution canonique = QC Cloud research kernel.
  3. La fabrication = placeholder commited pour faire croire a un resultat de
     backtest qui n'a pas eu lieu, ce qui EST la violation C.2 qu'on Stop&Repair.

L'outil :

  - REUTILISE `detect_fabricated_outputs.detect_cell()` (single source of truth)
  - PRESCORE le SOURCE de la cellule intact (jamais de modification du code)
  - VIDE les `outputs` des cellules flaggees + met `execution_count` a null
  - INSERE une cellule markdown **apres** la cellule strippee (ne modifie pas
    la numerotation des cellules suivantes en inseree AVANT)
  - DRY-RUN par defaut (--apply pour commiter le strip)

Ce qu'il NE FAIT PAS
--------------------
- NE MODIFIE PAS le source des cellules (Stop&Repair : corriger la cause = le
  detecteur a deja signale la fabrication, et la vraie correction = re-executer
  dans QC Cloud -- voir Side B planifie, hors scope ce PR).
- NE TOUCHE PAS aux notebooks non-QuantBook (la fabrication peut etre un faux
  positif pedagogique, on laisse l'auteur corriger).
- NE SCRUBBE PAS les notebooks `.ipynb` non-quantbook (cf exceptions explicites
  dans secrets-hygiene rule 6 : quantbooks QC + metadata.papermill basename).

Usage
-----
    python strip_fabricated_quantbook_outputs.py --list                       # liste les 8 quantbooks cibles
    python strip_fabricated_quantbook_outputs.py --check                      # dry-run + rapport JSON (axe 2 only)
    python strip_fabricated_quantbook_outputs.py --check --include-blank-png  # dry-run + axe 1 blank PNG aussi
    python strip_fabricated_quantbook_outputs.py --apply --include-blank-png  # strip effectif + insertion markdown
    python strip_fabricated_quantbook_outputs.py --nb DualMomentum --apply   # un seul notebook

Sortie stdout (--check) : tableau par notebook (kernel, n cells flagged, n cells will be stripped,
cells indexes) pour audit. Sortie stderr : warning si 0 quantbook trouve.

Lien
----
Issue: https://github.com/jsboige/CoursIA/issues/6891
Detector: scripts/notebook_tools/detect_fabricated_outputs.py (axe 2 sibling)
PR initial: split du strip par notebook = 1 PR par quantbook (R3 strict).
PR groupé : 8 quantbooks = 1 PR (R3 atomicite = 1 type d'action = strip).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Permettre l'import du détecteur sibling (meme dossier).
sys.path.insert(0, str(Path(__file__).resolve().parent))

import detect_fabricated_outputs as detector  # noqa: E402

# Les 8 quantbooks cibles de #6891 (cf body issue, distribution documentee).
# EMA-Cross-Alpha est inclus bien que le detecteur ne le flag pas (il porte un
# blank PNG 96 bytes -- couvert par detect_blank_figures axe 1, pas par ce
# detecteur-ci). Pour coherence du strip on le traite separement via
# --include-blank-png (desactive par defaut, le blank PNG est gere par axe 1).
DEFAULT_TARGETS = [
    "AllWeather",
    "DualMomentum",
    "FuturesTrend",
    "TurnOfMonth",
    "RiskParity",
    "MomentumStrategy",
    "SectorMomentum",
    "EMA-Cross-Alpha",
]


def _resolve_quantbook_paths(
    repo_root: Path,
    targets: list[str],
    family: str = "QuantConnect",
) -> list[Path]:
    """Resolve <repo>/MyIA.AI.Notebooks/<family>/projects/<target>/quantbook.ipynb."""
    base = repo_root / "MyIA.AI.Notebooks" / family / "projects"
    out: list[Path] = []
    missing: list[str] = []
    for t in targets:
        p = base / t / "quantbook.ipynb"
        if not p.exists():
            missing.append(str(p))
            continue
        out.append(p)
    if missing:
        print(
            f"[WARN] {len(missing)} target(s) not found: {missing}",
            file=sys.stderr,
        )
    return out


def _strip_cell_outputs(cell: dict) -> bool:
    """Vide outputs/execution_count d'une cellule code. Retourne True si modifie.

    Preserve : source, metadata, cell_type. Modifie : outputs -> [], execution_count -> None.
    """
    if cell.get("cell_type") != "code":
        return False
    changed = False
    if cell.get("outputs"):
        cell["outputs"] = []
        changed = True
    if cell.get("execution_count") is not None:
        cell["execution_count"] = None
        changed = True
    return changed


def _make_warning_cell(note: str) -> dict:
    """Construit la cellule markdown d'avertissement inseree APRES le strip.

    Format volontairement compact pour minimiser le churn visuel du diff.
    Format FR (conformite readme-french-first).
    """
    return {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            f"> **Sortie strippee** (FABRICATED `Row N` / blank PNG). "
            f"Re-execution QC Cloud recherche kernel requise -- see {note}.\n",
            "> "
            "Code preserve pour tracabilite. "
            "Side A = strip honnete, Side B = re-execution (hors scope ce PR).\n",
        ],
    }


# Seuil blank PNG (axe 1 sibling `detect_blank_figures.py`) -- un image/png
# de moins de 200 bytes = matplotlib figure vide, signature canonique d'un
# plot qui n'a pas eu lieu. Permet de couvrir EMA-Cross-Alpha cell [17] (96b).
BLANK_PNG_THRESHOLD = 200


def _has_blank_png(cell: dict) -> bool:
    """True si la cellule contient une sortie image/png < BLANK_PNG_THRESHOLD bytes."""
    for out in cell.get("outputs", []) or []:
        if not isinstance(out, dict):
            continue
        data = out.get("data", {})
        png = data.get("image/png")
        if isinstance(png, str) and len(png) < BLANK_PNG_THRESHOLD:
            return True
    return False


def _plan_strip(nb: dict, include_blank_png: bool = False) -> list[dict]:
    """Identifie les cellules a stripper et les cellules markdown a inserer.

    Par defaut, ne flag que les cellules avec detections `detect_fabricated_outputs`
    (axe 2 : Row N + zero_stats_dataframe). Avec `include_blank_png=True`, on
    inclut aussi les sorties image/png de moins de 200 bytes (axe 1 sibling).

    Retourne une liste de patches, chacun avec :
        cell_index : index de la cellule code flagged (AVANT insertion)
        findings   : liste des findings (detecteur axe 2 + axe 1 eventuel)
        insert_after : True si on doit inserer une cellule markdown apres
    """
    plan = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        findings = detector.detect_cell(cell)
        if include_blank_png and _has_blank_png(cell):
            findings = findings + [{"signal": "blank_png_axe1"}]
        if not findings:
            continue
        # Strip + insert warning
        plan.append({
            "cell_index": ci,
            "findings": findings,
            "insert_warning": True,
        })
    return plan


def _apply_plan(nb: dict, plan: list[dict], note: str) -> dict:
    """Applique le plan : strip + insertion des cellules warning.

    IMPORTANT: on parcourt le plan en ordre DECROISSANT d'index pour eviter que
    l'insertion d'une cellule markdown ne decale les indices suivants.

    Retourne un dict avec : n_stripped, n_inserted, modified (bool).
    """
    n_stripped = 0
    n_inserted = 0
    # Tri decroissant pour stabilite d'index pendant l'insertion.
    plan_sorted = sorted(plan, key=lambda p: p["cell_index"], reverse=True)
    for patch in plan_sorted:
        ci = patch["cell_index"]
        cell = nb["cells"][ci]
        if _strip_cell_outputs(cell):
            n_stripped += 1
        if patch.get("insert_warning"):
            warning = _make_warning_cell(note)
            nb["cells"].insert(ci + 1, warning)
            n_inserted += 1
    return {
        "n_stripped": n_stripped,
        "n_inserted": n_inserted,
        "modified": n_stripped > 0 or n_inserted > 0,
    }


def _summarize_plan(path: Path, nb: dict, plan: list[dict], include_blank_png: bool = False) -> dict:
    """Construit un resume JSON-friendly du plan pour --check."""
    return {
        "path": str(path),
        "kernel": detector._kernel(nb),  # noqa: SLF001 (sibling helper)
        "n_cells_flagged": len(plan),
        "include_blank_png": include_blank_png,
        "cells": [
            {
                "cell_index": p["cell_index"],
                "findings": p["findings"],
            }
            for p in plan
        ],
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--root", default=".", help="Repo root (default: cwd)")
    ap.add_argument(
        "--family", default="QuantConnect",
        help="Family directory under MyIA.AI.Notebooks (default: QuantConnect)",
    )
    ap.add_argument(
        "--nb", action="append", default=None,
        help="Restrict to a single target (can be repeated). Default = 8 quantbooks de #6891.",
    )
    ap.add_argument(
        "--list", action="store_true",
        help="List the 8 target quantbooks paths and exit.",
    )
    ap.add_argument(
        "--check", action="store_true",
        help="Dry-run: print plan JSON summary, do not modify files.",
    )
    ap.add_argument(
        "--apply", action="store_true",
        help="Apply the strip in-place (writes .ipynb back to disk).",
    )
    ap.add_argument(
        "--note", default="#6891",
        help="Reference note inserted in the warning markdown (default: #6891).",
    )
    ap.add_argument(
        "--include-blank-png", action="store_true",
        help="Also flag cells with image/png output < 200 bytes (axe 1 sibling "
             "coverage, e.g. EMA-Cross-Alpha cell [17]).",
    )
    args = ap.parse_args(argv)

    if not (args.check or args.apply or args.list):
        ap.error("specify --check (dry-run) or --apply (write) or --list")

    repo_root = Path(args.root).resolve()
    targets = args.nb if args.nb else DEFAULT_TARGETS

    paths = _resolve_quantbook_paths(repo_root, targets, args.family)
    if not paths:
        print("[ERROR] no quantbook paths resolved -- check --root or --nb", file=sys.stderr)
        return 2

    if args.list:
        for p in paths:
            print(p.relative_to(repo_root))
        return 0

    if args.check:
        report = {
            "issue": args.note,
            "targets": [p.relative_to(repo_root).as_posix() for p in paths],
            "notebooks": [],
        }
        for p in paths:
            try:
                nb = json.loads(p.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                report["notebooks"].append({"path": str(p), "error": str(exc)})
                continue
            plan = _plan_strip(nb, include_blank_png=args.include_blank_png)
            report["notebooks"].append(
                _summarize_plan(p, nb, plan, include_blank_png=args.include_blank_png)
            )
        print(json.dumps(report, indent=2, ensure_ascii=False))
        return 0

    if args.apply:
        total_stripped = 0
        total_inserted = 0
        per_nb = []
        for p in paths:
            try:
                nb = json.loads(p.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                print(f"[ERROR] cannot read {p}: {exc}", file=sys.stderr)
                return 2
            plan = _plan_strip(nb, include_blank_png=args.include_blank_png)
            if not plan:
                per_nb.append({"path": str(p), "modified": False, "n_stripped": 0})
                continue
            result = _apply_plan(nb, plan, args.note)
            total_stripped += result["n_stripped"]
            total_inserted += result["n_inserted"]
            # Re-serialize (UTF-8 no-BOM, indent=1 = format jupyter standard).
            p.write_text(
                json.dumps(nb, indent=1, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            per_nb.append({
                "path": str(p.relative_to(repo_root)),
                "modified": result["modified"],
                "n_stripped": result["n_stripped"],
                "n_inserted": result["n_inserted"],
                "cells_flagged": len(plan),
            })
        print(json.dumps({
            "issue": args.note,
            "total_stripped": total_stripped,
            "total_inserted": total_inserted,
            "per_notebook": per_nb,
        }, indent=2, ensure_ascii=False))
        return 0

    return 1  # pragma: no cover


if __name__ == "__main__":
    sys.exit(main())
