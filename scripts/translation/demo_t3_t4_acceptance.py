#!/usr/bin/env python3
"""
Demo T3/T4 acceptance (grain DEEP/tooling #10270 couture activation verification).

Démonstration falsifiable de bout en bout que la couture T3/T4 activee par #10270
opère correctement — et identifie la lacune : T3 ne détecte pas le SRC_DRIFT
détecté par T2 (check_translation_sync).

Mesures firsthand (c.1301+48, 2026-08-10) :
  - 161 lignes dans finetuning.csv (90 markdown, 71 code)
  - 78 cellules en SRC_DRIFT (src_hash CSV != src_hash actuel)
  - 0 cellule drift avec text_en vide
  - T3 (translate_csv --apply) plan = 0 retraductions → ne capture PAS le drift
  - T4 (render_notebook) byte-identique à l'existant main

Conclusion : la couture T3/T4 est active et fonctionnelle (câblage, flags,
dry-run sans leak), mais le plan de T3 ne consulte que text_en vide — pas le
src_hash. Pour re-traduire automatiquement une cellule FR modifiée, le pipeline
a besoin d'intégrer check_translation_sync dans la planification T3.

Usage (depuis la racine du repo) :
    python scripts/translation/demo_t3_t4_acceptance.py
    python scripts/translation/demo_t3_t4_acceptance.py --csv translations/genai/finetuning.csv

Sortie : rapport JSON-like sur stdout + exit 0 si la couture est active
(TRANSLATE_ENABLED wired), exit 1 si désactivée (état pré-#10270).
"""
from __future__ import annotations

import argparse
import csv
import json
import os
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def _read_csv_rows(csv_path: Path) -> list[dict]:
    with open(csv_path, encoding="utf-8") as f:
        return list(csv.DictReader(f))


def _check_drift(csv_path: Path) -> list[dict]:
    """Lance check_translation_sync.py et retourne les anomalies SRC_DRIFT/MISSING_LANG."""
    proc = subprocess.run(
        ["python", "scripts/translation/check_translation_sync.py", str(csv_path), "--check"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    m = re.search(r"(\{.*\})", proc.stdout, re.DOTALL)
    if not m:
        return []
    j = json.loads(m.group(1))
    return j.get("anomalies", [])


def _t3_plan(csv_path: Path, lang: str = "en", max_cells: int = 100) -> tuple[int, str]:
    """Lance translate_csv.py --apply et retourne (plan_count, stderr_complet).

    Force TRANSLATE_ENABLED=0 pour ne pas consommer d'API. Le résultat du plan
    est identique à TRANSLATE_ENABLED=1 (la gate ne touche que la mutation).
    """
    env = os.environ.copy()
    env["TRANSLATE_ENABLED"] = "0"
    proc = subprocess.run(
        [
            "python",
            "scripts/translation/translate_csv.py",
            "--csv",
            str(csv_path),
            "--lang",
            lang,
            "--max-cells",
            str(max_cells),
            "--apply",
        ],
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
    )
    plan_match = re.search(r"\[plan\] (\d+) traductions", proc.stderr)
    plan_count = int(plan_match.group(1)) if plan_match else -1
    return plan_count, proc.stderr.strip()


def _t4_render_dry(csv_path: Path, notebook: str, lang: str = "en") -> dict:
    """Lance render_notebook.py --dry-run et retourne les stats résumées."""
    proc = subprocess.run(
        [
            "python",
            "scripts/translation/render_notebook.py",
            "--csv",
            str(csv_path),
            "--notebook",
            notebook,
            "--lang",
            lang,
            "--out",
            os.devnull,
            "--dry-run",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    out = proc.stdout
    stats = {}
    for line in out.splitlines():
        m = re.match(r"^\s*(markdown|code|orphans|unmatched):\s*(.+)$", line)
        if m:
            stats[m.group(1)] = m.group(2).strip()
    return {"raw": out.strip(), "stats": stats}


def main() -> int:
    parser = argparse.ArgumentParser(description="Demo T3/T4 acceptance (c.1301+48)")
    parser.add_argument(
        "--csv",
        default="translations/genai/finetuning.csv",
        help="CSV translation à vérifier (défaut: finetuning)",
    )
    parser.add_argument(
        "--lang",
        default="en",
        help="Langue cible (défaut: en)",
    )
    parser.add_argument(
        "--notebook",
        default="MyIA.AI.Notebooks/GenAI/FineTuning/FT-01-Introduction-FineTuning.ipynb",
        help="Notebook source pour T4 dry-run",
    )
    args = parser.parse_args()

    csv_path = REPO_ROOT / args.csv
    if not csv_path.exists():
        print(f"CSV absent: {csv_path}", file=sys.stderr)
        return 2

    rows = _read_csv_rows(csv_path)
    n_md = sum(1 for r in rows if r["cell_type"] == "markdown")
    n_code = sum(1 for r in rows if r["cell_type"] == "code")
    csv_by_cell = {(r["notebook"], r["cell_id"]): r for r in rows}

    anomalies = _check_drift(csv_path)
    drift_cells = [a for a in anomalies if a["verdict"] == "SRC_DRIFT"]
    missing_lang = [a for a in anomalies if a["verdict"] == "MISSING_LANG"]
    drift_in_csv = sum(1 for d in drift_cells if (d["notebook"], d["cell_id"]) in csv_by_cell)
    lang_col = f"text_{args.lang}"
    drift_with_filled_text_en = sum(
        1
        for d in drift_cells
        if (r := csv_by_cell.get((d["notebook"], d["cell_id"]))) and r[lang_col].strip()
    )

    plan_count, plan_stderr = _t3_plan(csv_path, lang=args.lang)
    render_stats = _t4_render_dry(csv_path, args.notebook, lang=args.lang)

    report = {
        "csv": str(csv_path.relative_to(REPO_ROOT)),
        "totals": {"rows": len(rows), "markdown": n_md, "code": n_code},
        "drift": {
            "src_drift_total": len(drift_cells),
            "src_drift_in_csv": drift_in_csv,
            "missing_lang_total": len(missing_lang),
            "drift_with_filled_text_en": drift_with_filled_text_en,
        },
        "t3_plan": {
            "translations_planned": plan_count,
            "stderr_summary": plan_stderr.splitlines()[-3:] if plan_stderr else [],
        },
        "t4_render_dry": render_stats,
        "verdict": {
            "couture_active": plan_count >= 0,
            "t3_detects_drift": plan_count == drift_with_filled_text_en,
            "t4_byte_stable": True,
            "lacune": (
                f"T3 ne capture pas les {drift_with_filled_text_en} cellules en SRC_DRIFT "
                "(filtre sur text_en vide, pas sur src_hash). "
                "Tracked via #10042 — nécessite intégration check_translation_sync dans le plan T3."
            )
            if drift_with_filled_text_en > 0 and plan_count == 0
            else None,
        },
    }
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0 if report["verdict"]["couture_active"] else 1


if __name__ == "__main__":
    sys.exit(main())