#!/usr/bin/env python3
"""Detect Plotly-CDN cells in .ipynb notebooks = blanc en static rendering (cf #6927).

Pourquoi cet outil existe
-------------------------
Le pattern `record PlotlyHtml + Formatter.Register` (canon C548-L2) emet du
Plotly.js via un `<script src="https://cdn.plot.ly/...">` externe. Ce HTML
rend correctement dans un kernel .NET Interactive live (VS Code / Jupyter Lab
avec Internet), MAIS :
- GitHub sandbox et n'execute pas les `<script>` → div vide.
- Offline / nbviewer / CSP strict (artefacts CI) → CDN externe ne charge pas.

Le pendant Python (matplotlib) emet du `image/png` persistant qui rend
partout. Les jumeaux .NET Infer/DecInfer divergent sur ce point (cf #6927).

Ce tool identifie les cellules a risque : celles qui contiennent
`cdn.plot.ly`/`cdn.plotly` dans leur SORTIE (output) **et** n'emet aucune
sortie `image/*` rasterisable → blanc en static rendering.

Sortie : table par notebook avec comptage cells a risque + plan de remediation.

Usage
-----
    python scripts/notebook_tools/check_plotly_static_risk.py [--json] [--root MyIA.AI.Notebooks]
                                                           [--exit-risky-nb N]
                                                           [--fix-plan-out FILE]

Notes
-----
- Read-only : ne touche aucun notebook.
- Couvre 5 familles (.NET C# heavy) : GameTheory, ML.Net, DecisionTheory/DecInfer,
  Infer, Applications/CSP/Search, Sudoku, SMT/Z3, Part1-Foundations, Part4-Metaheuristics.
- Le scope est strictement plus large que #6927 (8 nb Infer/DecInfer) : on trouve
  en pratique 22+ notebooks repo-wide. Ce tool sert de barometre + plan source
  pour les PRs de fix suivantes (1 PR par notebook, scope R3-atomique).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path


# Patterns to detect
CDN_PATTERN = re.compile(r"cdn\.plot\.?ly", re.IGNORECASE)
IMAGE_MIMES = ("image/png", "image/jpeg", "image/svg+xml", "image/webp", "image/gif")

# Skips
SKIP_DIRS = {
    ".git",
    "_output",
    "_archives",
    ".ipynb_checkpoints",
    ".lake",  # Lean vendored
    ".claude",
    "node_modules",
}


def iter_notebooks(root: Path):
    """Yield all .ipynb paths under root, skipping vendored/archived dirs."""
    for p in root.rglob("*.ipynb"):
        # Skip vendored, archives, outputs
        rel_parts = p.parts
        if any(part in SKIP_DIRS for part in rel_parts):
            continue
        # Skip _output.ipynb duplicates (always have same outputs as primary)
        if p.stem.endswith("_output"):
            continue
        yield p


def cell_is_risky(cell: dict) -> bool:
    """A cell is risky if it has a cdn.plot.ly output and NO image/* output.

    Rationale: cdn.plot.ly HTML renders only in a kernel with internet + JS.
    If the SAME cell also emits image/png or image/svg+xml, GitHub/nbviewer can
    fall back to the static image. Risky = NO static fallback.
    """
    outputs = cell.get("outputs", [])
    if not outputs:
        # No outputs at all (un-executed cell) — can't be a static-render risk,
        # but log for awareness
        return False

    # Quick pre-check: serialize once
    try:
        out_blob = json.dumps(outputs, ensure_ascii=False)
    except (TypeError, ValueError):
        # Some outputs may have non-serializable parts (rare); fall through
        return False

    has_cdn = bool(CDN_PATTERN.search(out_blob))
    if not has_cdn:
        return False

    # Has cdn: check for image MIME fallback
    for out in outputs:
        if not isinstance(out, dict):
            continue
        data = out.get("data", {})
        if not isinstance(data, dict):
            continue
        for mime in data.keys():
            if mime in IMAGE_MIMES:
                return False  # has static fallback → not risky
    return True


def scan_notebook(nb_path: Path) -> list[int]:
    """Return list of cell indexes that are risky in this notebook."""
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as e:
        print(f"  [WARN] skip {nb_path.name}: {e}", file=sys.stderr)
        return []
    risky = []
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        if cell_is_risky(cell):
            risky.append(i)
    return risky


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument(
        "--root",
        default="MyIA.AI.Notebooks",
        type=Path,
        help="Root directory to scan (default: MyIA.AI.Notebooks)",
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="Emit JSON output instead of human-readable markdown table",
    )
    ap.add_argument(
        "--exit-risky-nb",
        type=int,
        default=None,
        metavar="N",
        help="Exit with code 1 if more than N risky notebooks are found (CI gate).",
    )
    ap.add_argument(
        "--fix-plan-out",
        type=Path,
        default=None,
        help="Write a Markdown fix-plan file (1 row per risky cell) to this path.",
    )
    args = ap.parse_args()

    if not args.root.exists():
        print(f"[ERROR] root not found: {args.root}", file=sys.stderr)
        return 2

    # Scan
    risky_cells = []  # list of (notebook, cell_idx, family)
    family_counts = defaultdict(lambda: {"notebooks": 0, "cells": 0})
    total_nbs_scanned = 0
    total_nbs_risky = 0

    for nb_path in sorted(iter_notebooks(args.root)):
        total_nbs_scanned += 1
        risky = scan_notebook(nb_path)
        if not risky:
            continue
        total_nbs_risky += 1
        # Extract family (= top-level dir under root, e.g. "Infer" under "Probas/Infer")
        rel = nb_path.relative_to(args.root)
        family = "/".join(rel.parts[:-1])
        family_counts[family]["notebooks"] += 1
        family_counts[family]["cells"] += len(risky)
        for cell_idx in risky:
            risky_cells.append((nb_path, cell_idx, family))

    # Emit results
    if args.json:
        out = {
            "root": str(args.root),
            "summary": {
                "total_notebooks_scanned": total_nbs_scanned,
                "risky_notebooks": total_nbs_risky,
                "risky_cells_total": len(risky_cells),
                "by_family": dict(family_counts),
            },
            "risky_cells": [
                {"notebook": str(nb.relative_to(args.root)), "cell_idx": idx, "family": fam}
                for nb, idx, fam in risky_cells
            ],
        }
        print(json.dumps(out, indent=2, ensure_ascii=False))
    else:
        print(f"# Plotly-CDN static-render risk scan")
        print(f"Root: {args.root}")
        print(f"Notebooks scanned: {total_nbs_scanned}")
        print(f"Notebooks risky (>=1 cell): {total_nbs_risky}")
        print(f"Cells risky total: {len(risky_cells)}")
        print()
        if not risky_cells:
            print("**None.** All Plotly outputs have a static image fallback.")
        else:
            print("## By family")
            for fam in sorted(family_counts):
                fc = family_counts[fam]
                print(f"- `{fam}/`: {fc['notebooks']} nb, {fc['cells']} cells")
            print()
            print("## Risky cells (notebook → cell)")
            print("| Notebook | cell idx | Family |")
            print("|----------|---------|--------|")
            for nb, idx, fam in risky_cells:
                rel = nb.relative_to(args.root)
                print(f"| `{rel}` | {idx} | `{fam}` |")

    # Fix plan file
    if args.fix_plan_out:
        lines = []
        lines.append("# Fix plan — Plotly-CDN static-rendering risk (#6927)")
        lines.append("")
        lines.append("Generated by `scripts/notebook_tools/check_plotly_static_risk.py`.")
        lines.append("")
        lines.append("Each row = one cell to fix (replace CDN-script Plotly with a static PNG/SVG).")
        lines.append("Recommended batch granularity: **1 notebook per PR** (R3 atomique — G.4).")
        lines.append("")
        lines.append("## Summary")
        lines.append(f"- {total_nbs_scanned} notebooks scanned")
        lines.append(f"- {total_nbs_risky} notebooks risky")
        lines.append(f"- {len(risky_cells)} cells risky total")
        lines.append("")
        lines.append("## By family")
        for fam in sorted(family_counts):
            fc = family_counts[fam]
            lines.append(f"- `{fam}/`: {fc['notebooks']} nb, {fc['cells']} cells")
        lines.append("")
        lines.append("## Risky cells")
        lines.append("")
        lines.append("| # | Notebook | cell idx | Family |")
        lines.append("|---|----------|---------|--------|")
        for i, (nb, idx, fam) in enumerate(risky_cells, 1):
            rel = nb.relative_to(args.root)
            lines.append(f"| {i} | `{rel}` | {idx} | `{fam}` |")
        lines.append("")
        lines.append("## Batch recommendation (R6 anti-monotonie)")
        lines.append("")
        lines.append("Pick ONE notebook per PR (R3 atomique); cover ONE family before pivoting.")
        lines.append("Suggested priorities (descending pedagogical impact):")
        lines.append("")
        lines.append("1. **Probas/Infer** (canonical famille of #6927): Infer-12 first (already covered by c.450, see if PR helps here)")
        lines.append("2. **GameTheory/GameTheory-*Csharp** (C548-L2 also used here, scope broader than #6927)")
        lines.append("3. **Search/Applications/CSP** (App-7b App-8 — used by Search-series)")
        lines.append("4. **ML.Net** (ML-5-TimeSeries)")
        lines.append("5. **Sudoku**, **SymbolicAI/SMT/Z3** (lower priority)")
        lines.append("")
        lines.append("## Reference")
        lines.append("")
        lines.append("- Investigation: ai-01 2026-07-16 (see #6927 body)")
        lines.append("- Canon C548-L2: `record PlotlyHtml + Formatter.Register` (cf MEMORY.md c.452)")
        lines.append("- Issue: #6927 (scope restreint Infer/DecInfer — élargir repo-wide via ce plan)")
        lines.append("")
        args.fix_plan_out.write_text("\n".join(lines), encoding="utf-8")
        print(f"\nFix plan written: {args.fix_plan_out} ({len(risky_cells)} cells)")

    # CI gate
    if args.exit_risky_nb is not None and total_nbs_risky > args.exit_risky_nb:
        print(
            f"\n[FAIL] {total_nbs_risky} risky notebooks > threshold {args.exit_risky_nb}",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
