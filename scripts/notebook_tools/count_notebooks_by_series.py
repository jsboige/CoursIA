#!/usr/bin/env python3
"""Count notebooks by series and compare with README declarations.

Usage:
    python count_notebooks_by_series.py                    # All series, pedagogical only
    python count_notebooks_by_series.py --all               # Include research/examples/archives
    python count_notebooks_by_series.py --series GenAI      # Single series
    python count_notebooks_by_series.py --json              # JSON output for scripts
    python count_notebooks_by_series.py --check-readme      # Compare with README counts

Excluded by default (pedagogical mode):
    - .ipynb_checkpoints/
    - research notebooks (path contains "research")
    - archive/backup notebooks (path contains "archive" or "_output")
    - ESGF student examples (ESGF-*/examples/)
    - obj/, bin/
"""

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_ALWAYS = {".ipynb_checkpoints", "obj", "bin", "__pycache__", ".git"}
EXCLUDE_PEDAGOGICAL = {"research", "archive", "_output", "ESGF", "examples"}

SERIES_ORDER = [
    "GenAI", "Search", "ML", "SymbolicAI", "QuantConnect",
    "GameTheory", "Sudoku", "Probas", "IIT", "RL", "EPF",
]


def count_notebooks_in_dir(
    directory: Path,
    pedagogical: bool = True,
) -> dict:
    """Count .ipynb files in a directory tree.

    Returns dict with 'total' and 'by_subfolder' breakdown.
    """
    by_subfolder = {}
    total = 0

    for nb_path in sorted(directory.rglob("*.ipynb")):
        parts = nb_path.relative_to(directory).parts

        if any(exc in part for part in parts for exc in EXCLUDE_ALWAYS):
            continue

        if pedagogical and any(
            exc in str(nb_path.relative_to(directory))
            for exc in EXCLUDE_PEDAGOGICAL
        ):
            continue

        sub = parts[0] if len(parts) > 1 else "_root"
        by_subfolder[sub] = by_subfolder.get(sub, 0) + 1
        total += 1

    return {"total": total, "by_subfolder": by_subfolder}


def extract_readme_count(readme_path: Path) -> int | None:
    """Try to extract a notebook count from a README file.

    Looks for patterns like "N notebooks", "N notebooks Python",
    table rows with "Notebooks" label, or blockquote stats.
    Returns the first plausible match (> 0).
    """
    if not readme_path.exists():
        return None

    text = readme_path.read_text(encoding="utf-8")

    # Specific patterns ordered by reliability
    patterns = [
        # Blockquote: > **28 notebooks Python**
        r"\*\*(\d+)\s*notebooks",
        # Table row: | Notebooks | 28 |
        r"\|\s*Notebooks?\s*\|\s*(\d+)",
        # Inline: "28 notebooks Python"
        r"(\d+)\s+notebooks?\s+Python",
        # Inline: "N notebooks"
        r"(\d+)\s+notebooks",
        # Table row: | Total | 84 |
        r"\|\s*Total\s*\|\s*(\d+)",
        # French: "N exercices"
        r"(\d+)\s+exercices",
    ]

    for pattern in patterns:
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            val = int(match.group(1))
            if val > 0:
                return val
    return None


def main():
    parser = argparse.ArgumentParser(
        description="Count notebooks by series in CoursIA repository"
    )
    parser.add_argument(
        "--all", action="store_true",
        help="Include research, examples, and archive notebooks",
    )
    parser.add_argument(
        "--series", type=str, default=None,
        help="Count only a specific series (e.g. GenAI)",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output as JSON",
    )
    parser.add_argument(
        "--check-readme", action="store_true",
        help="Compare actual counts with README declarations",
    )
    args = parser.parse_args()

    pedagogical = not args.all
    results = {}

    series_dirs = sorted(NOTEBOOKS_DIR.iterdir()) if not args.series else [
        NOTEBOOKS_DIR / args.series
    ]

    for series_dir in series_dirs:
        if not series_dir.is_dir():
            continue
        if series_dir.name in EXCLUDE_ALWAYS or series_dir.name.startswith("."):
            continue

        counts = count_notebooks_in_dir(series_dir, pedagogical=pedagogical)
        if counts["total"] > 0 or args.series:
            results[series_dir.name] = counts

    if args.check_readme:
        print(f"\n{'Series':<15} {'Actual':>7} {'README':>7} {'Status':<10}")
        print("-" * 45)
        for name in SERIES_ORDER:
            if name not in results:
                continue
            actual = results[name]["total"]
            readme_path = NOTEBOOKS_DIR / name / "README.md"
            declared = extract_readme_count(readme_path)
            if declared is None:
                status = "no count"
            elif actual == declared:
                status = "OK"
            else:
                status = f"MISMATCH"
            declared_str = str(declared) if declared is not None else "?"
            print(f"{name:<15} {actual:>7} {declared_str:>7} {status:<10}")
        print(f"\nTotal: {sum(r['total'] for r in results.values())} notebooks in {len(results)} series")
        return

    if args.json:
        print(json.dumps(results, indent=2, ensure_ascii=False))
        return

    mode = "pedagogical" if pedagogical else "all"
    print(f"\nNotebook counts by series ({mode})")
    print(f"{'=' * 45}")

    total_all = 0
    for name in SERIES_ORDER:
        if name not in results:
            continue
        total = results[name]["total"]
        subs = results[name]["by_subfolder"]
        total_all += total

        sub_detail = ""
        if len(subs) > 1:
            top_subs = sorted(subs.items(), key=lambda x: -x[1])[:3]
            sub_detail = " (" + ", ".join(f"{k}: {v}" for k, v in top_subs) + ")"

        print(f"  {name:<15} {total:>4} notebooks{sub_detail}")

    remaining = sum(
        r["total"] for name, r in results.items()
        if name not in SERIES_ORDER
    )
    if remaining:
        print(f"  {'(other)':<15} {remaining:>4} notebooks")

    print(f"{'=' * 45}")
    print(f"  {'TOTAL':<15} {total_all + remaining:>4} notebooks in {len(results)} series")


if __name__ == "__main__":
    main()
