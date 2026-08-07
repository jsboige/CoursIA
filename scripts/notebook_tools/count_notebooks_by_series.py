#!/usr/bin/env python3
"""Count notebooks by series and compare with README declarations.

Usage:
    python count_notebooks_by_series.py                    # All series, pedagogical only
    python count_notebooks_by_series.py --all               # Include research/examples/archives
    python count_notebooks_by_series.py --series GenAI      # Single series
    python count_notebooks_by_series.py --json              # JSON output for scripts
    python count_notebooks_by_series.py --check-readme      # Compare with README counts

Excluded by default (pedagogical mode):
    - .ipynb_checkpoints/, obj/, bin/, __pycache__/, .git/  (directory names only;
      NOT matched against filename -- a notebook named "Foo-CombinatorialGames.ipynb"
      must still be counted, see #9851)
    - research notebooks (path contains "research")
    - archive/backup notebooks (path contains "archive" or "_output")
    - partner course student examples (partner-course-*/examples/)
"""

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

# EXCLUDE_ALWAYS: directory names only, matched EXACTLY against directory
# segments of the notebook path (NEVER against the filename -- a notebook named
# "Foo-CombinatorialGames.ipynb" must still be counted, see #9851 for the bug
# history where substring matching excluded 5 GameTheory root notebooks).
EXCLUDE_ALWAYS = {".ipynb_checkpoints", "obj", "bin", "__pycache__", ".git"}

# EXCLUDE_PEDAGOGICAL: path-substring by NAMING CONVENTION. These are intentional
# pedagogical exclusions: papermill _output artifacts, QC research quantbooks,
# archives, partner-course student examples. Substring match on the relative
# path is the documented behaviour here -- do NOT change to exact match.
EXCLUDE_PEDAGOGICAL = {"research", "archive", "_output", "partner-course", "examples"}

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
        # Directory segments only -- never the filename -- for EXCLUDE_ALWAYS
        # (bin/ obj/ __pycache__/ .git/ .ipynb_checkpoints/ are directories).
        # See #9851: substring-on-all-parts silently dropped "CombinatorialGames"
        # notebooks (5 in GameTheory, false positive on "bin" substring).
        dir_parts = parts[:-1]

        if any(exc in dir_parts for exc in EXCLUDE_ALWAYS):
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
    """Extract the AUTHORITATIVE series notebook count from a README.

    Scope-aware (#9835): anchored on the generated ``<!-- CATALOG-STATUS -->``
    marker (``pedagogical_count``, maintained daily by ``catalog-cron.yml``),
    which is the canonical per-series total. Falls back to an explicitly-anchored
    prose "Total" only when the marker is absent -- never the first number that
    matches anywhere in the file. That first-match behaviour compared notebooks
    to sub-section headers (e.g. SymbolicAI's "28 notebooks Lean" while the
    series has 226) and to exercise counts (IIT: 53 notebooks vs "3 exercices").

    A count of exercises is NOT a count of notebooks: the former prose-fallback
    ``(\\d+)\\s+exercices`` is removed. A series with no marker and no explicit
    Total returns None ("no count") -- an honest silence, not a number caught at
    random.
    """
    if not readme_path.exists():
        return None

    text = readme_path.read_text(encoding="utf-8")

    # Primary anchor: the generated CATALOG-STATUS marker (canonical,
    # cron-maintained, per-series). See #9835.
    marker = re.search(r"<!--\s*CATALOG-STATUS\b(.*?)-->", text, re.S)
    if marker:
        m = re.search(r"pedagogical_count:\s*(\d+)", marker.group(1))
        if m:
            val = int(m.group(1))
            if val > 0:
                return val

    # Fallback (marker absent): an explicitly-anchored series-total in prose.
    # Require an explicit "Total" anchor -- NOT the first "N notebooks" anywhere
    # (often a sub-section header, e.g. "28 notebooks Lean"). See #9835.
    for pattern in (
        # Table row: | Total | 84 |
        r"\|\s*Total\s*\|\s*(\d+)",
        # Explicit "N notebooks total"
        r"(\d+)\s+notebooks?\s+total",
    ):
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            val = int(match.group(1))
            if val > 0:
                return val

    # No marker, no explicit total -> honest silence (not a random number).
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
    parser.add_argument(
        "--check", action="store_true",
        help="Assertion (issue #9857): exit 1 if tool pedagogical count diverges from catalogue",
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

    if args.check:
        # Assertion #9857 : l'outil (pedagogique) et le catalogue (curé) doivent
        # converger. Les deux appliquent le même EXCLUDE_PEDAGOGICAL, donc tout
        # écart signale soit un drift de curation (notebook fraîchement ajouté,
        # non curé — résolu par catalog-cron < 24h) soit un changement structurel.
        # Détail chemin-par-chemin : scripts/audit/check_denominators.py --strict.
        tool_total = sum(r["total"] for r in results.values())
        catalog_path = REPO_ROOT / "COURSE_CATALOG.generated.json"
        try:
            with open(catalog_path, encoding="utf-8") as f:
                catalog = json.load(f)
        except FileNotFoundError:
            print(f"ERREUR: catalogue introuvable: {catalog_path}", file=sys.stderr)
            return 2
        catalog_count = len(catalog) if isinstance(catalog, list) else len(
            catalog.get("notebooks", []) if isinstance(catalog, dict) else []
        )

        print("CHECK -- convergence catalogue / outil")
        print(f"  Outil (pedagogical) : {tool_total}")
        print(f"  Catalogue (curated) : {catalog_count}")
        if tool_total == catalog_count:
            print(f"  Statut              : OK -- convergent ({tool_total} == {catalog_count})")
            return 0
        delta = tool_total - catalog_count
        if delta > 0:
            direction = "outil > catalogue : drift de curation (notebook fraichement ajoute, non cure -- resolu par catalog-cron < 24h)"
        else:
            direction = "catalogue > outil : notebook cure mais exclu par chemin outil (ex. examples/ promu au catalogue)"
        print(f"  DIVERGENCE          : {abs(delta)} -- {direction}")
        print("  -> investiguer : py scripts/audit/check_denominators.py --strict")
        return 1

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
    sys.exit(main())
