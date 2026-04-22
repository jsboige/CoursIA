#!/usr/bin/env python3
"""Fix notebook cells where source is a string instead of list[str].

Issue #413: Regression introduced by PR #354 where cell source fields
were written as plain strings instead of the Jupyter-required list[str] format.

Usage:
    python scripts/fix_notebook_source.py [path_or_glob ...]
    python scripts/fix_notebook_source.py --dry-run [path_or_glob ...]
    python scripts/fix_notebook_source.py --check [path_or_glob ...]

If no paths given, scans all .ipynb files recursively from CWD.
"""

import json
import glob
import sys
import os


def fix_notebook(path, dry_run=False):
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
    nb = json.loads(content)

    fixed = 0
    for cell in nb.get("cells", []):
        src = cell.get("source")
        if isinstance(src, str):
            cell["source"] = [src]
            fixed += 1

    if fixed == 0:
        return 0, 0

    if not dry_run:
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)
            f.write("\n")

    return fixed, 1


def check_notebook(path):
    with open(path, "r", encoding="utf-8") as f:
        nb = json.load(f)

    bad = 0
    for i, cell in enumerate(nb.get("cells", [])):
        if isinstance(cell.get("source"), str):
            bad += 1
    return bad


def main():
    args = sys.argv[1:]
    dry_run = "--dry-run" in args
    check_mode = "--check" in args
    paths = [a for a in args if not a.startswith("-")]

    if not paths:
        paths = glob.glob("**/*.ipynb", recursive=True)

    paths = [p for p in paths if ".ipynb_checkpoints" not in p]

    if check_mode:
        total_bad = 0
        total_notebooks = 0
        for p in sorted(paths):
            bad = check_notebook(p)
            if bad:
                total_bad += bad
                total_notebooks += 1
                print(f"  {p}: {bad} cells")
        print(f"\nTotal: {total_notebooks} notebooks, {total_bad} affected cells")
        return 0 if total_bad == 0 else 1

    total_cells = 0
    total_notebooks = 0
    for p in sorted(paths):
        cells, nbs = fix_notebook(p, dry_run=dry_run)
        if cells:
            total_cells += cells
            total_notebooks += nbs
            prefix = "[DRY-RUN] " if dry_run else ""
            print(f"  {prefix}{p}: {cells} cells fixed")

    print(f"\nTotal: {total_notebooks} notebooks, {total_cells} cells{' (dry-run)' if dry_run else ''}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
