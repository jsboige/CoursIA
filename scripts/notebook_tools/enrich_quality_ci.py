#!/usr/bin/env python3
"""Per-PR enrich-quality REGRESSION gate (CoursIA #13410 / roo-extensions #3374).

Sibling of cell_order_ci.py (Epic #3240): compares the HIGH enrich-quality
findings of a notebook (scripts/notebook_tools/scan_enrich_quality.py)
between its base revision and its PR (head) revision, and fails only on a
*regression* -- a HIGH finding present in head that was NOT already present
in base. Pre-existing findings (legacy leaks, main-space anchors of earlier
enrich waves) do not block unrelated PRs; a brand-new notebook (no base)
must be clean.

Base-vs-head findings (classes (b) MD_REWRITE / MD_SURVIVAL_LOW and (c)
DIACRITICS_LOSS) only exist when a --base is given and are inherently
relative to it, so they always count as new.

A finding's identity is its (category, message) pair. Messages embed the
anchor index / href / shared tokens / survival counts, so they are specific
enough that moving a defect around does not mask a newly introduced one.

Usage:
    enrich_quality_ci.py --base <base.ipynb|NONE> --head <head.ipynb> [--repo-root <dir>]

Exit codes:
    0 - no new HIGH findings in head (or head unreadable -> nothing to gate)
    1 - one or more NEW HIGH findings introduced by head (regression)
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from scan_enrich_quality import scan_notebook  # noqa: E402


def high_signatures(nb_path: str | None, base_path: str | None, repo_root: Path) -> set[tuple[str, str]]:
    """Set of (category, message) for HIGH findings of a notebook, or empty."""
    if not nb_path or nb_path == "NONE" or not Path(nb_path).exists():
        return set()
    rep = scan_notebook(Path(nb_path), base=Path(base_path) if base_path else None,
                        repo_root=repo_root)
    if rep.get("error"):
        return set()
    return {(f["category"], f["message"]) for f in rep["findings"] if f["severity"] == "HIGH"}


def regressions(base_path: str | None, head_path: str | None, repo_root: Path) -> list[tuple[str, str]]:
    """HIGH findings present in head but not in base (sorted, deterministic)."""
    # The base is scanned STANDALONE (no base-of-base): head-only checks run
    # on it, relative checks ((b)/(c)) cannot apply to it.
    base = high_signatures(base_path, None, repo_root)
    head = high_signatures(head_path, base_path, repo_root)
    return sorted(head - base)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Enrich-quality per-PR regression gate.")
    ap.add_argument("--base", help="base revision of the notebook, or NONE for a new file")
    ap.add_argument("--head", required=True, help="head (PR) revision of the notebook, at its repo path")
    ap.add_argument("--repo-root", default=None,
                    help="tree against which hrefs resolve (default: the repo containing this script)")
    args = ap.parse_args(argv)

    repo_root = Path(args.repo_root).resolve() if args.repo_root else Path(__file__).resolve().parent.parent.parent

    new = regressions(args.base, args.head, repo_root)
    if not new:
        return 0

    print(f"REGRESSION in {args.head}: {len(new)} new HIGH enrich-quality finding(s):")
    for category, message in new:
        print(f"  [{category}] {message}")
    print("\nGround-truth each finding (the signal is not a verdict, rule G.1). The anchor")
    print("convention is: code[N] = the N-th CODE cell, 0-based, counted at HEAD.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
