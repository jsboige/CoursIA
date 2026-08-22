#!/usr/bin/env python3
"""Gate the certified-modules contract of a lake subtree (#12330).

Why this organ exists
---------------------
The ``fail-on-sorry`` job of ``lean-social-choice.yml`` carried three defects
(issue #12330):

1. **Fail-open**: a certified module that disappears (rename, move, absorb)
   passed in silence -- ``if [ -f "$f" ]`` with no ``else`` -- and the job
   still concluded "All certified modules are sorry-free". A zero denominator
   read exactly like a zero numerator. ``SocialChoice`` itself already lived
   this motion: the subtree was absorbed from the retired lake
   ``social_choice_lean`` (workflow header), and #12329 added a module the
   hardcoded list never learned about.
2. **Wrong instrument**: ``grep -c "sorry"`` counts the prose (docstrings,
   ``--`` comments) -- the very instrument ``anti-regression.md`` forbids
   (measured 2026-08-14: 484 naive for 21 real across the 21 lakes).
3. **Unverifiable exhaustiveness**: the certified list was hardcoded in the
   workflow, so a module added to the subtree was invisible to the gate.

This script replaces the hand-rolled loop. The certified contract lives in a
manifest **next to the modules** (``<subdir>/CERTIFIED.txt``): one filename
per line, ``#`` comments allowed, ``!name.lean`` = explicitly excluded (the
exclusion is a decision, not a silence). The gate verifies three things, each
naming its target on failure (a gate that blushes must say at what):

1. every listed file EXISTS                        -> ``MISSING: <file>``
2. every ``*.lean`` in the subtree is listed or
   explicitly excluded                             -> ``STALE-LIST: <file>``
3. every listed file carries 0 real code ``sorry``
   (canonical instrument: ``count_code_sorry.scan_file``,
   comment-stripped, docstrings don't count)       -> ``SORRY: <decl> <file>:<line>``

Exit 0 = contract holds. Exit 1 = the named failure(s). Pure text analysis,
no Lean toolchain needed, CI-cheap.

Usage
-----
    python scripts/lean/check_certified_sorry.py \
        --lake MyIA.AI.Notebooks/GameTheory/game_theory_lean \
        --subdir SocialChoice

Module usage:
    from check_certified_sorry import check_subtree, parse_manifest
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from count_code_sorry import scan_file  # noqa: E402  -- canonical instrument

MANIFEST_NAME = "CERTIFIED.txt"


def parse_manifest(text: str) -> tuple[list[str], list[str]]:
    """Split manifest text into (certified files, explicitly-excluded files).

    One filename per line. ``!name.lean`` marks a deliberate exclusion (kept
    visible so the exclusion is a decision, not an oversight). ``#`` comments
    and blank lines are ignored.
    """
    certified: list[str] = []
    excluded: list[str] = []
    for raw in text.splitlines():
        # Inline comments too: a `#` never appears in a .lean filename, so
        # `Arrow.lean  # reason` is Arrow.lean. (Caught live on first run:
        # entries with inline comments matched no file.)
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("!"):
            excluded.append(line[1:].strip())
        else:
            certified.append(line)
    return certified, excluded


def check_subtree(lake_root: Path, subdir: str) -> tuple[list[str], dict]:
    """Run the three checks. Returns (failures, report). failures == [] = pass."""
    tree = lake_root / subdir
    manifest_path = tree / MANIFEST_NAME
    if not manifest_path.is_file():
        return ([f"MISSING-MANIFEST: {subdir}/{MANIFEST_NAME} — the certified "
                 f"contract file does not exist (create it: one filename per "
                 f"line, !name.lean = explicit exclusion)"], {})

    certified, excluded = parse_manifest(manifest_path.read_text(encoding="utf-8"))
    failures: list[str] = []
    report: dict = {"subdir": subdir, "certified": certified,
                    "excluded": excluded, "per_file": {}}

    # Check 1 -- every certified file exists (fail-CLOSED: the anchor is the
    # contract; a renamed module must break the gate, not slip out of view).
    for name in certified:
        if not (tree / name).is_file():
            failures.append(f"MISSING: {subdir}/{name}")

    # Check 2 -- exhaustiveness: nothing in the subtree is unaccounted for.
    on_disk = sorted(p.name for p in tree.glob("*.lean"))
    accounted = set(certified) | set(excluded)
    for name in on_disk:
        if name not in accounted:
            failures.append(
                f"STALE-LIST: {subdir}/{name} is in the subtree but neither "
                f"certified nor explicitly excluded in {MANIFEST_NAME} — a new "
                f"module must enter the contract in the same PR that adds it")
    for name in certified:
        if name in excluded:
            failures.append(f"CONTRADICTION: {subdir}/{name} both certified and excluded")

    # Check 3 -- 0 real code sorry in every certified file (canonical
    # instrument: comment-stripped scan, docstrings don't count).
    for name in certified:
        path = tree / name
        if not path.is_file():
            continue  # already reported by check 1
        decls, naive, code = scan_file(path, lake_root)
        report["per_file"][name] = {"naive_sorry": naive, "code_sorry": code}
        if code:
            where = [f"{d.kind} {d.name or '<anon>'} ({subdir}/{name}:{d.line})"
                     for d in decls if d.sorry_count]
            for w in where:
                failures.append(f"SORRY: {w}")
    return failures, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Gate the certified-modules contract of a lake subtree (#12330).")
    parser.add_argument("--repo", default=".", help="repo root (default: cwd)")
    parser.add_argument("--lake", required=True, help="lake root, repo-relative")
    parser.add_argument("--subdir", required=True,
                        help="certified subtree inside the lake (e.g. SocialChoice)")
    parser.add_argument("--json", action="store_true", help="machine-readable output")
    args = parser.parse_args(argv)

    lake_root = (Path(args.repo) / args.lake).resolve()
    failures, report = check_subtree(lake_root, args.subdir)

    if args.json:
        print(json.dumps({"ok": not failures, "failures": failures, **report},
                         indent=2, ensure_ascii=False))
    else:
        for name, stats in report.get("per_file", {}).items():
            print(f"  {args.subdir}/{name}: code sorry = {stats['code_sorry']} "
                  f"(naive grep would say {stats['naive_sorry']})")
        if failures:
            print()
            for f in failures:
                print(f"FAIL {f}")
            return 1
        print(f"OK: {len(report.get('certified', []))} certified modules, "
              f"{len(report.get('excluded', []))} explicit exclusion(s), "
              f"0 code sorry (canonical instrument).")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
