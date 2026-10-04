#!/usr/bin/env python3
"""Delta comparator for README-vs-.ipynb violations (F2 of #18970).

Reads two JSON artefacts produced by `dump_readme_link_violations.py` (base
and head) and reports ONLY the violations that the PR introduces (head minus base).

This is the guard that the fast-lane `delta_argv` slot consumes: it lets the
PR gate stay blocking on NEW STALE_LINK (defaut fondateur #13025) without
rouging on the 2428 historical backlog committed before the guard existed.

Exit codes:
    0 = no NEW violation (PR clean)
    1 = at least one NEW violation (PR must be fixed)
    2 = invocation error

Usage:
    python diff_readme_link_violations.py <base.json> <head.json>
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def _key(v: dict) -> tuple[str, str, str]:
    return (v.get("class", ""), v.get("readme", ""), v.get("href", ""))


def _load(path: Path) -> list[dict]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return data.get("violations", [])


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("base_json", type=Path, help="JSON dump sur la base (main)")
    ap.add_argument("head_json", type=Path, help="JSON dump sur la tete (PR)")
    args = ap.parse_args()

    if not args.base_json.is_file():
        print(f"::error::base JSON introuvable: {args.base_json}", file=sys.stderr)
        return 2
    if not args.head_json.is_file():
        print(f"::error::head JSON introuvable: {args.head_json}", file=sys.stderr)
        return 2

    base_set = {_key(v) for v in _load(args.base_json)}
    head_set = {_key(v) for v in _load(args.head_json)}
    new = sorted(head_set - base_set)
    fixed = sorted(base_set - head_set)

    print(f"README-link delta: base={len(base_set)} head={len(head_set)} "
          f"NOUVELLES={len(new)} CORRIGEES={len(fixed)}")
    for cls, readme, href in new:
        print(f"  + {cls}  {readme}  ->  {href}")
    for cls, readme, href in fixed:
        print(f"  - {cls}  {readme}  ->  {href}")

    if new:
        # Meme format que le run originel (regen_quarto_render.py emet
        # `::error::STALE_LINK ...` sur stderr) pour que les outils en
        # aval qui grep le pattern continuent de fonctionner.
        for cls, readme, href in new:
            print(f"::error::{cls} {readme} -> {href}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
