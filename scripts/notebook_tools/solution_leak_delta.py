#!/usr/bin/env python3
"""Solution-leak HIGH delta guard — compare two ``detect_solution_leaks.py``
JSON scans and fail if the PR introduces *new* HIGH-severity solution leaks
(an Exercice cell containing its complete solution instead of a stub).

Why a delta (not an absolute ``--check`` fail)
---------------------------------------------
``detect_solution_leaks.py --scan-all --check`` fails on ANY HIGH occurrence.
The repo still carries 111 inherited HIGH leaks (angle-mut #8053, to be drained
one-PR-per-notebook). An absolute gate would therefore block every PR that
touches an inherited-leak notebook for an unrelated reason and freeze the whole
cluster — the opposite of a useful rollout.

The durable, non-blocking transposition is a **delta guard** (mirror of
``pip_leak_delta.py`` / #6314): count HIGH occurrences on BASE (pull-request
base) and HEAD (pull-request head), fail only when HEAD > BASE, i.e. when the PR
*introduces* new leaks. Existing leaks are tolerated (inventoried in the CI step
summary); regressions are not. When the inherited backlog is drained, the gate
becomes a strict absolute fail naturally — realising #8053's "WARN first, FAIL
after cleanup" without a mode switch.

Usage
-----
Typically driven by ``.github/workflows/solution-leak-guard.yml`` which produces
the two JSON files via two ``--scan-all --json`` runs (swapping
``MyIA.AI.Notebooks/`` between base and head with ``git checkout``)::

    python scripts/notebook_tools/detect_solution_leaks.py --scan-all --json > head.json
    git checkout baseref -- MyIA.AI.Notebooks
    python scripts/notebook_tools/detect_solution_leaks.py --scan-all --json > base.json
    git checkout HEAD -- MyIA.AI.Notebooks
    python scripts/notebook_tools/solution_leak_delta.py base.json head.json

Standalone (local, no git): the two JSON files may be produced by any means.

Exit codes: 0 = no new HIGH leaks ; 1 = HEAD introduces HIGH delta > 0 ; 2 = IO
or JSON error.

See #8053 (CI branch of the detector), #6314 (pip-leak mirror pattern),
exercise-example-labeling.md (content-based Exemple/Exercice rule).
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def high_keys(data):
    """Yield stable identifiers ``(path, cell_index)`` for every HIGH finding.

    A finding is matched on (path, cell_index) so that editing the prose of an
    already-leaking cell does NOT register as a regression — only a genuinely
    new leak (new cell or new notebook) does. ``path`` is normalised to
    forward slashes for cross-platform stability (Windows runs emit ``\\``).
    """
    for f in data:
        if f.get("severity") != "HIGH":
            continue
        path = str(f.get("path", "?")).replace("\\", "/")
        yield (path, f.get("cell_index"))


def count_high(data):
    return sum(1 for _ in high_keys(data))


def high_by_path(data):
    """map(path -> sorted list of cell_index) for HIGH findings."""
    by: dict[str, list] = {}
    for path, idx in high_keys(data):
        by.setdefault(path, []).append(idx)
    for cells in by.values():
        cells.sort()
    return by


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Fail if HEAD introduces new HIGH solution leaks vs BASE."
    )
    parser.add_argument("base", help="BASE JSON (detect_solution_leaks.py --json)")
    parser.add_argument("head", help="HEAD JSON (detect_solution_leaks.py --json)")
    args = parser.parse_args(argv)

    try:
        with open(args.base, encoding="utf-8") as fh:
            base = json.load(fh)
        with open(args.head, encoding="utf-8") as fh:
            head = json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"error: cannot read JSON inputs: {exc}", file=sys.stderr)
        return 2

    base_n = count_high(base)
    head_n = count_high(head)
    delta = head_n - base_n

    print(f"solution-leak guard: BASE HIGH={base_n}  HEAD HIGH={head_n}  delta={delta:+d}")

    if delta <= 0:
        print(
            "OK: no new HIGH solution leaks introduced "
            f"(inherited {head_n} tolerated, angle-mut #8053, drained one-PR-per-notebook)."
        )
        return 0

    # Report which notebooks gained HIGH occurrences (new or worsened).
    base_by = high_by_path(base)
    head_by = high_by_path(head)
    print(
        f"FAIL: PR introduces {delta} new HIGH-severity solution leak(s) "
        "(an Exercice cell containing its complete solution). Stub it per "
        "exercise-example-labeling.md (pass / print('Exercice a completer') / "
        "return None / # TODO — never raise NotImplementedError, cf regle C.1).",
        file=sys.stderr,
    )
    print("Newly-leaking / worsened notebooks:", file=sys.stderr)
    for path, cells in sorted(head_by.items()):
        prev = len(base_by.get(path, []))
        if len(cells) > prev:
            print(f"  +{len(cells) - prev}  {path}  (cells {cells})", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
