#!/usr/bin/env python3
"""Pip-leak HIGH delta guard — compare two ``audit_pip_install_cells.py`` JSON
scans and fail if the PR introduces *new* HIGH-severity ``!pip install`` leaks.

Why a delta (not an absolute ``--check`` fail)
---------------------------------------------
``audit_pip_install_cells.py --scan-all --check`` fails on ANY HIGH occurrence.
The repo still carries inherited HIGH notebooks (drained one-PR-per-notebook per
regle C.3, cf #6314 / #6310 / #6313). An absolute gate would therefore block
every PR that touches an inherited-leak notebook for an unrelated reason and
freeze the whole cluster — the opposite of #6312's ``strip_probe_banner.py``
mirror, which is ``--apply`` (auto-fix, never fails).

The durable, non-blocking transposition is a **delta guard**: count HIGH
occurrences on BASE (pull-request base) and HEAD (pull-request head), fail only
when HEAD > BASE, i.e. when the PR *introduces* new leaks. Existing leaks are
tolerated; regressions are not.

Usage
-----
Typically driven by ``.github/workflows/pip-leak-guard.yml`` which produces the
two JSON files via two ``--scan-all`` runs (swapping ``MyIA.AI.Notebooks/``
between base and head with ``git checkout``)::

    python scripts/notebook_tools/audit_pip_install_cells.py --scan-all --json > head.json
    git checkout baseref -- MyIA.AI.Notebooks
    python scripts/notebook_tools/audit_pip_install_cells.py --scan-all --json > base.json
    git checkout HEAD -- MyIA.AI.Notebooks
    python scripts/notebook_tools/pip_leak_delta.py base.json head.json

Standalone (local, no git): the two JSON files may be produced by any means.

Exit codes: 0 = no new HIGH leaks ; 1 = HEAD introduces HIGH delta > 0 ; 2 = IO
or JSON error.

See #6314 (detector), #6309/#6312 (probeAddresses mirror pattern),
secrets-hygiene.md §6 (Stop & Repair, source-level fix).
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HIGH_CLASSIFICATIONS = ("UNCONDITIONAL_BASH", "UNCONDITIONAL_SYS")


def high_occurrences(data):
    """Yield (file, cell_index, classification) for every HIGH occurrence in a
    parsed audit-pip-install JSON document."""
    for nb in data:
        f = nb.get("file", "?")
        for occ in nb.get("occurrences", []):
            cls = occ.get("classification")
            if cls in HIGH_CLASSIFICATIONS:
                yield (f, occ.get("cell_index"), cls)


def count_high(data):
    return sum(1 for _ in high_occurrences(data))


def high_by_file(data):
    """map(file -> list of cell_index) for HIGH occurrences."""
    by = {}
    for f, idx, _ in high_occurrences(data):
        by.setdefault(f, []).append(idx)
    return by


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Fail if HEAD introduces new HIGH !pip install leaks vs BASE."
    )
    parser.add_argument("base", help="BASE JSON (audit_pip_install_cells.py --json)")
    parser.add_argument("head", help="HEAD JSON (audit_pip_install_cells.py --json)")
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

    print(f"pip-leak guard: BASE HIGH={base_n}  HEAD HIGH={head_n}  delta={delta:+d}")

    if delta <= 0:
        print(
            "OK: no new HIGH leaks introduced "
            f"(inherited {head_n} tolerated, drained one-PR-per-notebook per #6314)."
        )
        return 0

    # Report which files gained HIGH occurrences (new or worsened).
    base_by = high_by_file(base)
    head_by = high_by_file(head)
    print(
        f"FAIL: PR introduces {delta} new HIGH-severity !pip install leak(s). "
        "Source-level fix required (remove the !pip install line + re-execute, "
        "cf secrets-hygiene.md §6 Stop & Repair, regle F).",
        file=sys.stderr,
    )
    print("Newly-leaking / worsened notebooks:", file=sys.stderr)
    for f, cells in sorted(head_by.items()):
        prev = len(base_by.get(f, []))
        if len(cells) > prev:
            print(f"  +{len(cells) - prev}  {f}  (cells {cells})", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
