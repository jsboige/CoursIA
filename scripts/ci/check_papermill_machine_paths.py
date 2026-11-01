#!/usr/bin/env python3
"""Papermill machine-path delta guard — a PR must not ADD an absolute
``metadata.papermill.input_path`` / ``output_path`` to a notebook.

Why a delta and not an absolute check
-------------------------------------
``scrub_papermill_paths.py --scan-all`` measures **22 notebooks / 42 absolute
paths on ``main``** (measured 2026-11-01, see the body of the PR that wired
this guard). An absolute gate would redden every PR touching one of those
notebooks for an unrelated reason and freeze the cluster -- the same trap
``pip_leak_delta.py`` documents (#6314). The durable transposition is a
**delta**: compare the count on the pull-request base with the count on the
head, and fail only when the head *introduces* a new absolute path.

Why a CI guard when a pre-commit hook already exists
----------------------------------------------------
``scrub-papermill-paths`` is wired in ``.pre-commit-config.yaml`` and does run
on this clone (measured 2026-11-01: hook present, ``pre-commit 4.6.1``,
``core.hooksPath`` set). A client-side hook is bypassable by design
(``--no-verify``, ``SKIP``, any commit that does not go through git hooks), and
four leaks did land in a single day (#23914, #23917, #23943, #23958) before
being repaired after the fact. The hook stays the first line; this guard is the
one that cannot be skipped.

Scope
-----
Only notebooks the PR **changes** are compared, so the stock on ``main`` never
reddens anybody. Submodule contents are out of scope (``git diff`` names a
submodule as a single path). Generated files are irrelevant here: only
``metadata.papermill`` is read.

Exit codes: 0 = no new absolute path ; 1 = the head introduces at least one ;
2 = IO / git error.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys

ABS_MARKERS = ("C:\\", "C:/", "D:\\", "D:/", "/home/", "/Users/", "/mnt/", "/tmp/")
PA_FORMAT_KEYS = ("input_path", "output_path")


def _git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args], capture_output=True, text=True, encoding="utf-8", errors="replace"
    )
    if result.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} -> rc={result.returncode}: {result.stderr.strip()}")
    return result.stdout


def changed_notebooks(base_ref: str, head_ref: str) -> list[str]:
    """Notebooks whose blob differs between base and head."""
    out = _git("diff", "--name-only", f"{base_ref}...{head_ref}", "--", "*.ipynb")
    return [line.strip() for line in out.splitlines() if line.strip()]


def papermill_paths(ref: str, path: str) -> list[str]:
    """Absolute papermill paths recorded in ``path`` at ``ref`` ([] if absent)."""
    try:
        blob = _git("show", f"{ref}:{path}")
    except RuntimeError:
        return []  # file absent at that ref (added or removed by the PR)
    try:
        notebook = json.loads(blob)
    except json.JSONDecodeError:
        return []
    papermill = (notebook.get("metadata") or {}).get("papermill") or {}
    found = []
    for key in PA_FORMAT_KEYS:
        value = papermill.get(key)
        if isinstance(value, str) and value.startswith(ABS_MARKERS):
            found.append(f"{key}: {value}")
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-ref", required=True, help="pull-request base (ex origin/main)")
    parser.add_argument("--head-ref", default="HEAD", help="pull-request head (default HEAD)")
    parser.add_argument("--json", action="store_true", help="machine-readable verdict")
    args = parser.parse_args()

    try:
        notebooks = changed_notebooks(args.base_ref, args.head_ref)
    except RuntimeError as exc:
        print(f"[ERREUR] {exc}", file=sys.stderr)
        return 2

    introduced = []
    for path in notebooks:
        base_paths = papermill_paths(args.base_ref, path)
        head_paths = papermill_paths(args.head_ref, path)
        delta = len(head_paths) - len(base_paths)
        if delta > 0:
            introduced.append({"file": path, "base": len(base_paths), "head": len(head_paths)})
            print(f"[DEFECT] {path} -- {len(base_paths)} -> {len(head_paths)} chemin(s) absolu(s)")
            for entry in head_paths:
                print(f"         {entry}")

    if args.json:
        print(json.dumps({"introduced": introduced, "changed": len(notebooks)}, ensure_ascii=False))

    if introduced:
        print(
            f"\n{len(introduced)} carnet(s) introduisent un chemin machine dans "
            "metadata.papermill.\nRemede (metadata seul, aucune re-execution due, C.2) :\n"
            "  python scripts/notebook_tools/scrub_papermill_paths.py --apply <carnet>"
        )
        return 1

    print(f"papermill machine paths: 0 introduction sur {len(notebooks)} carnet(s) modifie(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
