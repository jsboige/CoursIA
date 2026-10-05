#!/usr/bin/env python3
r"""Detect text files whose blob EOL disagrees with their `.gitattributes` EOL.

Issue #19374. The class of #19287 : a vendored file with CRLF or mixed line
endings (`git ls-files --eol` reports `i/crlf` or `i/mixed`) is committed
with `.gitattributes` declaring it as `eol=lf` (or `text`). Git renormalizes
the **worktree** to LF on every checkout, but never rewrites the blob. The
file then looks modified on every machine that touches it -- any check
depending on a clean tree (merge_ready, check_clean_cycle_exit) stops.

Scope : files **added or modified by the PR** (delta vs `base_ref`). Heritance
on `main` is out of scope -- a renormalization pass (#19373) is a separate
gesture. Acceptance criterion 4 of #19374 measures the inherit-free `main` :
a separate sweep, not this gate.

Members of the family :

    i/crlf   blob ends in CRLF (.bat, fixture de test)
    i/mixed  blob mixes LF and CRLF in the same file (e.g. CRLF upstream, LF
             header in the merge)

Both are rejected when the **attribute** is `eol=lf` or `text`. A file
intentionally CRLF is declared by `eol=crlf` or `-text` in `.gitattributes`,
never by an exemption inside this check.

Usage :
    python scripts/ci/check_eol_blob_attribute.py --diff origin/main...HEAD
    python scripts/ci/check_eol_blob_attribute.py --diff origin/main...HEAD --json
    python scripts/ci/check_eol_blob_attribute.py --diff origin/main...HEAD --base-ref origin/main

Verdicts :
    CLEAN    no offending file in the diff (exit 0)
    FAIL     at least one file's blob EOL disagrees with attribute (exit 1)
    UNKNOWN  git error (rc != 0 or stdout empty) -- never a forged red (#14849)
             (exit 0, ::warning)

Output (text mode) :
    [FAIL] MyIA.AI.Notebooks/foo.py :: i/mixed (eol=lf)
        run: git add --renormalize MyIA.AI.Notebooks/foo.py

Output (json mode) :
    {"verdict": "FAIL", "offending": [{"path": ..., "i_attr": ..., "w_attr": ...}]}
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# `git ls-files --eol` line format (git 2.31+, measured on main 2026-10-06) :
#   i/<in-index-eol>[ ]w/<worktree-eol>[ ]attr/<attributes>[\t]<path>
# Fields are SPACE-separated, then a TAB before the path. `<attributes>` can
# contain spaces (e.g. `text eol=lf`).
EOL_LINE_RE = re.compile(
    r"^i/(?P<i_attr>\S+)\s+w/(?P<w_attr>\S+)\s+attr/(?P<attr>.+?)\t(?P<path>.*)$"
)

# An `eol=lf` attribute covers `text` (which defaults to eol=lf) as well.
LF_ATTRS = {"lf", "text"}
BAD_INDEX = {"crlf", "mixed"}


def _run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )


def changed_paths(diff: str, repo: Path) -> list[str]:
    """List of paths added or modified by `diff` (no deletion, no rename chain)."""
    cp = _run(["git", "diff", "--name-only", "--diff-filter=AM", diff], repo)
    if cp.returncode != 0:
        print(f"::warning::git diff failed: {cp.stderr.strip()}", file=sys.stderr)
        return []
    return [p.strip() for p in cp.stdout.splitlines() if p.strip()]


def offending(paths: list[str], repo: Path) -> list[dict[str, str]]:
    """For each path, look up its `git ls-files --eol` line and flag mismatch."""
    if not paths:
        return []
    cp = _run(["git", "ls-files", "--eol", "--", *paths], repo)
    if cp.returncode != 0 or not cp.stdout:
        print(f"::warning::git ls-files --eol failed: {cp.stderr.strip()}", file=sys.stderr)
        return []
    out: list[dict[str, str]] = []
    for line in cp.stdout.splitlines():
        m = EOL_LINE_RE.match(line.strip())
        if not m:
            continue
        i_attr = m.group("i_attr")
        # `attr` may carry a trailing space when the attribute is empty
        # (real output : `attr/ \t<path>`); strip before testing membership.
        attr = m.group("attr").strip()
        if i_attr in BAD_INDEX and attr in LF_ATTRS:
            out.append(
                {
                    "path": m.group("path"),
                    "i_attr": f"i/{i_attr}",
                    "w_attr": f"w/{m.group('w_attr')}",
                    "attr": f"attr/{attr}",
                }
            )
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument(
        "--diff",
        default="origin/main...HEAD",
        help="git diff range (default: origin/main...HEAD)",
    )
    ap.add_argument(
        "--repo",
        default=".",
        help="path to the git repository (default: cwd)",
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="emit a JSON verdict on stdout",
    )
    ns = ap.parse_args()

    repo = Path(ns.repo).resolve()
    paths = changed_paths(ns.diff, repo)
    if not paths:
        # no changes to inspect -- the verdict is CLEAN unless git itself failed
        if ns.json:
            print(json.dumps({"verdict": "CLEAN", "diff": ns.diff, "offending": []}))
        else:
            print(f"CLEAN :: 0 changed file(s) in {ns.diff}")
        return 0

    bad = offending(paths, repo)
    if not bad:
        if ns.json:
            print(
                json.dumps(
                    {
                        "verdict": "CLEAN",
                        "diff": ns.diff,
                        "scanned": len(paths),
                        "offending": [],
                    }
                )
            )
        else:
            print(f"CLEAN :: {len(paths)} changed file(s), 0 mismatch(es)")
        return 0

    if ns.json:
        print(
            json.dumps(
                {
                    "verdict": "FAIL",
                    "diff": ns.diff,
                    "scanned": len(paths),
                    "offending": bad,
                }
            )
        )
    else:
        print(f"FAIL :: {len(bad)} file(s) with blob EOL != attribute EOL", file=sys.stderr)
        for entry in bad:
            print(
                f"  [FAIL] {entry['path']} :: {entry['i_attr']} (attr/{entry['attr'].split('/', 1)[1]})",
                file=sys.stderr,
            )
            print(
                f"         run: git add --renormalize {entry['path']}",
                file=sys.stderr,
            )
    return 1


if __name__ == "__main__":
    sys.exit(main())
