#!/usr/bin/env python3
"""Restrict the Quarto ``project.render`` list to what a PR actually changed.

Why this exists
---------------
``quarto-pages-deploy.yml`` runs a Quarto build on every PR that touches the
render surface. Its stated purpose is narrow -- "bloque les PR qui etendent
``_quarto.yml`` / ajoutent un notebook / modifient une cellule markdown d'un
notebook rendu" -- but it implemented that purpose with a bare
``quarto render``, which renders the WHOLE site: 1192 entries, every PR, from
scratch (``_freeze/`` is not tracked, so nothing is cached between runs).

Measured on PR #14225 (run 33714385365, 2026-09-03): 25 min queued, then the
render step ran 3180 s (53 min) and was killed by the job's 60-min ceiling.
Its ``PR gate`` had already self-cancelled at 45 min waiting for that verdict
(#13510 STARVED path), leaving a required check with NO verdict and the PR
blocked. Raising the two ceilings (#14412) does not fix that: it makes each
Quarto PR hold a self-hosted slot for a full hour on a pool measured at 19/22
busy, which is the CI starvation itself.

Rendering only the changed documents makes the check proportional to the PR.

Scope decision
--------------
FULL    a changed path can affect documents it does not name (project config,
        theme, the pre-processing scripts, the workflow, or the DELETION of a
        rendered document -- which breaks links from pages still pointing at
        it). Rendering everything is the only sound answer.
SCOPED  only rendered documents were added/modified: render exactly those.
EMPTY   nothing on the render surface changed: nothing to validate.

The bias is deliberately conservative: anything not understood is FULL.

What a scoped render does NOT catch: breakage a changed file causes in an
UNCHANGED one (a cross-reference, a sidebar entry). That class is still
caught by the full render on the ``push``/deploy leg on ``main`` -- one merge
later instead of one PR earlier. That is the trade this script makes, and it
is the right way round while the alternative is a check that cannot conclude
at all.

Usage:
    python scripts/quarto_render_scope.py --base <sha> --head <sha>
    python scripts/quarto_render_scope.py --base <sha> --head <sha> --apply
    python scripts/quarto_render_scope.py --changed-from <file> --apply
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
QUARTO_YML = REPO_ROOT / "_quarto.yml"

# A change to any of these can alter the rendering of documents it does not
# name -> a scoped render would be blind to it.
FULL_RENDER_TRIGGERS = (
    "_quarto.yml",
    "styles.css",
    "favicon.ico",
    ".github/workflows/quarto-pages-deploy.yml",
)
FULL_RENDER_PREFIXES = (
    "scripts/quarto_",              # yaml_safe, csharp_kernel_fix, this file
    "scripts/regen_quarto_render",  # the list generator itself
)
FULL_RENDER_SUFFIXES = (".scss", ".css", "_metadata.yml")

_ENTRY_RE = re.compile(r'^\s*-\s*"(?P<path>[^"]+)"\s*$')
_RENDER_KEY_RE = re.compile(r"^\s{2}render:\s*$")


def render_list_entries(yml_text: str) -> list[str]:
    """Every quoted path in the project.render block, in file order."""
    entries: list[str] = []
    in_project = False
    in_render = False
    for line in yml_text.splitlines():
        if line.startswith("project:"):
            in_project = True
            continue
        if in_project and line and not line.startswith((" ", "\t", "#", "-")):
            break  # next top-level key ends the project block
        if not in_project:
            continue
        if _RENDER_KEY_RE.match(line):
            in_render = True
            continue
        if in_render:
            m = _ENTRY_RE.match(line)
            if m:
                entries.append(m.group("path"))
    return entries


def changed_files(base: str, head: str) -> list[tuple[str, str]]:
    """[(status, path)] between two commits. Status is one of A C D M R."""
    # encoding= is mandatory, not decorative (#12811): the repo carries accented
    # notebook paths, and a cp1252 host decoding git's UTF-8 output would raise
    # mid-diff -- turning a scope decision into a crashed job.
    out = subprocess.run(
        ["git", "diff", "--name-status", "--find-renames", base + "..." + head],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace",
    ).stdout
    rows: list[tuple[str, str]] = []
    for line in out.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        # For a rename git prints "R100<TAB>old<TAB>new": the NEW path renders.
        rows.append((parts[0][:1], parts[-1]))
    return rows


def decide(rows: list[tuple[str, str]], entries: list[str]) -> tuple[str, list[str], str]:
    """Return (mode, files, reason)."""
    listed = set(entries)
    for status, path in rows:
        if path in FULL_RENDER_TRIGGERS:
            return "full", [], path + " changed (project-wide effect)"
        if path.startswith(FULL_RENDER_PREFIXES):
            return "full", [], path + " changed (pre-processing script)"
        if path.endswith(FULL_RENDER_SUFFIXES):
            return "full", [], path + " changed (theme/metadata)"
        if status == "D" and path in listed:
            return "full", [], path + " deleted (link integrity)"

    # Order-preserving intersection: keep the render list's own ordering.
    changed = set(p for s, p in rows if s != "D")
    files = [e for e in entries if e in changed]
    if not files:
        return "empty", [], "no rendered document added or modified"
    return "scoped", files, "%d of %d rendered documents changed" % (len(files), len(entries))


def restrict_yaml(yml_text: str, keep: list[str]) -> str:
    """Rewrite project.render to `keep`, preserving every other project key."""
    out: list[str] = []
    in_project = False
    in_render = False
    emitted = False
    for line in yml_text.splitlines():
        if line.startswith("project:"):
            in_project = True
            out.append(line)
            continue
        if in_project and line and not line.startswith((" ", "\t", "#", "-")):
            in_project = in_render = False  # next top-level key
            out.append(line)
            continue
        if in_project and _RENDER_KEY_RE.match(line):
            in_render = True
            out.append(line)
            continue
        if in_render:
            if _ENTRY_RE.match(line) or line.lstrip().startswith("#"):
                if not emitted:
                    out.append("    # SCOPED to this PR's changed documents by")
                    out.append("    # scripts/quarto_render_scope.py -- CI only, never committed.")
                    out.extend('    - "' + p + '"' for p in keep)
                    emitted = True
                continue  # drop the original entries and their comments
            in_render = False  # a non-entry, non-comment line ends the list
        out.append(line)
    return "\n".join(out) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Scope the Quarto render list to a PR's changed documents.")
    ap.add_argument("--base", help="base commit (PR merge-base side)")
    ap.add_argument("--head", help="head commit")
    ap.add_argument("--changed-from",
                    help="read 'status<TAB>path' rows from a file instead of git")
    ap.add_argument("--apply", action="store_true",
                    help="rewrite _quarto.yml in place when mode is 'scoped'")
    ap.add_argument("--github-output", action="store_true",
                    help="also append mode/count/total to $GITHUB_OUTPUT")
    args = ap.parse_args()

    yml_text = QUARTO_YML.read_text(encoding="utf-8")
    entries = render_list_entries(yml_text)
    if not entries:
        print("::error::_quarto.yml: empty project.render list -- refusing to scope")
        return 2

    if args.changed_from:
        rows = []
        for line in Path(args.changed_from).read_text(encoding="utf-8").splitlines():
            if line.strip():
                parts = line.split("\t")
                rows.append((parts[0][:1], parts[-1]))
    else:
        if not (args.base and args.head):
            ap.error("--base and --head are required unless --changed-from is given")
        rows = changed_files(args.base, args.head)

    mode, files, reason = decide(rows, entries)
    print("[quarto-scope] mode=%s (%s)" % (mode, reason))
    for f in files:
        print("[quarto-scope]   " + f)

    if args.apply and mode == "scoped":
        QUARTO_YML.write_text(restrict_yaml(yml_text, files), encoding="utf-8")
        kept = render_list_entries(QUARTO_YML.read_text(encoding="utf-8"))
        # Positive control: the rewritten list must be exactly the selection.
        # A silent mismatch here would render the wrong set under a green check.
        if kept != files:
            print("::error::scope rewrite mismatch: wrote %d, selected %d"
                  % (len(kept), len(files)))
            return 2
        print("[quarto-scope] _quarto.yml render list: %d -> %d" % (len(entries), len(kept)))

    if args.github_output and os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as fh:
            fh.write("mode=%s\n" % mode)
            fh.write("count=%d\n" % len(files))
            fh.write("total=%d\n" % len(entries))
    return 0


if __name__ == "__main__":
    sys.exit(main())
