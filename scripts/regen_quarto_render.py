#!/usr/bin/env python3
"""Regenerate the Quarto ``project.render`` list in ``_quarto.yml``.

Quarto 1.7 does not expand ``**/README.md`` globs across nested directories in
``project.render`` (the glob matches only the root file). To render every
README of the pedagogical tree as HTML (Axe C of #4211, validated user
2026-07-05), we list every git-tracked ``README.md`` explicitly.

This script is idempotent: it rewrites only the ``project.render`` block,
preserving the rest of ``_quarto.yml`` byte-for-byte. It is meant to be run:
  - locally before ``quarto render`` (a developer check),
  - on CI as a pre-render step of ``quarto-pages-deploy.yml`` (so new READMEs
    appear on the site without a manual regen commit).

Since EPIC #10921 (pilot Phase A #10923), the ``Search/`` notebook series is
additionally rendered as HTML: ``notebook-preview: false`` only governs the
preview of an embedded notebook, not membership in the render list, and
``freeze: auto`` keeps CI from executing any kernel (outputs are committed,
rule C.2). The series-specific ``echo: true`` / ``execute: enabled: false``
override lives in ``MyIA.AI.Notebooks/Search/_metadata.yml`` — a
directory-level metadata file, NOT ``_quarto.yml`` (a nested ``_quarto.yml``
would create a nested Quarto project boundary and hijack the site render
into sidecar HTML next to the sources).

Usage:
    python scripts/regen_quarto_render.py            # rewrite _quarto.yml in place
    python scripts/regen_quarto_render.py --check    # exit 1 if drift (CI guard)
"""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
QUARTO_YML = REPO_ROOT / "_quarto.yml"

# Files always rendered first (landing pages). Order matters for build log only.
LANDING_PAGES = [
    "*.qmd",
    "MyIA.AI.Notebooks/index.qmd",
    "MyIA.AI.Notebooks/Search/index.qmd",
    "MyIA.AI.Notebooks/Sudoku/index.qmd",
    "MyIA.AI.Notebooks/GameTheory/index.qmd",
    "MyIA.AI.Notebooks/Probas/index.qmd",
    "docs/index.qmd",
]

# READMEs in vendored / archived / LFS subtrees that must NOT render.
# - vendored: external Lean/Foundry libs (not our content)
# - archived: internal history (docs/archive, _archive-*, */archive/) — these
#   often start with '---' which Quarto mis-parses as YAML front-matter, and
#   they add no pedagogical value to the public site anyway.
EXCLUDE_MARKERS = (
    ".lake/packages",      # vendored Lean Mathlib checkouts
    "foundry-lib/lib",     # vendored Foundry lib
    "docs/archive",        # internal suivi history
    "_archive-",           # archived docker configs / snapshots
    "/archive/",           # any archive/ subdir (notebook families, scripts)
    "\\archive\\",
)


# Notebook series rendered as HTML (EPIC #10921, pilot Phase A #10923).
# Quarto 1.7 expands ``**`` for .ipynb globs in project.render — matching both
# direct children and nested subdirectories (validated locally against
# 1.7.32). Per-series globs instead of ``Search/**``: the single glob would
# also match ``Search/_archive`` (internal history, excluded like the README
# archives above) and stay readable in the diff. The subtree override
# (echo: true, execute: enabled: false) lives in
# ``MyIA.AI.Notebooks/Search/_metadata.yml`` (directory-level metadata).
NOTEBOOK_RENDER_GLOBS = [
    "MyIA.AI.Notebooks/Search/Part1-Foundations/**/*.ipynb",
    "MyIA.AI.Notebooks/Search/Part2-CSP/**/*.ipynb",
    "MyIA.AI.Notebooks/Search/Part3-Advanced/**/*.ipynb",
    "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/**/*.ipynb",
    "MyIA.AI.Notebooks/Search/Applications/**/*.ipynb",
]

# Notebooks excluded from the render via ``!`` negation (applied after the
# positive globs). Each carries a GIF image embedded as a base64 data URI in a
# ``text/html`` output cell of 212-795 KB: the Quarto/pandoc 1.7 renderer hangs
# indefinitely on it (isolated repro: solo ``quarto render`` times out at 150s,
# rc=124; the same notebook without that single output renders in seconds.
# Boundary probed: <=24 KB renders fine, >=212 KB hangs). The ``.ipynb`` files
# stay served raw by the site (status quo for them). Lifting one exclusion
# requires first fixing the renderer hang (output externalization or a Quarto
# filter), tracked on EPIC #10921 Phase B.
NOTEBOOK_EXCLUDE_GLOBS = [
    "!MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-4-Islands.ipynb",
    "!MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-8-LandscapeExplorer.ipynb",
    "!MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-9-EverestRelief.ipynb",
    "!MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-11-IslandSynergy.ipynb",
    "!MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-13-LandscapeDebias.ipynb",
    "!MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-14-IslandSynergyFound.ipynb",
    "!MyIA.AI.Notebooks/Search/Applications/Hybrid/App-9b-EdgeDetection-CSharp.ipynb",
]


def git_tracked_readmes() -> list[str]:
    """Return repo-relative POSIX paths of every git-tracked README.md,
    excluding vendored and archived subtrees."""
    # `-c core.quotePath=false`: without it, git quotes non-ASCII paths
    # (accents/spaces) as "\303\251..." AND wraps them in double-quotes under
    # CI's default core.quotePath=true. The emitter below wraps again -> doubled
    # quotes ("" ... "") -> broken YAML in _quarto.yml (CI Quarto Pages Deploy
    # failure since 2026-07-05). Forcing false yields raw UTF-8 paths, so the
    # single wrap below stays valid YAML on every machine (CI or local).
    out = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "-c", "core.quotePath=false", "ls-files", "*README.md"],
        capture_output=True, text=True, check=True,
    )
    paths = []
    for line in out.stdout.splitlines():
        p = line.strip()
        if not p or p == "README.md":
            continue  # root handled separately (added with explicit form)
        # Skip vendored / archived subtrees
        if any(bad in p for bad in EXCLUDE_MARKERS):
            continue
        paths.append(p)
    # Sort for deterministic diffs (by path, case-insensitive)
    paths.sort(key=lambda s: s.lower())
    return paths


def build_render_block() -> list[str]:
    """Build the YAML lines for the project.render list."""
    lines = ["project:", "  type: site", "  output-dir: _site", "  render:"]
    # Landing pages (qmd) with a header comment
    lines.append("    # Landing pages (.qmd).")
    for entry in LANDING_PAGES:
        lines.append(f'    - "{entry}"')
    # READMEs (explicit list — globs do not expand in Quarto 1.7, see header)
    readmes = git_tracked_readmes()
    lines.append("    # README.md rendus en HTML (Axe C #4211). Liste explicite")
    lines.append("    # (regeneree par scripts/regen_quarto_render.py) car Quarto 1.7")
    lines.append("    # n'etend pas le glob **/README.md sur les sous-repertoires.")
    lines.append("    # Archives et libs vendored EXCLUES (history interne, non pedagogique).")
    lines.append(f"    # {len(readmes) + 1} READMEs (racine + arborescence, hors archives).")
    lines.append('    - "README.md"')
    for p in readmes:
        lines.append(f'    - "{p}"')
    # Notebooks .ipynb rendus en HTML (pilote Phase A #10923).
    lines.append("    # Notebooks .ipynb rendus en HTML (EPIC #10921, pilote Phase A #10923).")
    lines.append("    # Globs par sous-serie (pas Search/**) : exclut Search/_archive.")
    lines.append(f"    # {len(NOTEBOOK_RENDER_GLOBS)} globs de serie.")
    for g in NOTEBOOK_RENDER_GLOBS:
        lines.append(f'    - "{g}"')
    # Notebooks excluded via ! negation (renderer hang, see NOTEBOOK_EXCLUDE_GLOBS).
    lines.append("    # 7 notebooks exclu du rendu : output image GIF encode en base64 dans un")
    lines.append("    # output text/html de 212 a 795 KB -> le renderer Quarto/pandoc 1.7 boucle")
    lines.append("    # indefiniment (repro isolee : solo render timeout 150s, rc=124 ; sans cet")
    lines.append("    # output le notebook rend en quelques secondes). Seuil : <=24 KB OK,")
    lines.append("    # >=212 KB hang. Les fichiers .ipynb restent servis bruts (statu quo).")
    for g in NOTEBOOK_EXCLUDE_GLOBS:
        lines.append(f'    - "{g}"')
    return lines


def replace_render_block(yml_text: str, new_block_lines: list[str]) -> str:
    """Replace the project: {...} block at the top of _quarto.yml.

    The block runs from the first ``project:`` line up to (but not including)
    the next top-level key (``site:``). Everything after is preserved.
    """
    lines = yml_text.splitlines(keepends=True)
    start = None
    end = len(lines)
    top_keys = ("site:", "format:", "execute:", "lang:", "notebook-preview:",
                "editor:", "website:", "book:", "manuscript:", "server:")
    for i, line in enumerate(lines):
        if line.startswith("project:"):
            start = i
            continue
        if start is not None and line and not line.startswith((" ", "\t", "#", "-")):
            if any(line.startswith(k) for k in top_keys):
                end = i
                break
    if start is None:
        raise SystemExit("_quarto.yml: no 'project:' block found")
    # Rebuild: new block + original tail (from `end` onward)
    new_block = "\n".join(new_block_lines) + "\n"
    tail = "".join(lines[end:])
    return new_block + tail


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if _quarto.yml render list is stale")
    args = ap.parse_args()

    new_block = build_render_block()
    current = QUARTO_YML.read_text(encoding="utf-8")
    proposed = replace_render_block(current, new_block)

    if args.check:
        if proposed != current:
            print("::error::_quarto.yml render list is stale. "
                  "Run: python scripts/regen_quarto_render.py", file=sys.stderr)
            return 1
        n = len(git_tracked_readmes()) + 1
        print(f"_quarto.yml render list up to date ({n} READMEs).")
        return 0

    QUARTO_YML.write_text(proposed, encoding="utf-8")
    n = len(git_tracked_readmes()) + 1
    print(f"_quarto.yml updated: render list now includes {n} READMEs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
