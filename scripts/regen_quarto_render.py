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

The .ipynb notebooks of the pilot subtree (``NOTEBOOK_SUBTREES``, currently
``Search/``) ARE rendered to HTML (EPIC #10921, Phase A #10923): they are
listed explicitly with the same mechanism. Rendering consumes the committed
outputs (rule C.2) without kernel re-execution and shows the code cells: the
root ``execute`` block carries ``enabled: false`` + ``echo: true`` (measured
firsthand on the pilot: a directory-scoped ``_quarto.yml`` is NOT applied to
.ipynb documents in Quarto 1.7.32, only the root project block is).

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

# Notebooks rendered to HTML (EPIC #10921). Pilot = the Search series only
# (#10923 Phase A); extending to other series = adding a subtree here. The
# root execute block (_quarto.yml) already carries enabled: false + echo: true
# for every notebook — a directory-scoped _quarto.yml is NOT applied to .ipynb
# in Quarto 1.7.32 (measured firsthand), so no per-subtree override exists.
NOTEBOOK_SUBTREES = (
    "MyIA.AI.Notebooks/Search/",  # pilote #10923 — voir EPIC #10921 pour l'extension
)

# Notebook subtrees that must NOT render (archived families only — vendored
# subtrees are never git-tracked under these prefixes).
NOTEBOOK_EXCLUDE_MARKERS = (
    "/_archive/",
    "/archive/",
)

# Notebook files volontairement exclus du rendu HTML, avec raison mesurée.
# Pathologie pandoc 1.7.32 sous echo: true (config requise par #10923, code
# visible) : le reader ipynb boucle CPU-bound sans produire de sortie, alors
# que le meme notebook rend en 2-6 s en echo: false. Mesures (2026-08-14,
# standalone + build complet) :
#   - App-9b-EdgeDetection-CSharp.ipynb : >= 15 min sans progression
#     (outputs .NET 4.8 MB, 1061 blocs).
#   - MGS-4/-8/-9/-11/-14/-15 (MetaGeneticSharp, .net-csharp) : >= 40 s sans
#     progression (meme pathologie, independante du volume d'outputs —
#     MGS-11 ne fait que 361 KB / 22 blocs). MGS-4 confirme par le build
#     complet : hang malgre la normalisation des cellules (post-#10965).
# Voir issue #10968.
NOTEBOOK_EXCLUDE_FILES = (
    "MyIA.AI.Notebooks/Search/Applications/Hybrid/App-9b-EdgeDetection-CSharp.ipynb",
    "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-4-Islands.ipynb",
    "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-8-LandscapeExplorer.ipynb",
    "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-9-EverestRelief.ipynb",
    "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-11-IslandSynergy.ipynb",
    "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-14-IslandSynergyFound.ipynb",
    "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-15-LandscapeAnalysis.ipynb",
)


def git_tracked_notebooks() -> list[str]:
    """Return repo-relative POSIX paths of every git-tracked ``.ipynb`` under
    NOTEBOOK_SUBTREES, excluding archived subtrees.

    Same `git ls-files` + quote handling as ``git_tracked_readmes`` (raw UTF-8
    paths, single YAML wrap stays valid on every machine).
    """
    patterns = []
    for tree in NOTEBOOK_SUBTREES:
        patterns.append(tree + "*.ipynb")
        patterns.append(tree + "**/*.ipynb")
    out = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "-c", "core.quotePath=false", "ls-files", *patterns],
        capture_output=True, text=True, check=True,
    )
    paths = []
    for line in out.stdout.splitlines():
        p = line.strip()
        if not p:
            continue
        if any(bad in p for bad in NOTEBOOK_EXCLUDE_MARKERS):
            continue
        if p in NOTEBOOK_EXCLUDE_FILES:
            continue
        paths.append(p)
    # Sort for deterministic diffs (by path, case-insensitive)
    paths.sort(key=lambda s: s.lower())
    return paths


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
    # Notebooks rendered to HTML (EPIC #10921, pilote Search #10923). Explicit
    # list (globs do not expand in Quarto 1.7, see README comment above).
    notebooks = git_tracked_notebooks()
    if notebooks:
        lines.append("    # Notebooks rendus en HTML (EPIC #10921, pilote Search #10923).")
        lines.append("    # Liste explicite — globs non etendus en Quarto 1.7.")
        lines.append("    # Execution desactivee + echo: true au niveau racine (_quarto.yml).")
        lines.append(f"    # {len(notebooks)} notebooks (sous-arbres: "
                     + ", ".join(sorted(NOTEBOOK_SUBTREES)) + ").")
        for p in notebooks:
            lines.append(f'    - "{p}"')
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
        nb = len(git_tracked_notebooks())
        print(f"_quarto.yml render list up to date ({n} READMEs, {nb} notebooks).")
        return 0

    QUARTO_YML.write_text(proposed, encoding="utf-8")
    n = len(git_tracked_readmes()) + 1
    nb = len(git_tracked_notebooks())
    print(f"_quarto.yml updated: render list now includes {n} READMEs, {nb} notebooks.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
