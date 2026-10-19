#!/usr/bin/env python
"""check_knots_extracts.py — refuse stale path extractions in KNOTS notebooks.

Implements the (A) arm of the prevention strategy in #21007 (KNOTS):
- Stale path class 1: cells that cite a Lean path (``knot_lean/...`` or
  ``Knots/<Module>.lean``) that does not exist on disk relative to the
  notebook directory.

This is a pre-commit hook. It runs on staged ``.ipynb`` files whose path
contains ``Lean/KNOTS/`` (or any other ``Lean/<series>`` cell path
configured below). It scans the cells (markdown + code) for
``lean_file_path`` candidates and fails the commit if any of them cannot
be resolved from the notebook's parent directory.

A new finding is logged as ``path:cell_NN:match`` and the hook exits 1.
On a clean tree the hook exits 0.

The baseline allows a known set of false positives via
``--allow`` (regex on match) — used to whitelist e.g. a literal string
inside a markdown example.

Scope: KNOTS-01 (c.1747). Generalisation to other Lean series
(KNOTS-02+, Lean-XX) is a follow-up tracked under #21007 voie (B).

See issue #21007 for the prevention strategy and the 3 measured classes
of stale extract.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Candidat : un chemin de fichier ``.lean`` qui ressemble à un chemin
# du projet. La regex capture :
#  - `knot_lean/.../*.lean` (relatif au cwd d'exécution du notebook)
#  - `KNOTS/.../*.lean` (relatif, forme post-4ee14af19e)
#  - `MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/...` (absolu repo)
#
# Variante historique pré-4ee14af19e NON capturée (volontaire) :
#  - `lean/Knots/...` (lowercase ``lean/`` + capital ``Knots/``) — le
#    défaut historique que ce hook ne vise pas. La convention repo
#    post-4ee14af19e est normalisée sur ``knot_lean/`` ou ``KNOTS/`` ;
#    on n'élargit pas le périmètre au-delà de ce qui est mesuré.
LEAN_PATH_RE = re.compile(
    r"""
    (?P<path>
        (?:[A-Za-z0-9_./-]*?/)?
        (?:knot_lean|KNOTS)/[A-Za-z0-9_./-]*\.lean
    )
    """,
    re.VERBOSE,
)

# Faux positifs connus (à étendre au fur et à mesure des merges).
DEFAULT_ALLOW_PATTERNS: tuple[str, ...] = ()


def iter_cells(notebook: dict) -> list[tuple[int, str, str]]:
    """Yield (cell_index, cell_type, source_text) for every cell."""
    out: list[tuple[int, str, str]] = []
    for i, cell in enumerate(notebook.get("cells", []) or []):
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        ctype = cell.get("cell_type", "?")
        out.append((i, ctype, src))
    return out


def find_lean_paths(source: str) -> list[tuple[str, int]]:
    """Return all (path, line_no) candidates found in source text."""
    out: list[tuple[str, int]] = []
    for m in LEAN_PATH_RE.finditer(source):
        path = m.group("path")
        # line_no is 1-based, computed from offset
        line_no = source.count("\n", 0, m.start()) + 1
        out.append((path, line_no))
    return out


def check_notebook(
    notebook_path: Path,
    notebook_root: Path,
    allow_patterns: tuple[str, ...],
    rel_resolve_from_repo_root: bool = False,
) -> list[str]:
    """Return a list of finding strings; empty if clean.

    rel_resolve_from_repo_root (R3 opt-in) : si True, un chemin relatif
    qui ne resout pas depuis le dossier du carnet tente un repli sur
    le repo_root. Defaut False (fail-closed) -- un chemin relatif qui
    n'existe pas dans le carnet reste un finding, sans repli. Le
    repli est opt-in parce qu'il peut masquer des chemins ../../foo
    qui ne sont valides que depuis la racine.
    """
    findings: list[str] = []
    try:
        with open(notebook_path, "r", encoding="utf-8") as f:
            nb = json.load(f)
    except (json.JSONDecodeError, OSError) as e:
        findings.append(f"{notebook_path}: cannot parse ({e})")
        return findings

    notebook_dir = notebook_path.parent

    for cell_idx, cell_type, src in iter_cells(nb):
        for path, line_no in find_lean_paths(src):
            if any(re.search(pat, path) for pat in allow_patterns):
                continue
            # Two resolution strategies:
            # 1. Absolute repo path → check directly.
            # 2. Relative path (knot_lean/...) → check relative to notebook_dir.
            #    Opt-in repli repo_root si R3 active.
            abs_candidate = notebook_root / path
            rel_candidate = notebook_dir / path
            if path.startswith("MyIA.AI.Notebooks/"):
                if not abs_candidate.exists():
                    findings.append(
                        f"{notebook_path}:cell_{cell_idx:02d}:{line_no}: "
                        f"STALE_PATH (abs) {path}"
                    )
            else:
                resolved = rel_candidate.exists()
                if not resolved and rel_resolve_from_repo_root:
                    resolved = abs_candidate.exists()
                if not resolved:
                    findings.append(
                        f"{notebook_path}:cell_{cell_idx:02d}:{line_no}: "
                        f"STALE_PATH (rel) {path}"
                    )
    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="Path to the CoursIA repo root (defaults to script's grandparent).",
    )
    parser.add_argument(
        "--allow",
        action="append",
        default=list(DEFAULT_ALLOW_PATTERNS),
        help="Regex (Python re) for path candidates to skip. Repeatable.",
    )
    parser.add_argument(
        "--path-filter",
        default=r"Lean/KNOTS/",
        help="Substring path filter — only check notebooks under this. "
        "Default: r'Lean/KNOTS/'. Pass empty string to disable filter.",
    )
    parser.add_argument(
        "--rel-resolve-from-repo-root",
        action="store_true",
        help=(
            "Opt-in (R3) : pour un chemin relatif qui ne resout pas "
            "depuis le dossier du carnet, tente un repli sur --repo-root "
            "avant de signaler STALE_PATH. Defaut off (fail-closed) : "
            "un chemin relatif qui n'existe pas dans le carnet reste "
            "un finding, sans repli. Utile pour les chemins "
            "../Knots/Foo.lean qui sont valides depuis n'importe quel "
            "sous-dossier du repo."
        ),
    )
    parser.add_argument(
        "notebooks",
        nargs="*",
        type=Path,
        help="Notebook files to check. If omitted, stdin lists paths (pre-commit).",
    )
    args = parser.parse_args(argv)

    repo_root: Path = args.repo_root.resolve()

    # pre-commit passes filenames via argv when pass_filenames:true.
    if not args.notebooks:
        # stdin mode (legacy)
        paths = [Path(line.strip()) for line in sys.stdin if line.strip()]
    else:
        paths = list(args.notebooks)

    # Filter
    if args.path_filter:
        flt = re.compile(args.path_filter)
        # Windows : ``str(Path)`` rend des antislashs (``\``) sur les
        # .ipynb crees/renommes par Git ou par pre-commit. Le filtre
        # par defaut (``Lean/KNOTS/``) est forward-slash -- applique
        # sur la forme Windows, il ne matche JAMAIS, le hook scanne 0
        # carnet et sort en rc 0 sans un mot. C'est la classe 1 stale
        # path documente par #21007. On normalise via ``as_posix()``
        # pour que le filtre forward-slash attrape les deux formes
        # (cf. test_path_filter_matches_windows_path dans le fichier
        # de tests, cas fondateur preserve).
        paths = [p for p in paths if flt.search(p.as_posix())]

    if not paths:
        return 0

    all_findings: list[str] = []
    for p in paths:
        if not p.exists():
            all_findings.append(f"{p}: file not found")
            continue
        all_findings.extend(
            check_notebook(
                p,
                repo_root,
                tuple(args.allow or ()),
                rel_resolve_from_repo_root=args.rel_resolve_from_repo_root,
            )
        )

    if all_findings:
        print(
            f"check_knots_extracts: {len(all_findings)} finding(s) — "
            "refusing commit (see #21007, prevention strategy voie A).",
            file=sys.stderr,
        )
        for f in all_findings:
            print(f"  {f}", file=sys.stderr)
        return 1

    print(
        f"check_knots_extracts: {len(paths)} notebook(s) checked, 0 findings.",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
