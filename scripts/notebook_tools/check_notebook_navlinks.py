#!/usr/bin/env python3
"""Check for broken notebook navigation links (`.ipynb` relative links) across the repository.

Sibling of ``scripts/check_docs_links.py``: that tool scans markdown documentation
(``CLAUDE.md``, ``docs/``, READMEs) for broken relative links; THIS tool scans the
**markdown cells of ``.ipynb`` notebooks** for broken relative links to other notebooks
(the cell-0 "Navigation" prev/next bars and in-body prerequisite links).

Motivation: after a series reorganization that moves notebooks into subdirectories
(see EPIC #5081 — narrative renumbering), relative navlinks like
``[<< 14-WeightedAstar](Search-14-WeightedAstar-Csharp.ipynb)`` silently break when the
target moved to another subdir (e.g. ``Part3-Advanced/``). ``check_docs_links.py`` cannot
catch these because it never opens ``.ipynb`` files. This tool closes that gap.

A link is reported broken when the target ``.ipynb`` (resolved relative to the source
notebook's own directory) does not exist on disk. HTTP(S) links are skipped.

Usage:
    python scripts/notebook_tools/check_notebook_navlinks.py            # scan all notebooks
    python scripts/notebook_tools/check_notebook_navlinks.py Search/    # scan one family
    python scripts/notebook_tools/check_notebook_navlinks.py --quiet    # minimal output
    python scripts/notebook_tools/check_notebook_navlinks.py --strict   # exit 1 if broken

Exit codes:
    0 = no broken navlinks (or report-only mode)
    1 = broken navlinks found AND --strict set
    2 = error during execution

NOTE: as of EPIC #5081, several Search/ notebooks carry pre-existing broken navlinks
that reference notebooks renamed during the Part1-4 reorganization. Those require the
renumbering map to resolve (pedagogical judgment, not a mechanical path fix) and are
tracked in #5081. This tool is therefore NOT yet wired to blocking CI; run it on demand
to surface drift, and adopt ``--strict`` in CI once the renumbering settles.
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

# Markdown link to a .ipynb target: [label](target.ipynb)
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+\.ipynb)\)")

# Directories / path fragments to skip (non-pedagogical, generated, or legacy)
SKIP_FRAGMENTS = (
    "_output",
    ".lake",
    "_lean",
    "/.ipynb_checkpoints",
    "/archive/",
    "partner-course",
    "MetaGeneticSharp",
)


@dataclass(frozen=True)
class BrokenNavlink:
    notebook: str   # repo-relative path of the source notebook
    cell: int       # cell index containing the broken link
    target: str     # the raw (unresolvable) link target

    def __str__(self) -> str:
        return f"{self.notebook} [cell {self.cell}] -> {self.target}"


def _should_skip(path: Path) -> bool:
    posix = path.as_posix()
    return any(frag in posix for frag in SKIP_FRAGMENTS)


def find_notebook_files(roots: list[Path]) -> list[Path]:
    """Return sorted .ipynb files under the given roots, skipping generated/legacy dirs."""
    files: list[Path] = []
    for root in roots:
        if root.is_file() and root.suffix == ".ipynb":
            if not _should_skip(root):
                files.append(root)
        else:
            for nb in sorted(root.rglob("*.ipynb")):
                if not _should_skip(nb):
                    files.append(nb)
    # De-duplicate while preserving order
    seen: set[Path] = set()
    unique: list[Path] = []
    for f in files:
        if f not in seen:
            seen.add(f)
            unique.append(f)
    return unique


def iter_navlinks(nb_path: Path):
    """Yield (cell_index, target) for each markdown link to a .ipynb in the notebook."""
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except Exception:
        return
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = "".join(cell.get("source", []))
        for m in LINK_RE.finditer(src):
            target = m.group(1)
            if target.startswith(("http://", "https://")):
                continue
            yield ci, target


def check_navlink(target: str, nb_path: Path) -> bool:
    """Return True if the target .ipynb resolves relative to the notebook's directory."""
    resolved = (nb_path.parent / target).resolve()
    return resolved.exists()


def scan(roots: list[Path]) -> list[BrokenNavlink]:
    """Scan notebooks under roots; return the list of broken navlinks."""
    broken: list[BrokenNavlink] = []
    for nb in find_notebook_files(roots):
        rel = nb.relative_to(REPO_ROOT).as_posix() if nb.is_absolute() else nb.as_posix()
        for ci, target in iter_navlinks(nb):
            if not check_navlink(target, nb):
                broken.append(BrokenNavlink(rel, ci, target))
    return sorted(broken, key=lambda b: (b.notebook, b.cell, b.target))


def format_report(broken: list[BrokenNavlink], quiet: bool = False) -> str:
    if not broken:
        return "OK: 0 broken notebook navlink(s)." if not quiet else ""
    lines = [f"BROKEN notebook navlinks: {len(broken)}"]
    if not quiet:
        for b in broken:
            lines.append(f"  {b}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("roots", nargs="*", default=[str(DEFAULT_ROOT)],
                        help="Notebook file or directory to scan (default: MyIA.AI.Notebooks/). "
                             "Paths are relative to repo root and may omit the "
                             "'MyIA.AI.Notebooks/' prefix (e.g. 'Search/' or 'GameTheory/').")
    parser.add_argument("--strict", action="store_true",
                        help="Exit 1 if any broken navlink is found (for opt-in CI).")
    parser.add_argument("--quiet", action="store_true", help="Minimal output (count only).")
    args = parser.parse_args(argv)

    roots: list[Path] = []
    for r in args.roots:
        p = Path(r)
        if not p.is_absolute():
            # Allow shorthand: 'Search/' -> 'MyIA.AI.Notebooks/Search'
            candidate = REPO_ROOT / p
            if not candidate.exists():
                candidate = DEFAULT_ROOT / p
            p = candidate
        roots.append(p)

    try:
        broken = scan(roots)
    except Exception as exc:  # pragma: no cover - defensive
        print(f"ERROR during scan: {exc}", file=sys.stderr)
        return 2

    report = format_report(broken, quiet=args.quiet)
    if report:
        print(report)
    if broken and args.strict:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
