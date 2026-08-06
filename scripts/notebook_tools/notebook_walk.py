"""Shared directory walker for the notebook scanners (#8650).

Eleven scanners under ``scripts/notebook_tools/`` each carried their own
``SKIP_DIRS`` set (which had drifted into three variants) and their own
``rglob`` loop. This module is the single source of truth for (a) which
directory names are out-of-scope and (b) the file-set walked by an audit.

Design notes
------------
* ``SKIP_DIRS`` is the canonical union of the 13 directory names seen across
  the eleven scanners. ``_output`` is kept as a member (belt-and-suspenders):
  it is primarily a Papermill *file* suffix (``*_output.ipynb``) handled by
  ``skip_papermill_output``, but keeping it as a directory name too is harmless
  (no tracked directory is literally named ``_output``, verified #8650) and
  preserves the two scanners (check_notebook_navlinks, check_plotly_static_risk)
  whose tests assert a ``_output/`` directory is out-of-scope.
* ``tracked_only=True`` (default) restricts the walk to git-tracked files via
  ``git ls-files``. This deterministically excludes gitignored trees that may
  nonetheless exist on disk (local ``lean-workspace/`` clones, Papermill
  ``*_output.ipynb`` artefacts) so an audit never emits a finding that no PR
  can fix. When ``git`` is unavailable (a fresh export without ``.git``, a
  tarball), the walk gracefully degrades to the plain ``SKIP_DIRS`` scan and
  warns on stderr -- modelled on ``check_notebook_navlinks._iter_notebooks``,
  the reference implementation this module generalises.
* ``tracked_only=False`` keeps the historical "everything on disk" behaviour
  for ad-hoc local-artefact audits; it must stay explicit.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

# Out-of-scope directory names (matched as any path segment). Canonical union
# of the entries that were duplicated -- and had drifted -- across the eleven
# scanners (#8650). A plain ``set`` so callers/tests can rebind/inspect it.
SKIP_DIRS = {
    ".lake",             # Lean vendored (Mathlib)
    ".git",
    "__pycache__",
    "_archives", "archive", "_archive",   # pedagogical archives (not ours to fix)
    ".ipynb_checkpoints",
    "_output",           # Papermill output dir (file suffix handled separately)
    ".pytest_cache",
    "worktrees",         # git worktrees of other sessions
    "foundry-lib",       # vendored third-party library
    ".claude",
    "node_modules",
}

# Papermill execution artefact (gitignored). Not a directory name -> filtered
# on the file suffix via ``skip_papermill_output``.
_OUTPUT_SUFFIX = "_output.ipynb"


def _git_repo_root(start: Path) -> Path | None:
    """Return the git repository root containing ``start``, or None if ``start``
    is not inside a git repo / git is unavailable."""
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=str(start.resolve()), capture_output=True, text=True, timeout=15,
        )
    except (FileNotFoundError, OSError):
        return None
    if result.returncode != 0:
        return None
    top = result.stdout.strip()
    return Path(top) if top else None


def _git_tracked_notebooks(repo_root: Path, notebooks_root: Path) -> set[str] | None:
    """Return the set of git-tracked ``*.ipynb`` paths (repo-root posix) under
    ``notebooks_root``, or None if ``git ls-files`` fails. ``notebooks_root`` is
    resolved to absolute so the pathspec is well-formed against ``repo_root``
    (which is always absolute from ``git rev-parse``) even when the caller passed
    a relative ``--root``."""
    try:
        rel = notebooks_root.resolve().relative_to(repo_root).as_posix()
    except (ValueError, OSError):
        rel = "."
    try:
        result = subprocess.run(
            ["git", "ls-files", "-z", "--", rel],
            cwd=str(repo_root), capture_output=True, text=False, timeout=120,
        )
    except (FileNotFoundError, OSError):
        return None
    if result.returncode != 0:
        return None
    entries = result.stdout.decode("utf-8", "replace").strip("\x00").split("\x00")
    return {e.replace("\\", "/") for e in entries if e.endswith(".ipynb")}


def iter_notebooks(
    notebooks_root: Path,
    *,
    family: str | None = None,
    tracked_only: bool = True,
    skip_papermill_output: bool = True,
):
    """Yield ``*.ipynb`` paths under ``notebooks_root[/<family>]``.

    Parameters
    ----------
    notebooks_root : the directory containing the family sub-tree to scan (for
        the repo, ``REPO_ROOT/MyIA.AI.Notebooks``; scanners that take a CLI
        ``--root`` pointing there pass it directly).
    family : optional top-level family under ``notebooks_root`` (e.g. "Search").
    tracked_only : if True (default), restrict to git-tracked notebooks via
        ``git ls-files`` (drops gitignored trees present on disk). Degrades to
        a plain ``SKIP_DIRS`` scan with a stderr warning when git is unavailable.
    skip_papermill_output : if True (default), drop ``*_output.ipynb`` artefacts.
    """
    base = notebooks_root / family if family else notebooks_root
    if not base.is_dir():
        return

    tracked: set[str] | None = None
    repo_root: Path | None = None
    if tracked_only:
        repo_root = _git_repo_root(notebooks_root)
        if repo_root is not None:
            tracked = _git_tracked_notebooks(repo_root, notebooks_root)
    if tracked_only and tracked is None:
        # Not in a git repo (or git missing): degrade to "all files on disk"
        # to avoid a silent false "0 finding", but warn explicitly.
        print(
            "warn: tracked_only requested but git is unavailable; "
            "falling back to full on-disk discovery (possible gitignored noise).",
            file=sys.stderr,
        )

    for nb in sorted(base.rglob("*.ipynb")):
        rel_base = nb.relative_to(base)
        if any(part in SKIP_DIRS for part in rel_base.parts):
            continue
        if skip_papermill_output and nb.name.endswith(_OUTPUT_SUFFIX):
            continue
        if tracked is not None and repo_root is not None:
            # Resolve nb to absolute for the membership check only (repo_root is
            # absolute); yield the original rglob'd path so callers that do
            # ``nb.relative_to(their_root)`` (e.g. check_plotly_static_risk with a
            # relative --root) still work.
            try:
                rel_repo = nb.resolve().relative_to(repo_root).as_posix()
            except (ValueError, OSError):
                continue
            if rel_repo not in tracked:
                continue
        yield nb
