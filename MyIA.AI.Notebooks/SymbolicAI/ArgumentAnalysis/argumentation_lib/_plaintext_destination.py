#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/core/plaintext_destination.py` from
# the 2025-Epita-Intelligence-Symbolique project
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Source commit: ecfd9b9c (2026-09-29).
# Verbatim import rationale: see NOTICE-EPITA at the root of this directory.
#
# Verbatim integrity: file content below this header is byte-for-byte identical
# to the upstream source at the cited commit. No CoursIA modification.
#
# This module is a verbatim vendoring of the EPITA-IS tronc plugin set
# (FallacyWorkflowPlugin + ExplorationPlugin + TaxonomyNavigator) used by
# Argumentation-02-Fallacies-Detection. The Python package is renamed
# `argumentation_lib` here so that the upstream `from argumentation_analysis.X`
# imports are rewritten (via a conftest-time sys.path shim, see
# `_paths.py`) -- see NOTICE-EPITA.
#
# The vendoring covers portee 2 of issue #18391 (entonnoir taxonomique
# agentique). The Lexique (DETECTEUR_SOPHISMES, 38 entrees) shipped in
# #18506 is kept as the deterministic baseline; this file enables the
# agentic comparison path (run_guided_analysis + exploration_plugin).
"""Where corpus-derived plaintext may be written (#2738).

The dataset is tracked only in encrypted form. Several writers put its
plaintext, or text excerpts derived from it, at a path their caller chooses:
definition exports, unencrypted saves and their fallbacks, analysis traces.
A path inside a git work tree that is not ignored makes that plaintext one
``git add`` away from the history. This module is the single check those
writers call before they open the file.
"""

import subprocess
from pathlib import Path
from typing import Optional, Union

# A file name that the repository ignores wherever it is created
# (``*_unencrypted*`` in .gitignore). Default for interactive exports.
DEFAULT_PLAINTEXT_EXPORT_PATH = "./extract_definitions_unencrypted.json"


class PlaintextDestinationError(ValueError):
    """The destination could put plaintext into a git work tree."""


def _enclosing_work_tree(start: Path) -> Optional[Path]:
    """Nearest directory at or above *start* that holds a ``.git`` entry.

    ``.git`` is a directory in a main clone and a file in a linked worktree
    or a submodule; both count.
    """
    for candidate in (start, *start.parents):
        if (candidate / ".git").exists():
            return candidate
    return None


def check_plaintext_destination(path: Union[str, Path]) -> Path:
    """Return *path* resolved, or raise if plaintext written there is stageable.

    A destination outside every git work tree is accepted. Inside one, it is
    accepted only when ``git check-ignore`` says the path is ignored; a tracked
    file is never ignored, so overwriting one with plaintext is refused too.
    When git cannot answer, the write is refused: an unverified destination is
    treated as an unsafe one.
    """
    target = Path(path).resolve()
    root = _enclosing_work_tree(target.parent)
    if root is None:
        return target
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), "check-ignore", "-q", str(target)],
            capture_output=True,
            text=True,
            timeout=60,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise PlaintextDestinationError(
            f"Refusing to write plaintext to {target}: it is inside the git "
            f"work tree {root} and git could not say whether it is ignored "
            f"({exc})."
        ) from exc
    if proc.returncode == 0:
        return target
    if proc.returncode == 1:
        raise PlaintextDestinationError(
            f"Refusing to write plaintext to {target}: it is inside the git "
            f"work tree {root} and is not ignored, so it could be committed. "
            f"Write it outside the repository, or under an ignored name or "
            f"directory (for example '*_unencrypted*' or "
            f"'argumentation_analysis/evaluation/results/')."
        )
    raise PlaintextDestinationError(
        f"Refusing to write plaintext to {target}: 'git check-ignore' failed "
        f"in {root} (exit {proc.returncode}: {proc.stderr.strip()})."
    )
