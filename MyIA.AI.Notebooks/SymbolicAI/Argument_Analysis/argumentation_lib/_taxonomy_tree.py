#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/utils/taxonomy_tree.py` from
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
"""The taxonomy's parent relation, read from its ``path`` encoding (#2401).

The Argumentum CSV encodes its tree in ``path``: a dotted path's parent drops
its last segment (``"1.2.3"`` -> ``"1.2"``). The depth-1 nodes are the one case
the prefix rule cannot express: they carry a bare segment (``"1"``, ``"2"``...),
not ``"0.1"``, and their parent is the depth-0 root (``PK 0``, ``path "0"``).

Every child rule over the taxonomy reads the relation here. The local
``startswith(path + ".")`` rule found nothing under the root, and pairing it
with ``depth == parent_depth + 1`` lost the one row whose ``depth`` cell
disagrees with its path.
"""

from typing import TYPE_CHECKING, Iterable, Optional, Tuple

if TYPE_CHECKING:
    import pandas as pd


def taxonomy_root_path(rows: Iterable[Tuple[object, object]]) -> Optional[str]:
    """Return the path of the single depth-0 row, from ``(path, depth)`` pairs.

    ``None`` when the taxonomy carries no depth-0 row (test fixtures, subsets)
    or more than one: bare-segment nodes are then tops with no parent.
    """
    roots = []
    for path, depth in rows:
        try:
            if int(float(depth)) == 0:
                roots.append(str(path))
        except (TypeError, ValueError):
            continue
    return roots[0] if len(roots) == 1 else None


def taxonomy_parent_path(path: object, root_path: Optional[str]) -> Optional[str]:
    """Return the parent path of ``path``, or ``None`` for a node with no parent."""
    if path is None or path != path:  # None or NaN
        return None
    text = str(path)
    if not text or text == root_path:
        return None
    if "." in text:
        return text.rsplit(".", 1)[0]
    return root_path


def taxonomy_parent_paths(df: "pd.DataFrame") -> "pd.Series":
    """Each row's parent path in a taxonomy DataFrame (``path``/``depth``)."""
    root = (
        taxonomy_root_path(zip(df["path"], df["depth"]))
        if "depth" in df.columns
        else None
    )
    return df["path"].map(lambda path: taxonomy_parent_path(path, root))
