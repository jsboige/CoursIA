# _paths.py — path management for argumentation_lib
#
# Replaces EPITA's path manipulation (sys.path.insert, environment_manager,
# ensure_directories_exist side-effects). This module provides path resolution
# WITHOUT import-time side effects. All functions are pure.

from __future__ import annotations

import pathlib
from typing import Optional


# Base directory = parent of argumentation_lib/ = Argument_Analysis/
LIB_DIR = pathlib.Path(__file__).parent.resolve()
ARGUMENT_ANALYSIS_DIR = LIB_DIR.parent
SYMBOLIC_AI_DIR = ARGUMENT_ANALYSIS_DIR.parent


def get_tweety_jar_dir() -> Optional[pathlib.Path]:
    """Find the directory containing Tweety JAR files.

    Only the sibling series directory holds JARs. The former first candidate,
    ``Argument_Analysis/libs/``, was removed with the #23109 arbitration: it
    carried the duplicated native libraries and no JAR at all (measured at base
    ``7e1b735ab``: six ``native/*`` entries, zero ``*.jar``), so its ``*.jar``
    guard never matched -- a pointer that looked alive and resolved to nothing.
    """
    d = SYMBOLIC_AI_DIR / "Tweety" / "libs"
    if d.exists() and any(d.glob("*.jar")):
        return d
    return None


def get_ontology_dir() -> pathlib.Path:
    """Return the ontology directory path."""
    return ARGUMENT_ANALYSIS_DIR / "ontologies"


def get_data_dir() -> pathlib.Path:
    """Return the data directory path."""
    return ARGUMENT_ANALYSIS_DIR / "data"


def get_ext_tools_dir() -> pathlib.Path:
    """Return the shared external tools directory path (canonical).

    The shared sibling-series directory ``SymbolicAI/ext_tools/`` is the
    canonical location since the #23109 arbitration: the EProver tree that
    the series-local copy held was byte-identical to the shared one and has
    been removed from the tree, so the local directory now only carries the
    tools that are NOT shared (the SPASS binary, absent from the shared
    directory).

    Resolution order:
    1. SymbolicAI/ext_tools/ (shared, canonical)
    2. Argument_Analysis/ext_tools/ (local, fallback for a checkout that
       does not carry the shared directory)

    Returns the local path when neither exists, so callers keep a writable
    target and the failure stays where it was.
    """
    candidates = [
        SYMBOLIC_AI_DIR / "ext_tools",
        ARGUMENT_ANALYSIS_DIR / "ext_tools",
    ]
    for d in candidates:
        if d.exists():
            return d
    return ARGUMENT_ANALYSIS_DIR / "ext_tools"


def get_local_ext_tools_dir() -> pathlib.Path:
    """Return the series-local external tools directory path.

    Distinct from :func:`get_ext_tools_dir`, which now points at the shared
    directory. The local directory keeps the tools that are not shared with
    the other SymbolicAI series (the SPASS binary is not present in
    ``SymbolicAI/ext_tools/``).
    """
    return ARGUMENT_ANALYSIS_DIR / "ext_tools"


def ensure_output_dirs(*dir_names: str) -> dict[str, pathlib.Path]:
    """Create output directories on demand (NOT at import time).

    Returns a dict of name -> resolved Path for each created directory.
    """
    result = {}
    for name in dir_names:
        p = ARGUMENT_ANALYSIS_DIR / name
        p.mkdir(parents=True, exist_ok=True)
        result[name] = p
    return result
