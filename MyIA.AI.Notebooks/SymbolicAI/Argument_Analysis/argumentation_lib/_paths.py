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

    Search order:
    1. Argument_Analysis/libs/ (local)
    2. Tweety/libs/ (sibling series)
    """
    candidates = [
        ARGUMENT_ANALYSIS_DIR / "libs",
        SYMBOLIC_AI_DIR / "Tweety" / "libs",
    ]
    for d in candidates:
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
    """Return the external tools directory path."""
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
