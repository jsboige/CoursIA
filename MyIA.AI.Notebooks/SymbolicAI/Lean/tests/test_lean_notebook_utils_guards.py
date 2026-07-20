"""Tests for the degenerate-input guards in ``lean_notebook_utils``.

Run with: pytest SymbolicAI/Lean/tests/test_lean_notebook_utils_guards.py -v

Same bug-class as the c.703/c.704 guards on ``draw_search_tree`` /
``draw_csp_graph`` (Search) and the WFC entry-point guards (#7551/#7553):
public entry points must reject degenerate arguments (None, wrong type,
empty) at the boundary with a clear ``TypeError``/``ValueError``, rather
than crash deeper in the pipeline with an opaque ``AttributeError``
(``NoneType has no attribute 'resolve'``) or ``TypeError`` (``Path / None``)
that points at an implementation line instead of the caller's bad argument.

The module is consumed by 5 Lean notebooks (Lean-7b, Lean-13 Kochen-Specker,
Lean-16a/16b/16f Conway) which call these functions with values derived from
notebook parameters; a bad parameter deserves an actionable error, not an
opaque traceback.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import lean_notebook_utils as u  # noqa: E402


# --- _require_str helper ----------------------------------------------------

def test_require_str_rejects_none():
    with pytest.raises(TypeError, match="must be a non-empty string"):
        u._require_str("x", None)


def test_require_str_rejects_int():
    with pytest.raises(TypeError, match="got int"):
        u._require_str("x", 5)


def test_require_str_rejects_empty_and_whitespace():
    with pytest.raises(ValueError, match="non-empty"):
        u._require_str("x", "")
    with pytest.raises(ValueError, match="non-empty"):
        u._require_str("x", "   ")


def test_require_str_accepts_valid():
    assert u._require_str("x", "ok") == "ok"


# --- find_lean_project ------------------------------------------------------

def test_find_lean_project_none_raises_typeerror():
    """``project_name=None`` used to crash on ``current / None`` (opaque TypeError)."""
    with pytest.raises(TypeError, match="project_name must be a non-empty string"):
        u.find_lean_project(None)


def test_find_lean_project_int_raises_typeerror():
    with pytest.raises(TypeError, match="got int"):
        u.find_lean_project(42)


def test_find_lean_project_empty_raises_valueerror():
    with pytest.raises(ValueError, match="non-empty"):
        u.find_lean_project("")


# --- win_to_wsl -------------------------------------------------------------

def test_win_to_wsl_none_raises_typeerror():
    """``win_path=None`` used to crash on ``None.resolve()`` (opaque AttributeError)."""
    with pytest.raises(TypeError, match="win_path must be a Path or str"):
        u.win_to_wsl(None)


def test_win_to_wsl_int_raises_typeerror():
    with pytest.raises(TypeError, match="got int"):
        u.win_to_wsl(123)


def test_win_to_wsl_accepts_path_and_str():
    # Happy path preserved: both Path and str inputs are accepted (the guard
    # made win_to_wsl MORE permissive by normalizing str -> Path, not less).
    assert isinstance(u.win_to_wsl(Path("C:/tmp/x")), str)
    assert isinstance(u.win_to_wsl("D:/proj"), str)


# --- run_lake ---------------------------------------------------------------

def test_run_lake_args_none_raises_typeerror():
    """``args=None`` used to either crash on ``args.split()`` (native) or silently
    build ``lake None`` (WSL). Either way the caller got no actionable error."""
    with pytest.raises(TypeError, match="args must be a non-empty string"):
        u.run_lake("dummy_project_path", None)


def test_run_lake_args_empty_raises_valueerror():
    with pytest.raises(ValueError, match="non-empty"):
        u.run_lake("dummy", "")


# --- run_lean_snippet -------------------------------------------------------

def test_run_lean_snippet_none_raises_typeerror():
    """``snippet=None`` used to crash inside ``textwrap.dedent(None)`` (opaque)."""
    with pytest.raises(TypeError, match="snippet must be a non-empty string"):
        u.run_lean_snippet("dummy", None)


def test_run_lean_snippet_int_raises_typeerror():
    with pytest.raises(TypeError, match="got int"):
        u.run_lean_snippet("dummy", 123)


# --- count_sorry ------------------------------------------------------------

def test_count_sorry_project_path_none_raises_typeerror():
    """``project_path=None`` used to crash on ``os.path.join(None, ...)`` (native)
    or silently build ``cd None && grep`` (WSL)."""
    with pytest.raises(TypeError, match="project_path must be a non-empty string"):
        u.count_sorry(None)


def test_count_sorry_empty_raises_valueerror():
    with pytest.raises(ValueError, match="non-empty"):
        u.count_sorry("")


# --- read_lean_module -------------------------------------------------------

def test_read_lean_module_module_path_none_raises_typeerror():
    """``module_path=None`` used to crash on ``project_dir / None`` (opaque TypeError)."""
    with pytest.raises(TypeError, match="module_path must be a non-empty string"):
        u.read_lean_module("dummy_project", None)


def test_read_lean_module_empty_raises_valueerror():
    with pytest.raises(ValueError, match="non-empty"):
        u.read_lean_module("dummy_project", "")


# --- display_lean_module ----------------------------------------------------

def test_display_lean_module_highlight_int_raises_typeerror():
    """``highlight=5`` (a bare int instead of a list of ints) used to crash
    opaquely inside ``set(5)`` -> ``TypeError: int object is not iterable``."""
    with pytest.raises(TypeError, match="highlight must be an iterable"):
        u.display_lean_module("dummy_project", "dummy.lean", highlight=5)


def test_display_lean_module_highlight_none_accepted():
    """``highlight=None`` (the default) must remain valid -- the guard only
    rejects NON-iterable values, not the documented None sentinel."""
    # This calls into find_lean_project('dummy_project') which raises
    # FileNotFoundError -- that's fine, we only assert the highlight guard
    # itself did NOT raise a TypeError.
    with pytest.raises(FileNotFoundError):
        u.display_lean_module("dummy_project", "dummy.lean", highlight=None)


def test_display_lean_module_highlight_list_accepted():
    # A list/tuple/set of ints is the documented contract -- must pass the guard.
    with pytest.raises(FileNotFoundError):
        u.display_lean_module("dummy_project", "dummy.lean", highlight=[1, 3, 5])
