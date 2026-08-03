"""Tests for scripts/notebook_tools/_alpha_diag.py.

Covers the three pure helper functions:
- is_papermill_injected(cell)
- is_outputless_by_design(cell)  -- AST-based, the valuable one
- count_todos(nb)

The module runs a script-level loop `for path in sys.argv[1:]` at import
time. We neutralise sys.argv at the top of this file (before import) so the
loop iterates over nothing -- no source change to _alpha_diag needed.
"""

import sys

# Neutralise the script-level `for path in sys.argv[1:]` loop so the module
# body is a no-op on import under pytest.
sys.argv = ["pytest"]

from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import importlib

_alpha = importlib.import_module("_alpha_diag")
is_papermill_injected = _alpha.is_papermill_injected
is_outputless_by_design = _alpha.is_outputless_by_design
count_todos = _alpha.count_todos

import pytest


# ---------------------------------------------------------------------------
# is_papermill_injected
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("cell,expected", [
    ({"metadata": {"tags": ["injected-parameters"]}}, True),
    ({"metadata": {"tags": ["injected-parameters", "other"]}}, True),
    ({"metadata": {"tags": ["other"]}}, False),
    ({"metadata": {"tags": []}}, False),
    ({"metadata": {}}, False),
    ({}, False),
    # not in a "tags" key elsewhere
    ({"metadata": {"papermill": {"injected-parameters": True}}}, False),
])
def test_is_papermill_injected(cell, expected):
    assert is_papermill_injected(cell) is expected


# ---------------------------------------------------------------------------
# count_todos
# ---------------------------------------------------------------------------

def _code(source, **kw):
    cell = {"cell_type": "code", "source": [source] if isinstance(source, str) else source}
    cell.update(kw)
    return cell


def _md(source):
    return {"cell_type": "markdown", "source": [source]}


def test_count_todos_empty():
    assert count_todos({"cells": []}) == 0


def test_count_todos_single():
    nb = {"cells": [_code("# TODO fix this later")]}
    assert count_todos(nb) == 1


def test_count_todos_multiple_in_one_cell():
    nb = {"cells": [_code("# TODO one\n# TODO two\nx = 1  # TODO three")]}
    assert count_todos(nb) == 3


def test_count_todos_case_insensitive():
    # implementation uses .upper() before substring count
    nb = {"cells": [_code("# todo lowercase\n# Todo mixed")]}
    assert count_todos(nb) == 2


def test_count_todos_ignores_markdown():
    nb = {"cells": [_md("# TODO in markdown"), _code("x = 1")]}
    assert count_todos(nb) == 0


def test_count_todos_substring_match():
    # "# TODOO" contains the substring "# TODO" -> counted by str.count
    nb = {"cells": [_code("# TODOO extra")]}
    assert count_todos(nb) == 1


def test_count_todos_across_cells():
    nb = {"cells": [_code("# TODO a"), _code("print(1)"), _code("# TODO b\n# TODO c")]}
    assert count_todos(nb) == 3


# ---------------------------------------------------------------------------
# is_outputless_by_design -- the AST-based detector (parametrized branches)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("source,expected", [
    # empty / whitespace -> True (nothing to output)
    ("", True),
    ("   ", True),
    ("\n\n", True),
    # all-comment -> True
    ("# comment only", True),
    ("# line one\n# line two\n", True),
    # assignments -> True (no side effect, no display)
    ("x = 5", True),
    ("x = 5\ny = 10\nz = x + y", True),
    # annotated assignment -> True (AnnAssign)
    ("x: int = 5", True),
    # function / class / async defs -> True
    ("def foo():\n    pass", True),
    ("async def f():\n    return 1", True),
    ("class Bar:\n    pass", True),
    # comment + assignment (comment stripped, only Assign remains) -> True
    ("# note\nx = 5", True),
    # ---- NOT outputless ----
    # expression statement -> False
    ("print('hi')", False),
    # mixed assignment + expression -> False
    ("x = 5\nprint(x)", False),
    # import statement (top-level Import node) -> False
    ("import os", False),
    # syntax error -> False (except SyntaxError branch)
    ("def (", False),
])
def test_is_outputless_by_design(source, expected):
    cell = {"cell_type": "code", "source": [source]}
    assert is_outputless_by_design(cell) is expected


def test_is_outputless_by_design_list_source():
    # source may be a list of lines (real ipynb format)
    cell = {"cell_type": "code", "source": ["x = 5\n", "y = 10"]}
    assert is_outputless_by_design(cell) is True


# ---------------------------------------------------------------------------
# Integration: the diagnostic logic composition (without running the script)
# ---------------------------------------------------------------------------

def test_effective_cells_without_output_logic():
    """Reproduce the core diagnostic: a cell is 'effective without output'
    when it is code, not papermill-injected, not outputless-by-design, and
    has no outputs."""
    cells = [
        _code("x = 5"),                      # outputless-by-design -> skipped
        _code("print('hi')"),                # effective but HAS output -> not blocked
        _code("print('blocked')"),           # effective, NO output -> BLOCKED
        _code("# TODO injected", metadata={"tags": ["injected-parameters"]}),
        _md("just text"),
    ]
    cells[1]["outputs"] = [{"output_type": "stream", "text": ["hi\n"]}]
    cells[3]["outputs"] = []  # injected -> skipped regardless

    blocked = []
    for i, c in enumerate(cells):
        if c["cell_type"] != "code":
            continue
        if is_papermill_injected(c) or is_outputless_by_design(c):
            continue
        if not c.get("outputs"):
            blocked.append(i)
    assert blocked == [2]
