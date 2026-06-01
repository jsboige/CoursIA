"""Tests for validate_pr_notebooks.py — CI C.1/H.1/H.3 merge gate.

Focus: the C.1 detector must use the shared digit-bounded, comment/docstring-aware
scanner (#1505), so legitimate data like the date "21/02/2022" is no longer flagged
as a "1/0" division while a real `1/0` still fails.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from validate_pr_notebooks import validate_notebook


def _write_nb(cells, tmp_path, name="test.ipynb", kernel="python3"):
    """Write a notebook dict to a temp file and return its Path."""
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def _code(source, execution_count=1, outputs=None):
    """Build an executed code cell (exec_count + outputs set so only C.1 can fail)."""
    if isinstance(source, str):
        source = [source + "\n"]
    return {
        "cell_type": "code",
        "source": source,
        "execution_count": execution_count,
        "outputs": outputs or [],
    }


def _c1_errors(result):
    return [e for e in result["errors"] if "C.1" in e]


def test_date_literal_not_flagged_as_division(tmp_path):
    """A date like 21/02/2022 contains '1/0' as a substring but is legitimate data."""
    nb = _write_nb([_code('source_name = "Kremlin Discours 21/02/2022"')], tmp_path)
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]
    assert _c1_errors(result) == []


def test_real_division_by_zero_flagged(tmp_path):
    """A genuine 1/0 (digit-bounded) must still fail C.1."""
    nb = _write_nb([_code("x = 1/0")], tmp_path)
    result = validate_notebook(nb)
    assert not result["passed"]
    assert any("1/0" in e for e in _c1_errors(result))


def test_division_by_zero_with_spaces_flagged(tmp_path):
    """`1 / 0` with whitespace is still a division by zero."""
    nb = _write_nb([_code("y = 1 / 0")], tmp_path)
    result = validate_notebook(nb)
    assert not result["passed"]
    assert any("1/0" in e for e in _c1_errors(result))


def test_raise_not_implemented_flagged(tmp_path):
    nb = _write_nb([_code("raise NotImplementedError('todo')")], tmp_path)
    result = validate_notebook(nb)
    assert not result["passed"]
    assert any("raise NotImplementedError" in e for e in _c1_errors(result))


def test_assert_false_flagged(tmp_path):
    nb = _write_nb([_code("assert False, 'nope'")], tmp_path)
    result = validate_notebook(nb)
    assert not result["passed"]
    assert any("assert False" in e for e in _c1_errors(result))


def test_banned_pattern_in_comment_not_flagged(tmp_path):
    """A commented-out 1/0 is not executable, so it must not trip C.1."""
    nb = _write_nb([_code("x = 5  # this would be 1/0 but it is a comment")], tmp_path)
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]
    assert _c1_errors(result) == []


def test_banned_pattern_in_multiline_docstring_not_flagged(tmp_path):
    """1/0 inside a multi-line docstring is prose, not executable code.

    Note: the shared scanner tracks multi-line triple-quote state. A single-line
    `1/0` embedded in a regular string literal is a broader, pre-existing
    limitation (would need full tokenization) and is intentionally out of #1505's
    scope, which targets the date substring false positive.
    """
    src = 'def f():\n    """\n    Demonstrates the error 1/0 conceptually.\n    """\n    return 5'
    nb = _write_nb([_code(src)], tmp_path)
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]
    assert _c1_errors(result) == []


def test_clean_notebook_passes(tmp_path):
    nb = _write_nb([_code("total = 2 + 2\nprint(total)")], tmp_path)
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]
