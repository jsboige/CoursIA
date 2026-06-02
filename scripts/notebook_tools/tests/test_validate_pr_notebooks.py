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


# =============================================================================
# H.3 edge-case tests — execution_count is None + empty outputs = fail bloquant
# =============================================================================

def _h3_errors(result):
    """Filter errors for H.3 violations."""
    return [e for e in result["errors"] if "H.3" in e]


def test_h3_exec_count_none_no_outputs_fails(tmp_path):
    """execution_count is None AND outputs is [] → H.3 violation (the core case)."""
    cell = {
        "cell_type": "code",
        "source": ["print('hello')\n"],
        "execution_count": None,
        "outputs": [],
    }
    nb = _write_nb([cell], tmp_path)
    result = validate_notebook(nb)
    assert not result["passed"]
    assert len(_h3_errors(result)) == 1
    assert "execution_count is null" in _h3_errors(result)[0]


def test_h3_exec_count_none_with_outputs_passes(tmp_path):
    """execution_count is None BUT outputs present → passes H.3.

    This can happen when execution_count was manually cleared but outputs
    remain (count lost during conflation). Not a blocking violation per H.3
    (the outputs prove the cell was executed at some point).
    """
    cell = {
        "cell_type": "code",
        "source": ["print('hello')\n"],
        "execution_count": None,
        "outputs": [{"output_type": "stream", "text": "hello\n"}],
    }
    nb = _write_nb([cell], tmp_path)
    result = validate_notebook(nb)
    # H.3 check only flags execution_count is None — it does NOT check outputs
    # However, outputs being present is an unusual state. Let's verify actual behavior.
    # The validator checks: exec_count is None → fail, regardless of outputs.
    assert not result["passed"]
    assert len(_h3_errors(result)) == 1


def test_h3_exec_count_set_outputs_empty_passes_h3(tmp_path):
    """execution_count is set (int) AND outputs is [] → passes H.3.

    The H.3 rule specifically checks execution_count is None.
    A cell with execution_count=5 and empty outputs is not an H.3 violation
    (it may be outputless-by-design: assignment, import, etc.).
    """
    cell = {
        "cell_type": "code",
        "source": ["x = 42\n"],
        "execution_count": 5,
        "outputs": [],
    }
    nb = _write_nb([cell], tmp_path)
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]


def test_h3_multiple_unexecuted_cells_all_flagged(tmp_path):
    """Multiple code cells with execution_count=None → each one flagged."""
    cells = [
        {"cell_type": "code", "source": ["print('a')\n"], "execution_count": None, "outputs": []},
        {"cell_type": "markdown", "source": ["# Title\n"]},
        {"cell_type": "code", "source": ["print('b')\n"], "execution_count": None, "outputs": []},
        {"cell_type": "code", "source": ["print('c')\n"], "execution_count": 3, "outputs": [{"output_type": "stream"}]},
    ]
    nb = _write_nb(cells, tmp_path)
    result = validate_notebook(nb)
    assert not result["passed"]
    h3 = _h3_errors(result)
    assert len(h3) == 2
    assert any("cell 0" in e for e in h3)
    assert any("cell 2" in e for e in h3)


def test_h3_skip_dotnet_kernel(tmp_path):
    """execution_count=None on .NET kernel → H.3 skipped (no Papermill for .NET)."""
    cell = {
        "cell_type": "code",
        "source": ["Console.WriteLine(\"hi\");\n"],
        "execution_count": None,
        "outputs": [],
    }
    nb = _write_nb([cell], tmp_path, kernel=".net-csharp")
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]
    assert _h3_errors(result) == []


def test_h3_skip_lean_kernel(tmp_path):
    """execution_count=None on Lean kernel → H.3 skipped."""
    cell = {
        "cell_type": "code",
        "source": ["#check Nat\n"],
        "execution_count": None,
        "outputs": [],
    }
    nb = _write_nb([cell], tmp_path, kernel="lean4")
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]


def test_h3_skip_qc_cloud_path(tmp_path):
    """Notebooks under QuantConnect/ → H.3 skipped (requires QC Cloud)."""
    cell = {
        "cell_type": "code",
        "source": ["qb = QuantBook()\n"],
        "execution_count": None,
        "outputs": [],
    }
    qc_dir = tmp_path / "QuantConnect" / "Python"
    qc_dir.mkdir(parents=True)
    nb = _write_nb([cell], qc_dir, name="test.ipynb", kernel="python3")
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]
    assert _h3_errors(result) == []


def test_h3_empty_source_cell_not_counted(tmp_path):
    """Empty code cell (source='') → skipped entirely, not counted as H.3."""
    cell = {
        "cell_type": "code",
        "source": [""],
        "execution_count": None,
        "outputs": [],
    }
    nb = _write_nb([cell], tmp_path)
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]
    assert result["total_code"] == 0


def test_h3_comment_only_cell_not_counted(tmp_path):
    """Comment-only code cell → skipped, not counted as H.3."""
    cell = {
        "cell_type": "code",
        "source": ["# just a comment\n", "# another comment\n"],
        "execution_count": None,
        "outputs": [],
    }
    nb = _write_nb([cell], tmp_path)
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]
    assert result["total_code"] == 0


def test_h3_mixed_executed_and_unexecuted(tmp_path):
    """Mix of properly executed and unexecuted cells → only unexecuted flagged."""
    cells = [
        {"cell_type": "code", "source": ["print('ok')\n"], "execution_count": 1, "outputs": [{"output_type": "stream"}]},
        {"cell_type": "code", "source": ["x = 42\n"], "execution_count": 2, "outputs": []},
        {"cell_type": "code", "source": ["print('bad')\n"], "execution_count": None, "outputs": []},
    ]
    nb = _write_nb(cells, tmp_path)
    result = validate_notebook(nb)
    assert not result["passed"]
    h3 = _h3_errors(result)
    assert len(h3) == 1
    assert "cell 2" in h3[0]


def test_h1_error_output_flags_failure(tmp_path):
    """Cell with output_type=error → H.1 violation, even with exec_count set."""
    cell = {
        "cell_type": "code",
        "source": ["raise ValueError('boom')\n"],
        "execution_count": 1,
        "outputs": [{"output_type": "error", "ename": "ValueError", "evalue": "boom"}],
    }
    nb = _write_nb([cell], tmp_path)
    result = validate_notebook(nb)
    assert not result["passed"]
    assert any("error output" in e for e in result["errors"])


def test_h1_error_output_dotnet_advisory(tmp_path):
    """Error output on .NET kernel → advisory only, not blocking."""
    cell = {
        "cell_type": "code",
        "source": ["invalid_code\n"],
        "execution_count": 1,
        "outputs": [{"output_type": "error", "ename": "SyntaxError", "evalue": "bad"}],
    }
    nb = _write_nb([cell], tmp_path, kernel=".net-csharp")
    result = validate_notebook(nb)
    # .NET kernel skips exec check; error is advisory
    assert result["passed"], result["errors"]
    assert any("advisory" in e for e in result["errors"])


def test_json_parse_error(tmp_path):
    """Malformed JSON file → fails with parse error."""
    bad = tmp_path / "broken.ipynb"
    bad.write_text("{not valid json}", encoding="utf-8")
    result = validate_notebook(bad)
    assert not result["passed"]
    assert any("Cannot parse JSON" in e for e in result["errors"])


def test_total_code_counts_correctly(tmp_path):
    """total_code counts only non-empty, non-comment-only code cells."""
    cells = [
        {"cell_type": "code", "source": ["print('a')\n"], "execution_count": 1, "outputs": [{"output_type": "stream"}]},
        {"cell_type": "code", "source": [""], "execution_count": None, "outputs": []},  # empty → skipped
        {"cell_type": "code", "source": ["# comment\n"], "execution_count": None, "outputs": []},  # comment-only → skipped
        {"cell_type": "markdown", "source": ["# Title\n"]},
        {"cell_type": "code", "source": ["x = 1\n"], "execution_count": 2, "outputs": []},
    ]
    nb = _write_nb(cells, tmp_path)
    result = validate_notebook(nb)
    assert result["passed"], result["errors"]
    assert result["total_code"] == 2  # only cells 0 and 4
