"""Tests for notebook_lint.py — Unified notebook validator (C.1, C.2, structure, metadata).

Covers scan_c1_source, check_c1, check_c2, check_structure, check_metadata,
lint_notebook with synthetic notebook dicts — no I/O.

Run from the repo root:
    python -m pytest scripts/notebook_tools/tests/test_notebook_lint.py -v
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from notebook_lint import (
    C1_PATTERNS,
    _is_in_docstring,
    check_c1,
    check_c2,
    check_metadata,
    check_structure,
    lint_notebook,
    scan_c1_source,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _nb(cells, *, kernelspec=None):
    """Build a minimal notebook dict."""
    meta = {}
    if kernelspec:
        meta["kernelspec"] = kernelspec
    return {"cells": cells, "metadata": meta, "nbformat": 4, "nbformat_minor": 5}


def _code(source, *, execution_count=1, outputs=None):
    """Build a code cell."""
    if isinstance(source, str):
        source = [source]
    outs = outputs or [{"output_type": "stream", "text": ["ok"]}]
    return {
        "cell_type": "code",
        "source": source,
        "execution_count": execution_count,
        "outputs": outs,
        "metadata": {},
    }


def _md(*source):
    """Build a markdown cell."""
    lines = []
    for s in source:
        lines.extend(s if isinstance(s, list) else [s])
    return {"cell_type": "markdown", "source": lines, "metadata": {}}


# ---------------------------------------------------------------------------
# _is_in_docstring
# ---------------------------------------------------------------------------


class TestIsInDocstring:
    def test_not_in_docstring(self):
        new_state, is_inside = _is_in_docstring('x = 1', False)
        assert new_state is False
        assert is_inside is False

    def test_enter_docstring(self):
        new_state, is_inside = _is_in_docstring('"""docstring"""', False)
        # Triple quote opens and closes on same line — toggles twice → no net change
        assert new_state is False
        assert is_inside is False

    def test_enter_multiline_docstring(self):
        new_state, is_inside = _is_in_docstring('"""start', False)
        assert new_state is True
        assert is_inside is True

    def test_exit_docstring(self):
        new_state, is_inside = _is_in_docstring('end"""', True)
        assert new_state is False
        assert is_inside is True

    def test_inside_docstring(self):
        new_state, is_inside = _is_in_docstring("some content", True)
        assert new_state is True
        assert is_inside is True

    def test_single_quotes(self):
        new_state, is_inside = _is_in_docstring("'''start", False)
        assert new_state is True
        assert is_inside is True


# ---------------------------------------------------------------------------
# scan_c1_source
# ---------------------------------------------------------------------------


class TestScanC1Source:
    def test_notimplementederror(self):
        hits = scan_c1_source("raise NotImplementedError('todo')")
        assert len(hits) == 1
        assert hits[0][1] == "raise NotImplementedError"

    def test_assert_false(self):
        hits = scan_c1_source("assert False, 'not done'")
        assert len(hits) == 1
        assert hits[0][1] == "assert False"

    def test_div_zero(self):
        hits = scan_c1_source("1/0")
        assert len(hits) == 1
        assert hits[0][1] == "1/0"

    def test_clean_code(self):
        hits = scan_c1_source("x = 1\ny = 2\nprint(x + y)")
        assert hits == []

    def test_comment_line_skipped(self):
        hits = scan_c1_source("# raise NotImplementedError")
        assert hits == []

    def test_inline_comment_stripped(self):
        hits = scan_c1_source("x = 1  # raise NotImplementedError")
        assert hits == []

    def test_docstring_skipped(self):
        source = '"""\nraise NotImplementedError\n"""\nx = 1'
        hits = scan_c1_source(source)
        assert hits == []

    def test_date_not_flagged(self):
        """Dates like 21/02/2022 should NOT be flagged (digit-bounded regex)."""
        hits = scan_c1_source("date = '21/02/2022'")
        assert hits == []

    def test_fraction_not_flagged(self):
        hits = scan_c1_source("ratio = 10/3")
        assert hits == []

    def test_multiple_violations(self):
        source = "raise NotImplementedError\nassert False\nx = 1"
        hits = scan_c1_source(source)
        assert len(hits) == 2

    def test_pass_is_clean(self):
        hits = scan_c1_source("pass  # TODO student")
        assert hits == []

    def test_return_none_is_clean(self):
        hits = scan_c1_source("return None  # TODO etudiant")
        assert hits == []

    def test_print_exercise_is_clean(self):
        hits = scan_c1_source('print("Exercice a completer")')
        assert hits == []


# ---------------------------------------------------------------------------
# check_c1
# ---------------------------------------------------------------------------


class TestCheckC1:
    def test_clean_notebook(self):
        nb = _nb([
            _md("# Title"),
            _code("x = 1\nprint(x)"),
        ])
        assert check_c1(nb) == []

    def test_violation_in_code_cell(self):
        nb = _nb([
            _md("# Title"),
            _code("raise NotImplementedError"),
        ])
        violations = check_c1(nb)
        assert len(violations) == 1
        assert violations[0]["check"] == "C1"
        assert violations[0]["cell_index"] == 1

    def test_markdown_not_checked(self):
        nb = _nb([
            _md("raise NotImplementedError in text"),
        ])
        assert check_c1(nb) == []

    def test_multiple_cells(self):
        nb = _nb([
            _code("x = 1"),
            _code("assert False"),
            _code("y = 2"),
            _code("1/0"),
        ])
        violations = check_c1(nb)
        assert len(violations) == 2
        indices = [v["cell_index"] for v in violations]
        assert 1 in indices
        assert 3 in indices


# ---------------------------------------------------------------------------
# check_c2
# ---------------------------------------------------------------------------


class TestCheckC2:
    def test_all_executed(self):
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("y = 2", execution_count=2),
        ])
        assert check_c2(nb) == []

    def test_missing_execution_count(self):
        nb = _nb([
            _code("x = 1", execution_count=None),
        ])
        violations = check_c2(nb)
        assert len(violations) == 1
        assert violations[0]["check"] == "C2"

    def test_empty_code_cell_skipped(self):
        nb = _nb([
            _code("", execution_count=None),
        ])
        assert check_c2(nb) == []

    def test_comment_only_cell_skipped(self):
        nb = _nb([
            _code("# Just a comment", execution_count=None),
        ])
        assert check_c2(nb) == []

    def test_markdown_not_checked(self):
        nb = _nb([
            _md("# Title"),
        ])
        assert check_c2(nb) == []


# ---------------------------------------------------------------------------
# check_structure
# ---------------------------------------------------------------------------


class TestCheckStructure:
    def test_clean_structure(self):
        nb = _nb([
            _md("# Title"),
            _code("x = 1"),
            _md("## Section"),
            _code("y = 2"),
        ])
        assert check_structure(nb) == []

    def test_empty_code_cell(self):
        nb = _nb([
            _code(""),
        ])
        violations = check_structure(nb)
        assert any(v["reason"] == "empty code cell" for v in violations)

    def test_consecutive_code_cells_under_limit(self):
        nb = _nb([
            _code(f"x{i} = {i}") for i in range(5)
        ])
        violations = check_structure(nb)
        streak = [v for v in violations if "consecutive" in v.get("reason", "")]
        assert len(streak) == 0

    def test_consecutive_code_cells_over_limit(self):
        nb = _nb([
            _code(f"x{i} = {i}") for i in range(7)
        ])
        violations = check_structure(nb)
        streak = [v for v in violations if "consecutive" in v.get("reason", "")]
        assert len(streak) == 2  # cells 5 and 6 (0-indexed, streak >5)

    def test_empty_markdown_allowed(self):
        nb = _nb([
            _md(""),
            _code("x = 1"),
        ])
        violations = check_structure(nb)
        empty = [v for v in violations if v["reason"] == "empty code cell"]
        assert len(empty) == 0


# ---------------------------------------------------------------------------
# check_metadata
# ---------------------------------------------------------------------------


class TestCheckMetadata:
    def test_kernel_present(self):
        nb = _nb(
            [_md("# Title")],
            kernelspec={"display_name": "Python 3", "name": "python3"},
        )
        assert check_metadata(nb) == []

    def test_no_kernel(self):
        nb = _nb([_md("# Title")])
        violations = check_metadata(nb)
        assert any("no kernel" in v["reason"] for v in violations)

    def test_no_title(self):
        nb = _nb(
            [_md("Some text without heading"), _code("x = 1")],
            kernelspec={"display_name": "Python 3"},
        )
        violations = check_metadata(nb)
        assert any("no title" in v["reason"] for v in violations)

    def test_empty_notebook(self):
        nb = _nb([], kernelspec={"display_name": "Python 3"})
        # Empty notebook: no title required (len(cells) == 0)
        assert check_metadata(nb) == []

    def test_kernel_name_only(self):
        nb = _nb(
            [_md("# Title")],
            kernelspec={"name": "python3"},
        )
        assert check_metadata(nb) == []


# ---------------------------------------------------------------------------
# lint_notebook
# ---------------------------------------------------------------------------


class TestLintNotebook:
    def test_clean_notebook(self, tmp_path):
        nb = _nb(
            [
                _md("# Clean Notebook"),
                _code("x = 1"),
            ],
            kernelspec={"display_name": "Python 3"},
        )
        nb_path = tmp_path / "clean.ipynb"
        nb_path.write_text(
            '{"cells":[{"cell_type":"markdown","source":["# Clean Notebook"],"metadata":{}},'
            '{"cell_type":"code","source":["x = 1"],"execution_count":1,"outputs":[],"metadata":{}}],'
            '"metadata":{"kernelspec":{"display_name":"Python 3"}},'
            '"nbformat":4,"nbformat_minor":5}',
            encoding="utf-8",
        )
        result = lint_notebook(nb_path, {"c1", "c2", "structure", "meta"})
        assert result["violations"] == []

    def test_file_not_found(self, tmp_path):
        result = lint_notebook(tmp_path / "missing.ipynb", {"c1"})
        assert "error" in result
        assert "not found" in result["error"].lower() or "File not found" in result["error"]

    def test_invalid_json(self, tmp_path):
        nb_path = tmp_path / "bad.ipynb"
        nb_path.write_text("NOT JSON", encoding="utf-8")
        result = lint_notebook(nb_path, {"c1"})
        assert "error" in result

    def test_selective_checks(self, tmp_path):
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text(
            '{"cells":[{"cell_type":"code","source":["x = 1"],'
            '"execution_count":null,"outputs":[],"metadata":{}}],'
            '"metadata":{},'
            '"nbformat":4,"nbformat_minor":5}',
            encoding="utf-8",
        )
        # Only C1 — C2 missing execution_count should NOT be flagged
        result = lint_notebook(nb_path, {"c1"})
        assert result["violations"] == []

        # Only C2 — should flag missing execution_count
        result = lint_notebook(nb_path, {"c2"})
        assert len(result["violations"]) == 1


# ---------------------------------------------------------------------------
# C1_PATTERNS constants
# ---------------------------------------------------------------------------


class TestC1Patterns:
    def test_pattern_count(self):
        assert len(C1_PATTERNS) == 3

    def test_pattern_descriptions(self):
        descs = [desc for _, desc in C1_PATTERNS]
        assert "raise NotImplementedError" in descs
        assert "assert False" in descs
        assert "1/0" in descs


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
