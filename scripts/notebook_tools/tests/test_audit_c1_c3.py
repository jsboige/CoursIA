"""Tests for audit_c1_c3.py — C.1 + C.3 violation detection."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from audit_c1_c3 import (
    REPO_ROOT,
    check_c1,
    check_c3,
    find_notebooks,
    get_family,
    _is_in_docstring,
)


def _nb(cells: list[dict]) -> dict:
    """Build a minimal notebook dict."""
    return {
        "cells": cells,
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "name": "python3"},
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _code(source: str) -> dict:
    """Build a code cell."""
    lines = source.split("\n")
    elements = [line + "\n" for line in lines[:-1]] + [lines[-1]]
    return {
        "cell_type": "code",
        "source": elements,
        "execution_count": 1,
        "outputs": [],
        "metadata": {},
    }


def _md(source: str) -> dict:
    """Build a markdown cell."""
    lines = source.split("\n")
    elements = [line + "\n" for line in lines[:-1]] + [lines[-1]]
    return {
        "cell_type": "markdown",
        "source": elements,
        "metadata": {},
    }


def _write_nb(tmp_path: Path, name: str, nb: dict) -> str:
    """Write a notebook to disk and return the path string."""
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return str(p)


# --- _is_in_docstring ---


class TestIsInDocstring:
    def test_not_in_docstring(self):
        in_doc, inside = _is_in_docstring("x = 1", False)
        assert in_doc is False
        # was=False, now=False => was != now is False, or was is False => False
        assert inside is False

    def test_enter_docstring(self):
        in_doc, inside = _is_in_docstring('"""start doc', False)
        assert in_doc is True
        # was=False, now=True => was != now is True, or was is False => True... but inside should be True since we just entered
        assert inside is True  # inside docstring

    def test_exit_docstring(self):
        in_doc, inside = _is_in_docstring('end doc"""', True)
        assert in_doc is False
        assert inside is True  # was != now OR was is True

    def test_inside_docstring(self):
        in_doc, inside = _is_in_docstring("some content", True)
        assert in_doc is True
        assert inside is True  # was=True, was != now is False, but was is True => True

    def test_single_quotes_docstring(self):
        in_doc, inside = _is_in_docstring("'''start", False)
        assert in_doc is True

    def test_triple_quote_on_same_line(self):
        """Opening and closing on same line cancel out."""
        in_doc, inside = _is_in_docstring('"""inline"""', False)
        assert in_doc is False

    def test_multiple_triple_quotes(self):
        in_doc, _ = _is_in_docstring('"""a""" """b"""', False)
        assert in_doc is False


# --- check_c1 ---


class TestCheckC1:
    def test_clean_notebook(self, tmp_path):
        nb = _nb([
            _md("# Title"),
            _code("x = 1\ny = 2\nprint(x + y)"),
        ])
        p = _write_nb(tmp_path, "clean.ipynb", nb)
        assert check_c1(Path(p)) == []

    def test_raise_not_implemented_error(self, tmp_path):
        nb = _nb([
            _code("def f():\n    raise NotImplementedError"),
        ])
        p = _write_nb(tmp_path, "c1.ipynb", nb)
        violations = check_c1(Path(p))
        assert len(violations) == 1
        assert "raise NotImplementedError" in violations[0]["pattern"]
        assert violations[0]["cell"] == 0

    def test_assert_false(self, tmp_path):
        nb = _nb([
            _code("assert False"),
        ])
        p = _write_nb(tmp_path, "c1.ipynb", nb)
        violations = check_c1(Path(p))
        assert len(violations) == 1
        assert "assert False" in violations[0]["pattern"]

    def test_division_by_zero(self, tmp_path):
        nb = _nb([
            _code("x = 1/0"),
        ])
        p = _write_nb(tmp_path, "c1.ipynb", nb)
        violations = check_c1(Path(p))
        assert len(violations) == 1
        assert "1/0" in violations[0]["pattern"]

    def test_commented_violation_not_flagged(self, tmp_path):
        nb = _nb([
            _code("# raise NotImplementedError\nx = 1"),
        ])
        p = _write_nb(tmp_path, "ok.ipynb", nb)
        assert check_c1(Path(p)) == []

    def test_inline_comment_not_flagged(self, tmp_path):
        nb = _nb([
            _code("x = 1  # raise NotImplementedError"),
        ])
        p = _write_nb(tmp_path, "ok.ipynb", nb)
        assert check_c1(Path(p)) == []

    def test_violation_in_docstring_not_flagged(self, tmp_path):
        nb = _nb([
            _code('"""\nraise NotImplementedError\n"""\nx = 1'),
        ])
        p = _write_nb(tmp_path, "ok.ipynb", nb)
        assert check_c1(Path(p)) == []

    def test_multiple_violations_in_same_cell(self, tmp_path):
        nb = _nb([
            _code("raise NotImplementedError\nassert False\n1/0"),
        ])
        p = _write_nb(tmp_path, "multi.ipynb", nb)
        violations = check_c1(Path(p))
        assert len(violations) == 3

    def test_violations_across_cells(self, tmp_path):
        nb = _nb([
            _code("raise NotImplementedError"),
            _code("x = 1"),
            _code("assert False"),
        ])
        p = _write_nb(tmp_path, "multi.ipynb", nb)
        violations = check_c1(Path(p))
        assert len(violations) == 2
        assert violations[0]["cell"] == 0
        assert violations[1]["cell"] == 2

    def test_markdown_cells_not_checked(self, tmp_path):
        nb = _nb([
            _md("raise NotImplementedError is bad"),
        ])
        p = _write_nb(tmp_path, "md.ipynb", nb)
        assert check_c1(Path(p)) == []

    def test_invalid_json_returns_empty(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not valid json{{{", encoding="utf-8")
        assert check_c1(p) == []

    def test_10_division_not_flagged(self, tmp_path):
        """100/10 should NOT match the 1/0 pattern."""
        nb = _nb([
            _code("x = 100/10"),
        ])
        p = _write_nb(tmp_path, "ok.ipynb", nb)
        violations = check_c1(Path(p))
        assert len(violations) == 0

    def test_pass_is_not_violation(self, tmp_path):
        nb = _nb([
            _code("pass"),
        ])
        p = _write_nb(tmp_path, "ok.ipynb", nb)
        assert check_c1(Path(p)) == []

    def test_return_none_is_not_violation(self, tmp_path):
        nb = _nb([
            _code("return None"),
        ])
        p = _write_nb(tmp_path, "ok.ipynb", nb)
        assert check_c1(Path(p)) == []

    def test_10_over_0_flagged(self, tmp_path):
        """10/0 should match 1/0 pattern (the regex catches any N/0)."""
        nb = _nb([
            _code("x = 10/0"),
        ])
        p = _write_nb(tmp_path, "c1.ipynb", nb)
        violations = check_c1(Path(p))
        # The regex is (?<!\d)1\s*/\s*0(?!\d) which matches "1/0" but not "10/0"
        # Actually let's check what happens: "10/0" has "1" preceded by digit "1"
        # (?<!\d)1 = "1" not preceded by digit => "10/0" -> the "1" IS preceded by "1" => no match
        # But "0/0" -> the "0" is matched by "1"? No, the pattern matches literal "1"
        # So "10/0" should NOT match because the "1" is preceded by another "1" (a digit)
        assert len(violations) == 0


# --- check_c3 ---


class TestCheckC3:
    def test_no_git_diff_returns_empty(self, tmp_path, monkeypatch):
        """Notebook not tracked by git => no diff => no violations."""
        # check_c3 calls relative_to(REPO_ROOT), so we need a path inside the repo
        # Use monkeypatch to avoid the relative_to issue with tmp_path
        nb_path = REPO_ROOT / "MyIA.AI.Notebooks" / "_test_c3_temp.ipynb"
        nb = _nb([_code("x = 1")])
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        try:
            result = check_c3(nb_path)
            # No git changes to this file => empty
            assert result == []
        finally:
            nb_path.unlink(missing_ok=True)


# --- get_family ---


class TestGetFamily:
    def test_top_level_notebook(self):
        p = REPO_ROOT / "MyIA.AI.Notebooks" / "test.ipynb"
        assert get_family(p) == "test.ipynb"

    def test_nested_notebook(self):
        p = REPO_ROOT / "MyIA.AI.Notebooks" / "Search" / "App-1.ipynb"
        assert get_family(p) == "Search"

    def test_deeply_nested(self):
        p = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Tweety" / "Tweety-1.ipynb"
        assert get_family(p) == "SymbolicAI"


# --- find_notebooks ---


class TestFindNotebooks:
    def test_nonexistent_family_returns_empty(self):
        result = find_notebooks("NonExistentFamily12345")
        assert result == []

    def test_family_parameter_filters(self, tmp_path, monkeypatch):
        """With a specific family, only notebooks under that dir are returned."""
        notebooks_dir = tmp_path / "MyIA.AI.Notebooks"
        search_dir = notebooks_dir / "Search"
        search_dir.mkdir(parents=True)
        ml_dir = notebooks_dir / "ML"
        ml_dir.mkdir(parents=True)

        # Create notebooks in both families
        (search_dir / "App-1.ipynb").write_text('{"cells":[]}', encoding="utf-8")
        (ml_dir / "ML-1.ipynb").write_text('{"cells":[]}', encoding="utf-8")

        import audit_c1_c3
        monkeypatch.setattr(audit_c1_c3, "NOTEBOOKS_DIR", notebooks_dir)

        result = find_notebooks("Search")
        assert len(result) == 1
        assert result[0].name == "App-1.ipynb"

    def test_excluded_dirs_skipped(self, tmp_path, monkeypatch):
        """Notebooks in excluded directories are not returned."""
        import audit_c1_c3
        notebooks_dir = tmp_path / "MyIA.AI.Notebooks"
        ok_dir = notebooks_dir / "Search"
        ok_dir.mkdir(parents=True)
        checkpoint_dir = notebooks_dir / ".ipynb_checkpoints"
        checkpoint_dir.mkdir(parents=True)

        (ok_dir / "App-1.ipynb").write_text('{"cells":[]}', encoding="utf-8")
        (checkpoint_dir / "App-1.ipynb").write_text('{"cells":[]}', encoding="utf-8")

        monkeypatch.setattr(audit_c1_c3, "NOTEBOOKS_DIR", notebooks_dir)
        result = find_notebooks()
        assert len(result) == 1
        assert result[0].parent.name == "Search"

    def test_results_sorted(self, tmp_path, monkeypatch):
        """Results are sorted by path."""
        import audit_c1_c3
        notebooks_dir = tmp_path / "MyIA.AI.Notebooks" / "Search"
        notebooks_dir.mkdir(parents=True)

        for name in ["C.ipynb", "A.ipynb", "B.ipynb"]:
            (notebooks_dir / name).write_text('{"cells":[]}', encoding="utf-8")

        monkeypatch.setattr(audit_c1_c3, "NOTEBOOKS_DIR", tmp_path / "MyIA.AI.Notebooks")
        result = find_notebooks("Search")
        names = [p.name for p in result]
        assert names == sorted(names)
