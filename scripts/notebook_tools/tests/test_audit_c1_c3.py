"""Tests for scripts/notebook_tools/audit_c1_c3.py — C.1 + C.3 audit.

Tests focus on pure functions: _is_in_docstring, find_notebooks,
check_c1, check_c3, get_family.
"""

import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from audit_c1_c3 import (
    C1_PATTERNS,
    EXCLUDE_DIRS,
    _is_in_docstring,
    check_c1,
    check_c3,
    find_notebooks,
    get_family,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _nb(cells: list[dict], metadata: dict | None = None) -> dict:
    """Build a minimal notebook dict."""
    return {"cells": cells, "metadata": metadata or {}}


def _code(source: str, exec_count: int | None = None, outputs: list | None = None) -> dict:
    return {
        "cell_type": "code",
        "source": [source],
        "execution_count": exec_count,
        "outputs": outputs or [],
    }


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _write_nb(path: Path, cells: list[dict], metadata: dict | None = None) -> Path:
    """Write a minimal .ipynb file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# _is_in_docstring
# ---------------------------------------------------------------------------

class TestIsInDocstring:
    """Tests for the docstring tracker _is_in_docstring."""

    def test_no_docstring(self):
        in_doc, inside = _is_in_docstring("x = 1", False)
        assert in_doc is False
        assert inside is False

    def test_enter_triple_double(self):
        in_doc, inside = _is_in_docstring('"""hello', False)
        assert in_doc is True
        assert inside is True

    def test_exit_triple_double(self):
        in_doc, inside = _is_in_docstring('world"""', True)
        assert in_doc is False
        assert inside is True  # was != current -> inside True

    def test_enter_triple_single(self):
        in_doc, inside = _is_in_docstring("'''start", False)
        assert in_doc is True
        assert inside is True

    def test_complete_docstring_one_line(self):
        """Complete docstring on one line: opens and closes, ends outside."""
        in_doc, inside = _is_in_docstring('"""doc"""', False)
        assert in_doc is False  # opened and closed
        assert inside is False  # was=False, ended=False -> (False != False) or False = False

    def test_inside_docstring_line(self):
        in_doc, inside = _is_in_docstring("some content", True)
        assert in_doc is True
        assert inside is True  # was=True, still True -> (True != True) or True = True

    def test_consecutive_lines_in_doc(self):
        """Track state across multiple lines — propagates in_doc (first return)."""
        in_doc = False
        in_doc, inside = _is_in_docstring('"""opening', in_doc)
        assert in_doc is True
        assert inside is True
        in_doc, inside = _is_in_docstring("middle line", in_doc)
        assert in_doc is True
        assert inside is True
        in_doc, inside = _is_in_docstring('closing"""', in_doc)
        assert in_doc is False
        assert inside is True  # was True, now False -> inside=True
        in_doc, inside = _is_in_docstring("after", in_doc)
        assert in_doc is False
        assert inside is False  # was False, still False -> inside=False


# ---------------------------------------------------------------------------
# C1_PATTERNS
# ---------------------------------------------------------------------------

class TestC1Patterns:
    """Tests for the compiled C.1 regex patterns."""

    def test_raise_not_implemented(self):
        p = C1_PATTERNS[0][0]
        assert p.search("raise NotImplementedError")
        assert p.search("raise NotImplementedError('TODO')")
        assert p.search("  raise NotImplementedError")

    def test_assert_false(self):
        p = C1_PATTERNS[1][0]
        assert p.search("assert False")
        assert p.search("  assert False")

    def test_division_by_zero(self):
        p = C1_PATTERNS[2][0]
        assert p.search("1/0")
        assert p.search("1 / 0")
        assert p.search("return 1/0")
        # Should NOT match 21/0 or 1/07 (digits adjacent)
        assert not p.search("21/0")
        assert not p.search("1/07")
        # Should NOT match reward-notation slash-lists (win/loss/draw),
        # e.g. "+1/-1/0" or "1/0/0" — the "/" is a delimiter, not division.
        assert not p.search("+1/-1/0")
        assert not p.search("1/-1/0")
        assert not p.search("1/0/0")
        assert not p.search("1/-1/0 pour victoire J1/J2/nul")

    def test_no_false_positive_on_variants(self):
        p0, p1, p2 = [p for p, _ in C1_PATTERNS]
        # Normal code should not trigger
        assert not p0.search("x = 1")
        assert not p1.search("x = True")
        assert not p2.search("x = 1/2")

    def test_pattern_descriptions(self):
        """Each pattern has a human-readable description."""
        for pattern, desc in C1_PATTERNS:
            assert isinstance(desc, str)
            assert len(desc) > 0


# ---------------------------------------------------------------------------
# check_c1
# ---------------------------------------------------------------------------

class TestCheckC1:
    """Tests for check_c1 function."""

    def test_clean_notebook(self, tmp_path):
        nb = _nb([_code("x = 1"), _md("# Title"), _code("print('hello')")])
        p = _write_nb(tmp_path / "clean.ipynb", nb["cells"])
        assert check_c1(p) == []

    def test_raise_not_implemented_detected(self, tmp_path):
        nb = _nb([_code("raise NotImplementedError")])
        p = _write_nb(tmp_path / "bad.ipynb", nb["cells"])
        violations = check_c1(p)
        assert len(violations) == 1
        assert violations[0]["pattern"] == "raise NotImplementedError"
        assert violations[0]["cell"] == 0

    def test_assert_false_detected(self, tmp_path):
        nb = _nb([_code("assert False")])
        p = _write_nb(tmp_path / "bad.ipynb", nb["cells"])
        violations = check_c1(p)
        assert len(violations) == 1
        assert violations[0]["pattern"] == "assert False"

    def test_division_by_zero_detected(self, tmp_path):
        nb = _nb([_code("1/0")])
        p = _write_nb(tmp_path / "bad.ipynb", nb["cells"])
        violations = check_c1(p)
        assert len(violations) == 1
        assert violations[0]["pattern"] == "1/0"

    def test_multiple_violations_same_cell(self, tmp_path):
        nb = _nb([_code("raise NotImplementedError\nassert False\n1/0")])
        p = _write_nb(tmp_path / "multi.ipynb", nb["cells"])
        violations = check_c1(p)
        assert len(violations) == 3

    def test_violations_across_cells(self, tmp_path):
        nb = _nb([_code("raise NotImplementedError"), _code("assert False")])
        p = _write_nb(tmp_path / "multi_cell.ipynb", nb["cells"])
        violations = check_c1(p)
        assert len(violations) == 2
        assert violations[0]["cell"] == 0
        assert violations[1]["cell"] == 1

    def test_markdown_cells_skipped(self, tmp_path):
        nb = _nb([_md("raise NotImplementedError\nassert False")])
        p = _write_nb(tmp_path / "md.ipynb", nb["cells"])
        assert check_c1(p) == []

    def test_commented_violation_skipped(self, tmp_path):
        nb = _nb([_code("# raise NotImplementedError")])
        p = _write_nb(tmp_path / "comment.ipynb", nb["cells"])
        assert check_c1(p) == []

    def test_inline_comment_does_not_mask(self, tmp_path):
        """Code before inline comment should still be checked."""
        nb = _nb([_code("x = 1  # raise NotImplementedError")])
        p = _write_nb(tmp_path / "inline.ipynb", nb["cells"])
        assert check_c1(p) == []

    def test_inside_docstring_skipped(self, tmp_path):
        nb = _nb([_code('"""doc\nraise NotImplementedError\ndoc"""')])
        p = _write_nb(tmp_path / "docstring.ipynb", nb["cells"])
        assert check_c1(p) == []

    def test_empty_notebook(self, tmp_path):
        nb = _nb([])
        p = _write_nb(tmp_path / "empty.ipynb", nb["cells"])
        assert check_c1(p) == []

    def test_invalid_json(self, tmp_path):
        p = tmp_path / "bad_json.ipynb"
        p.write_text("not json", encoding="utf-8")
        assert check_c1(p) == []

    def test_multiline_source(self, tmp_path):
        """Source as a list of strings (standard nbformat)."""
        nb = {
            "cells": [{
                "cell_type": "code",
                "source": ["raise NotImplementedError\n"],
                "execution_count": None,
                "outputs": [],
            }]
        }
        p = _write_nb(tmp_path / "ml.ipynb", nb["cells"])
        violations = check_c1(p)
        assert len(violations) == 1

    def test_line_truncation(self, tmp_path):
        long_line = "x = " + "a" * 200
        nb = _nb([_code(f"raise NotImplementedError  # {long_line}")])
        p = _write_nb(tmp_path / "long.ipynb", nb["cells"])
        violations = check_c1(p)
        assert len(violations) == 1
        assert len(violations[0]["line"]) <= 80


# ---------------------------------------------------------------------------
# check_c3
# ---------------------------------------------------------------------------

class TestCheckC3:
    """Tests for check_c3 function — patches REPO_ROOT for tmp_path compat."""

    def test_no_git_diff(self, tmp_path):
        """No diff output -> no violations."""
        nb = _nb([_code("x = 1")])
        p = _write_nb(tmp_path / "clean.ipynb", nb["cells"])
        with patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.subprocess.run") as mock_run:
            mock_run.return_value.stdout = ""
            assert check_c3(p) == []

    def test_output_only_change(self, tmp_path):
        """Only outputs changed -> C.3 violation."""
        nb = _nb([_code("x = 1")])
        p = _write_nb(tmp_path / "out.ipynb", nb["cells"])
        diff_output = '@@ -1,1 +1,1 @@\n-"outputs": []\n+"outputs": [{"output_type": "stream"}]'
        with patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.subprocess.run") as mock_run:
            mock_run.return_value.stdout = diff_output
            violations = check_c3(p)
            assert len(violations) == 1
            assert "output-only" in violations[0]["reason"]

    def test_source_change_no_violation(self, tmp_path):
        """Source changed -> no C.3 violation even if outputs also changed."""
        nb = _nb([_code("x = 1")])
        p = _write_nb(tmp_path / "src.ipynb", nb["cells"])
        diff_output = '@@ -1,1 +1,1 @@\n-"source": ["x = 1"]\n+"source": ["x = 2"]\n-"outputs": []\n+"outputs": [{"data": 2}]'
        with patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.subprocess.run") as mock_run:
            mock_run.return_value.stdout = diff_output
            assert check_c3(p) == []

    def test_git_timeout(self, tmp_path):
        """Git timeout -> no violations (graceful)."""
        import subprocess
        nb = _nb([_code("x = 1")])
        p = _write_nb(tmp_path / "tout.ipynb", nb["cells"])
        with patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.subprocess.run") as mock_run:
            mock_run.side_effect = subprocess.TimeoutExpired(cmd="git", timeout=10)
            assert check_c3(p) == []

    def test_diff_headers_ignored(self, tmp_path):
        """+++ and --- lines should not count as changes."""
        nb = _nb([_code("x = 1")])
        p = _write_nb(tmp_path / "hdr.ipynb", nb["cells"])
        diff_output = '--- a/file.ipynb\n+++ b/file.ipynb\n@@ -1 +1 @@\n+"outputs": []'
        with patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.subprocess.run") as mock_run:
            mock_run.return_value.stdout = diff_output
            violations = check_c3(p)
            assert len(violations) == 1

    def test_execution_count_change(self, tmp_path):
        """execution_count change counts as output change."""
        nb = _nb([_code("x = 1")])
        p = _write_nb(tmp_path / "ec.ipynb", nb["cells"])
        diff_output = '@@ -1 +1 @@\n-"execution_count": null\n+"execution_count": 1'
        with patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.subprocess.run") as mock_run:
            mock_run.return_value.stdout = diff_output
            violations = check_c3(p)
            assert len(violations) == 1


# ---------------------------------------------------------------------------
# find_notebooks
# ---------------------------------------------------------------------------

class TestFindNotebooks:
    """Tests for find_notebooks discovery."""

    def test_nonexistent_family(self):
        result = find_notebooks("NONEXISTENT_FAMILY_XYZ")
        assert result == []

    def test_excluded_dirs(self, tmp_path):
        """Notebooks in excluded directories should be skipped."""
        with patch("audit_c1_c3.NOTEBOOKS_DIR", tmp_path):
            # Create notebook in excluded dir
            exc = tmp_path / ".ipynb_checkpoints"
            exc.mkdir()
            (exc / "bad.ipynb").write_text("{}", encoding="utf-8")
            # Create notebook in normal dir
            (tmp_path / "good.ipynb").write_text("{}", encoding="utf-8")
            result = find_notebooks()
            names = [p.name for p in result]
            assert "good.ipynb" in names
            assert "bad.ipynb" not in names


# ---------------------------------------------------------------------------
# get_family
# ---------------------------------------------------------------------------

class TestGetFamily:
    """Tests for get_family path extraction."""

    def test_normal_path(self):
        from audit_c1_c3 import NOTEBOOKS_DIR
        nb_path = NOTEBOOKS_DIR / "Search" / "Part1" / "test.ipynb"
        assert get_family(nb_path) == "Search"

    def test_root_notebook(self):
        from audit_c1_c3 import NOTEBOOKS_DIR
        nb_path = NOTEBOOKS_DIR / "test.ipynb"
        assert get_family(nb_path) == "test.ipynb"

    def test_path_outside_notebooks_dir(self):
        """Path not under NOTEBOOKS_DIR returns 'unknown'."""
        assert get_family(Path("/tmp/test.ipynb")) == "unknown"


# ---------------------------------------------------------------------------
# main (CLI)
# ---------------------------------------------------------------------------

class TestMainCLI:
    """Integration tests for the main CLI function."""

    def test_no_notebooks_found(self, capsys):
        from audit_c1_c3 import main
        with patch("audit_c1_c3.find_notebooks", return_value=[]), \
             patch("sys.argv", ["audit_c1_c3.py"]):
            ret = main()
            assert ret == 0
            assert "No notebooks found" in capsys.readouterr().out

    def test_all_clean(self, tmp_path, capsys):
        from audit_c1_c3 import main
        nb = _nb([_code("x = 1")])
        p = _write_nb(tmp_path / "clean.ipynb", nb["cells"])
        with patch("audit_c1_c3.find_notebooks", return_value=[p]), \
             patch("audit_c1_c3.check_c1", return_value=[]), \
             patch("audit_c1_c3.check_c3", return_value=[]), \
             patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.NOTEBOOKS_DIR", tmp_path), \
             patch("sys.argv", ["audit_c1_c3.py"]):
            ret = main()
            assert ret == 0
            assert "All clear" in capsys.readouterr().out

    def test_violations_exit_code_1(self, tmp_path, capsys):
        from audit_c1_c3 import main
        nb = _nb([_code("raise NotImplementedError")])
        p = _write_nb(tmp_path / "bad.ipynb", nb["cells"])
        with patch("audit_c1_c3.find_notebooks", return_value=[p]), \
             patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.NOTEBOOKS_DIR", tmp_path), \
             patch("sys.argv", ["audit_c1_c3.py"]):
            ret = main()
            assert ret == 1

    def test_json_output(self, tmp_path, capsys):
        from audit_c1_c3 import main
        nb = _nb([_code("raise NotImplementedError")])
        p = _write_nb(tmp_path / "bad.ipynb", nb["cells"])
        with patch("audit_c1_c3.find_notebooks", return_value=[p]), \
             patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.NOTEBOOKS_DIR", tmp_path), \
             patch("sys.argv", ["audit_c1_c3.py", "--json"]):
            ret = main()
            assert ret == 1
            output = capsys.readouterr().out
            parsed = json.loads(output)
            assert "total_notebooks" in parsed
            assert parsed["total_notebooks"] == 1

    def test_summary_output(self, tmp_path, capsys):
        from audit_c1_c3 import main
        nb = _nb([_code("x = 1")])
        p = _write_nb(tmp_path / "good.ipynb", nb["cells"])
        with patch("audit_c1_c3.find_notebooks", return_value=[p]), \
             patch("audit_c1_c3.check_c1", return_value=[]), \
             patch("audit_c1_c3.check_c3", return_value=[]), \
             patch("audit_c1_c3.REPO_ROOT", tmp_path), \
             patch("audit_c1_c3.NOTEBOOKS_DIR", tmp_path), \
             patch("sys.argv", ["audit_c1_c3.py", "--summary"]):
            ret = main()
            assert ret == 0
            output = capsys.readouterr().out
            assert "Family" in output
            assert "Total" in output
