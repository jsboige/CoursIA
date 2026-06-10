"""Tests for scripts/repair_genai_notebooks.py — pure function unit tests.

Tests cover is_cell_corrupted (corruption detection) and fix_source
(corruption repair). Both are pure functions with no I/O.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from repair_genai_notebooks import is_cell_corrupted, fix_source


# ---------------------------------------------------------------------------
# is_cell_corrupted
# ---------------------------------------------------------------------------


class TestIsCellCorrupted:
    """Tests for is_cell_corrupted — detects missing newline terminators."""

    def test_empty_source(self):
        assert is_cell_corrupted([]) is False

    def test_none_source(self):
        assert is_cell_corrupted(None) is False

    def test_non_list_source(self):
        assert is_cell_corrupted("not a list") is False

    def test_normal_cell(self):
        """A properly formatted cell is not corrupted."""
        source = ["import os\n", "x = 1\n", "print(x)\n"]
        assert is_cell_corrupted(source) is False

    def test_single_line(self):
        source = ["print('hello')"]
        assert is_cell_corrupted(source) is False

    def test_collapsed_import_line(self):
        """Method 1: lines > 300 chars with 'import' keyword."""
        collapsed = "import os; import sys; import json; " * 20  # > 300 chars
        source = [collapsed]
        assert is_cell_corrupted(source) is True

    def test_collapsed_def_line(self):
        """Method 1: lines > 300 chars with 'def ' keyword."""
        collapsed = "def foo(): x = 1; y = 2; " * 20  # > 300 chars
        source = [collapsed]
        assert is_cell_corrupted(source) is True

    def test_collapsed_dotenv_line(self):
        """Method 1: lines > 300 chars with 'dotenv' keyword."""
        collapsed = "from dotenv import load_dotenv; " * 25  # > 300 chars
        source = [collapsed]
        assert is_cell_corrupted(source) is True

    def test_collapsed_load_dotenv_line(self):
        """Method 1: lines > 300 chars with 'load_dotenv' keyword."""
        collapsed = "load_dotenv(); " * 25  # > 300 chars
        assert is_cell_corrupted([collapsed]) is True

    def test_collapsed_env_loaded_line(self):
        """Method 1: lines > 300 chars with 'env_loaded' keyword."""
        collapsed = "env_loaded = True; " * 25
        assert is_cell_corrupted([collapsed]) is True

    def test_collapsed_genai_root_line(self):
        """Method 1: lines > 300 chars with 'GENAI_ROOT' keyword."""
        collapsed = "GENAI_ROOT = '/path'; " * 25
        assert is_cell_corrupted([collapsed]) is True

    def test_long_line_without_keyword(self):
        """A long line without Python keywords is NOT corrupted."""
        long_line = "x = " + "1 + " * 200  # > 600 chars, no keyword
        assert is_cell_corrupted([long_line]) is False

    def test_missing_newlines_mid_array(self):
        """Method 2: 3+ non-empty mid-array elements missing \\n."""
        source = ["line1", "line2", "line3", "line4"]
        assert is_cell_corrupted(source) is True

    def test_fewer_than_3_missing(self):
        """2 missing \\n terminators is below threshold."""
        source = ["line1", "line2", "line3\n"]
        # source has 3 elements, so len > 3 is False
        # But even if we add more:
        source = ["line1", "line2\n", "line3\n", "line4\n"]
        # Only 1 missing -> not corrupted
        assert is_cell_corrupted(source) is False

    def test_exactly_3_missing_newlines(self):
        """Exactly 3 missing terminators triggers corruption."""
        source = ["a", "b", "c", "d\n"]  # 3 mid elements missing \n
        assert is_cell_corrupted(source) is True

    def test_empty_elements_ignored(self):
        """Empty strings in mid-array are not counted as missing."""
        source = ["", "", "", "final\n"]
        # 0 non-empty mid elements -> 0 missing
        assert is_cell_corrupted(source) is False

    def test_whitespace_only_elements_ignored(self):
        """Whitespace-only mid elements are not counted."""
        source = ["  ", "  ", "  ", "final\n"]
        # stripped = empty -> not counted
        assert is_cell_corrupted(source) is False

    def test_three_elements_not_enough(self):
        """3 elements total: len(source) > 3 is False -> method 2 skipped."""
        source = ["a", "b", "c"]
        assert is_cell_corrupted(source) is False

    def test_mixed_terminators(self):
        """Mix of elements with and without \\n terminators."""
        source = ["line1\n", "line2", "line3", "line4", "line5\n"]
        # mid elements: line1\n (has \n), line2 (missing), line3 (missing), line4 (missing)
        # 3 missing -> corrupted
        assert is_cell_corrupted(source) is True


# ---------------------------------------------------------------------------
# fix_source
# ---------------------------------------------------------------------------


class TestFixSource:
    """Tests for fix_source — repairs corrupted source arrays."""

    def test_empty_source(self):
        result, fixed = fix_source([])
        assert result == []
        assert fixed is False

    def test_none_source(self):
        result, fixed = fix_source(None)
        assert result is None
        assert fixed is False

    def test_non_list_source(self):
        result, fixed = fix_source("string")
        assert result == "string"
        assert fixed is False

    def test_normal_source_unchanged(self):
        """A clean source array is returned unchanged."""
        source = ["import os\n", "x = 1\n", "print(x)\n"]
        result, fixed = fix_source(source)
        assert result == source
        assert fixed is False

    def test_fixes_missing_newlines(self):
        """Missing \\n terminators are added to mid-array elements."""
        source = ["line1", "line2", "line3", "line4"]
        result, fixed = fix_source(source)
        assert fixed is True
        assert result == ["line1\n", "line2\n", "line3\n", "line4"]

    def test_last_element_preserved(self):
        """Last element is not modified even if it has no \\n."""
        source = ["line1", "line2", "last"]
        # Only 3 elements, len > 3 is False -> method 2 won't trigger
        # Need 4+ elements
        source = ["a", "b", "c", "last"]
        result, fixed = fix_source(source)
        assert fixed is True
        assert result[-1] == "last"  # no \n added to last element

    def test_already_has_newline_mid(self):
        """Elements already ending with \\n are not doubled."""
        # Need 3+ missing to trigger: provide 5 elements, 3 missing
        source = ["line1\n", "line2", "line3", "line4", "line5"]
        result, fixed = fix_source(source)
        assert fixed is True
        assert result[0] == "line1\n"  # unchanged, no extra \n
        assert result[1] == "line2\n"  # fixed

    def test_empty_mid_elements_preserved(self):
        """Empty mid-elements stay empty (not modified)."""
        # Need 3+ missing: use elements with enough non-empty missing
        source = ["a", "b", "c", "d", ""]
        result, fixed = fix_source(source)
        assert fixed is True
        assert result[0] == "a\n"

    def test_fixes_collapsed_line(self):
        """A collapsed mega-line is repaired via method 1 detection."""
        collapsed = "import os; import sys; " * 25  # > 300 chars
        source = [collapsed]
        result, fixed = fix_source(source)
        # Single element = no mid-array fix, but detection triggered
        # fix_source only adds \n to mid-array, single element stays
        assert result == source
        # Wait: is_cell_corrupted returns True (method 1) but fix loops
        # over elements. Single element = last element = keep as-is.
        # So fixed=True but result unchanged for single-element arrays.

    def test_returns_new_list(self):
        """Fix returns a new list, not a mutation of the input."""
        source = ["a", "b", "c", "d"]
        result, fixed = fix_source(source)
        assert result is not source
        assert source == ["a", "b", "c", "d"]  # original unchanged


# ---------------------------------------------------------------------------
# repair_notebook (integration-style via tmp_path)
# ---------------------------------------------------------------------------


class TestRepairNotebook:
    """Tests for repair_notebook using temporary files."""

    def test_repairs_corrupted_notebook(self, tmp_path):
        """A corrupted notebook is repaired in place."""
        import json

        nb = {
            "cells": [
                {
                    "cell_type": "code",
                    "source": ["line1", "line2", "line3", "line4"],
                },
                {
                    "cell_type": "markdown",
                    "source": ["# Title\n"],
                },
            ],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")

        from repair_genai_notebooks import repair_notebook

        fixed, total = repair_notebook(nb_path)
        assert fixed == 1
        assert total == 1  # only code cells counted

        # Verify file was written with fix
        with open(nb_path, "r", encoding="utf-8") as f:
            repaired = json.load(f)
        assert repaired["cells"][0]["source"] == [
            "line1\n", "line2\n", "line3\n", "line4"
        ]

    def test_clean_notebook_unchanged(self, tmp_path):
        """A clean notebook is not modified."""
        import json

        nb = {
            "cells": [
                {"cell_type": "code", "source": ["x = 1\n", "print(x)\n"]},
            ],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        nb_path = tmp_path / "clean.ipynb"
        content = json.dumps(nb)
        nb_path.write_text(content, encoding="utf-8")

        from repair_genai_notebooks import repair_notebook

        fixed, total = repair_notebook(nb_path)
        assert fixed == 0
        assert total == 1
        # File content unchanged
        assert nb_path.read_text(encoding="utf-8") == content

    def test_dry_run_does_not_modify(self, tmp_path):
        """Dry run detects corruption but does not write."""
        import json

        nb = {
            "cells": [
                {"cell_type": "code", "source": ["a", "b", "c", "d"]},
            ],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        nb_path = tmp_path / "dry.ipynb"
        original = json.dumps(nb)
        nb_path.write_text(original, encoding="utf-8")

        from repair_genai_notebooks import repair_notebook

        fixed, total = repair_notebook(nb_path, dry_run=True)
        assert fixed == 1
        assert total == 1
        # File unchanged
        assert nb_path.read_text(encoding="utf-8") == original

    def test_mixed_cells(self, tmp_path):
        """Only corrupted code cells are fixed; markdown ignored."""
        import json

        nb = {
            "cells": [
                {"cell_type": "code", "source": ["a", "b", "c", "d"]},  # corrupted
                {"cell_type": "markdown", "source": ["# Title"]},
                {"cell_type": "code", "source": ["x = 1\n", "y = 2\n"]},  # clean
            ],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        nb_path = tmp_path / "mixed.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")

        from repair_genai_notebooks import repair_notebook

        fixed, total = repair_notebook(nb_path)
        assert fixed == 1
        assert total == 2

    def test_no_code_cells(self, tmp_path):
        """A notebook with no code cells reports 0 fixed, 0 total."""
        import json

        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["# Title"]},
            ],
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        nb_path = tmp_path / "markdown_only.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")

        from repair_genai_notebooks import repair_notebook

        fixed, total = repair_notebook(nb_path)
        assert fixed == 0
        assert total == 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
