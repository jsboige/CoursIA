"""Tests for scripts/repair_genai_notebooks.py — GenAI notebook corruption repair."""

import importlib.util
import json
from pathlib import Path

import pytest

# Load module by file path
_MOD_PATH = (
    Path(__file__).resolve().parent.parent.parent.parent
    / "scripts"
    / "repair_genai_notebooks.py"
)
_spec = importlib.util.spec_from_file_location("repair_genai_notebooks", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

is_cell_corrupted = _mod.is_cell_corrupted
fix_source = _mod.fix_source
repair_notebook = _mod.repair_notebook


# --- is_cell_corrupted ---


class TestIsCellCorrupted:
    def test_empty_source_not_corrupted(self):
        assert is_cell_corrupted([]) is False

    def test_none_source_not_corrupted(self):
        assert is_cell_corrupted(None) is False

    def test_string_source_not_corrupted(self):
        """Non-list source should not be flagged."""
        assert is_cell_corrupted("a single string") is False

    def test_normal_source_not_corrupted(self):
        """Properly formatted source with \\n terminators."""
        source = ["import os\n", "print('hello')\n", "x = 1"]
        assert is_cell_corrupted(source) is False

    def test_collapsed_line_detected(self):
        """Method 1: lines > 300 chars with Python keywords."""
        mega_line = "import os; from dotenv import load_dotenv; " * 15
        source = [mega_line]
        assert is_cell_corrupted(source) is True

    def test_collapsed_line_def_keyword(self):
        """Collapsed line with 'def ' keyword detected."""
        mega_line = "def setup(): " + "x = 1; " * 100
        source = [mega_line]
        assert is_cell_corrupted(source) is True

    def test_collapsed_line_dotenv_keyword(self):
        """Collapsed line with 'dotenv' keyword detected."""
        mega_line = "dotenv" + " env_loaded" * 100
        source = [mega_line]
        assert is_cell_corrupted(source) is True

    def test_collapsed_line_genai_root_keyword(self):
        """Collapsed line with 'GENAI_ROOT' keyword detected."""
        mega_line = "GENAI_ROOT" + " path" * 100
        source = [mega_line]
        assert is_cell_corrupted(source) is True

    def test_short_line_not_flagged(self):
        """Lines < 300 chars with keywords should NOT be flagged by method 1."""
        source = ["import os\n", "load_dotenv()\n"]
        assert is_cell_corrupted(source) is False

    def test_missing_newline_terminators(self):
        """Method 2: 3+ non-empty mid-array elements without \\n."""
        source = ["import os", "from dotenv import load_dotenv", "load_dotenv()", "x = 1"]
        assert is_cell_corrupted(source) is True

    def test_two_missing_newlines_not_flagged(self):
        """Only 2 missing \\n is below the threshold (needs >= 3)."""
        source = ["import os", "from dotenv import load_dotenv", "x = 1\n"]
        # Only 2 non-empty mid-array elements without \n (below threshold of 3)
        assert is_cell_corrupted(source) is False

    def test_last_element_no_newline_is_ok(self):
        """Last element without \\n is normal Jupyter format."""
        source = ["import os\n", "x = 1"]
        assert is_cell_corrupted(source) is False

    def test_empty_strings_ignored(self):
        """Empty/whitespace-only strings don't count toward missing \\n."""
        source = ["import os\n", "", "  ", "x = 1"]
        assert is_cell_corrupted(source) is False


# --- fix_source ---


class TestFixSource:
    def test_empty_source_unchanged(self):
        src, fixed = fix_source([])
        assert src == []
        assert fixed is False

    def test_none_source_unchanged(self):
        src, fixed = fix_source(None)
        assert src is None
        assert fixed is False

    def test_non_list_source_unchanged(self):
        src, fixed = fix_source("a string")
        assert src == "a string"
        assert fixed is False

    def test_normal_source_not_fixed(self):
        """Already correct source should not be modified."""
        source = ["import os\n", "print('hello')\n", "x = 1"]
        new_src, fixed = fix_source(source)
        assert new_src == source
        assert fixed is False

    def test_corrupted_source_fixed(self):
        """Missing \\n terminators should be added."""
        source = ["import os", "from dotenv import load_dotenv", "load_dotenv()", "x = 1"]
        new_src, fixed = fix_source(source)
        assert fixed is True
        # First 3 elements should now have \n
        assert new_src[0] == "import os\n"
        assert new_src[1] == "from dotenv import load_dotenv\n"
        assert new_src[2] == "load_dotenv()\n"
        # Last element stays as-is
        assert new_src[3] == "x = 1"

    def test_last_element_preserved_with_newline(self):
        """If last element already has \\n, keep it."""
        source = ["import os", "from dotenv import load_dotenv", "load_dotenv()", "x = 1\n"]
        new_src, fixed = fix_source(source)
        assert fixed is True
        assert new_src[-1] == "x = 1\n"

    def test_collapsed_line_fixed(self):
        """Collapsed mega-line gets \\n appended (method 1 corruption)."""
        mega_line = "import os; from dotenv import load_dotenv; " * 15
        source = [mega_line, "print('done')"]
        new_src, fixed = fix_source(source)
        assert fixed is True
        # First element gets \n appended
        assert new_src[0] == mega_line + "\n"


# --- repair_notebook ---


class TestRepairNotebook:
    def _make_notebook(self, cells):
        """Helper to create a minimal notebook dict."""
        return {
            "cells": cells,
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 4,
        }

    def test_clean_notebook_no_changes(self, tmp_path):
        """Notebook with no corruption should not be modified."""
        cells = [
            {"cell_type": "code", "source": ["import os\n", "x = 1"], "outputs": []},
            {"cell_type": "markdown", "source": ["# Title\n", "Text"], "outputs": []},
        ]
        nb_path = tmp_path / "clean.ipynb"
        nb_path.write_text(json.dumps(self._make_notebook(cells)), encoding="utf-8")

        fixed_cells, total_cells = repair_notebook(str(nb_path))
        assert fixed_cells == 0
        assert total_cells == 1  # Only code cells counted

        # File should be unchanged (no rewrite)
        content = json.loads(nb_path.read_text(encoding="utf-8"))
        assert content["cells"][0]["source"] == ["import os\n", "x = 1"]

    def test_corrupted_notebook_fixed(self, tmp_path):
        """Corrupted notebook should be repaired."""
        corrupted_source = ["import os", "from dotenv import load_dotenv", "load_dotenv()", "x = 1"]
        cells = [
            {"cell_type": "code", "source": corrupted_source, "outputs": []},
        ]
        nb_path = tmp_path / "corrupted.ipynb"
        nb_path.write_text(json.dumps(self._make_notebook(cells)), encoding="utf-8")

        fixed_cells, total_cells = repair_notebook(str(nb_path))
        assert fixed_cells == 1
        assert total_cells == 1

        # Verify file was written with fixed source
        content = json.loads(nb_path.read_text(encoding="utf-8"))
        assert content["cells"][0]["source"][0] == "import os\n"

    def test_dry_run_no_modification(self, tmp_path):
        """Dry run should not modify the file."""
        corrupted_source = ["import os", "from dotenv import load_dotenv", "load_dotenv()", "x = 1"]
        cells = [
            {"cell_type": "code", "source": corrupted_source, "outputs": []},
        ]
        nb_path = tmp_path / "corrupted.ipynb"
        nb_path.write_text(json.dumps(self._make_notebook(cells)), encoding="utf-8")

        fixed_cells, total_cells = repair_notebook(str(nb_path), dry_run=True)
        assert fixed_cells == 1

        # File should NOT be modified
        content = json.loads(nb_path.read_text(encoding="utf-8"))
        assert content["cells"][0]["source"] == corrupted_source

    def test_mixed_cells_only_code_checked(self, tmp_path):
        """Markdown cells should be skipped (not counted as code cells)."""
        cells = [
            {"cell_type": "markdown", "source": ["# Title\n"], "outputs": []},
            {"cell_type": "code", "source": ["import os\n", "x = 1"], "outputs": []},
        ]
        nb_path = tmp_path / "mixed.ipynb"
        nb_path.write_text(json.dumps(self._make_notebook(cells)), encoding="utf-8")

        fixed_cells, total_cells = repair_notebook(str(nb_path))
        assert fixed_cells == 0
        assert total_cells == 1  # Only the code cell

    def test_multiple_corrupted_cells(self, tmp_path):
        """Multiple corrupted cells should all be fixed."""
        corrupted = ["import os", "from dotenv import load_dotenv", "load_dotenv()", "x = 1"]
        cells = [
            {"cell_type": "code", "source": corrupted, "outputs": []},
            {"cell_type": "markdown", "source": ["# Title"], "outputs": []},
            {"cell_type": "code", "source": list(corrupted), "outputs": []},
        ]
        nb_path = tmp_path / "multi_corrupted.ipynb"
        nb_path.write_text(json.dumps(self._make_notebook(cells)), encoding="utf-8")

        fixed_cells, total_cells = repair_notebook(str(nb_path))
        assert fixed_cells == 2
        assert total_cells == 2

    def test_no_code_cells(self, tmp_path):
        """Notebook with no code cells should report 0."""
        cells = [
            {"cell_type": "markdown", "source": ["# Title\n"], "outputs": []},
        ]
        nb_path = tmp_path / "no_code.ipynb"
        nb_path.write_text(json.dumps(self._make_notebook(cells)), encoding="utf-8")

        fixed_cells, total_cells = repair_notebook(str(nb_path))
        assert fixed_cells == 0
        assert total_cells == 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
