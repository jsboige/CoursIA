"""Tests for scripts/notebook_tools/count_notebooks_by_series.py.

Tests focus on pure functions: count_notebooks_in_dir, extract_readme_count.
Filesystem methods use tmp_path for isolation.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from count_notebooks_by_series import (
    EXCLUDE_ALWAYS,
    EXCLUDE_PEDAGOGICAL,
    count_notebooks_in_dir,
    extract_readme_count,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_notebook(path: Path, name: str = "test.ipynb") -> Path:
    """Create a minimal .ipynb file."""
    nb = path / name
    nb.parent.mkdir(parents=True, exist_ok=True)
    nb.write_text('{"cells": [], "metadata": {}}', encoding="utf-8")
    return nb


# ---------------------------------------------------------------------------
# count_notebooks_in_dir
# ---------------------------------------------------------------------------

class TestCountNotebooksInDir:
    def test_counts_ipynb_files(self, tmp_path):
        _make_notebook(tmp_path, "a.ipynb")
        _make_notebook(tmp_path, "b.ipynb")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 2

    def test_empty_dir(self, tmp_path):
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0

    def test_subfolder_breakdown(self, tmp_path):
        _make_notebook(tmp_path / "Image", "nb1.ipynb")
        _make_notebook(tmp_path / "Image", "nb2.ipynb")
        _make_notebook(tmp_path / "Audio", "nb3.ipynb")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 3
        assert result["by_subfolder"]["Image"] == 2
        assert result["by_subfolder"]["Audio"] == 1

    def test_excludes_checkpoints(self, tmp_path):
        _make_notebook(tmp_path / ".ipynb_checkpoints", "hidden.ipynb")
        _make_notebook(tmp_path, "visible.ipynb")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_excludes_obj_and_bin(self, tmp_path):
        _make_notebook(tmp_path / "obj", "build.ipynb")
        _make_notebook(tmp_path / "bin", "build.ipynb")
        _make_notebook(tmp_path, "good.ipynb")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_excludes_pycache(self, tmp_path):
        _make_notebook(tmp_path / "__pycache__", "cache.ipynb")
        _make_notebook(tmp_path, "real.ipynb")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_pedagogical_excludes_research(self, tmp_path):
        _make_notebook(tmp_path / "research", "exp.ipynb")
        _make_notebook(tmp_path, "main.ipynb")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_pedagogical_excludes_archive(self, tmp_path):
        _make_notebook(tmp_path / "archive", "old.ipynb")
        _make_notebook(tmp_path, "current.ipynb")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_pedagogical_excludes_output(self, tmp_path):
        _make_notebook(tmp_path / "_output", "exec.ipynb")
        _make_notebook(tmp_path, "src.ipynb")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_non_pedagogical_includes_all(self, tmp_path):
        _make_notebook(tmp_path / "research", "exp.ipynb")
        _make_notebook(tmp_path / "archive", "old.ipynb")
        _make_notebook(tmp_path, "main.ipynb")
        result = count_notebooks_in_dir(tmp_path, pedagogical=False)
        assert result["total"] == 3

    def test_root_level_notebook(self, tmp_path):
        _make_notebook(tmp_path, "root.ipynb")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert "_root" in result["by_subfolder"]

    def test_nested_subfolders(self, tmp_path):
        _make_notebook(tmp_path / "Level1" / "Level2", "deep.ipynb")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert result["by_subfolder"]["Level1"] == 1

    def test_non_ipynb_ignored(self, tmp_path):
        (tmp_path / "readme.md").write_text("hello", encoding="utf-8")
        (tmp_path / "script.py").write_text("pass", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0


# ---------------------------------------------------------------------------
# extract_readme_count
# ---------------------------------------------------------------------------

class TestExtractReadmeCount:
    def test_bold_notebooks(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# GenAI\n\n> **28 notebooks Python**\n", encoding="utf-8")
        assert extract_readme_count(readme) == 28

    def test_table_notebooks(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("| Notebooks | 42 |\n", encoding="utf-8")
        assert extract_readme_count(readme) == 42

    def test_inline_notebooks_python(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("This series has 15 notebooks Python.\n", encoding="utf-8")
        assert extract_readme_count(readme) == 15

    def test_inline_notebooks(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("We have 10 notebooks in this series.\n", encoding="utf-8")
        assert extract_readme_count(readme) == 10

    def test_table_total(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("| Total | 84 |\n", encoding="utf-8")
        assert extract_readme_count(readme) == 84

    def test_exercices_pattern(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("La serie contient 12 exercices.\n", encoding="utf-8")
        assert extract_readme_count(readme) == 12

    def test_missing_readme(self, tmp_path):
        assert extract_readme_count(tmp_path / "nonexistent.md") is None

    def test_no_count_in_readme(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# Title\n\nNo numbers here.\n", encoding="utf-8")
        assert extract_readme_count(readme) is None

    def test_zero_not_returned(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("**0 notebooks**\n", encoding="utf-8")
        # 0 is not > 0, so pattern skips it
        assert extract_readme_count(readme) is None

    def test_bold_pattern_priority(self, tmp_path):
        """Bold pattern should match first (highest reliability)."""
        readme = tmp_path / "README.md"
        readme.write_text("**5 notebooks** and also 10 notebooks later.\n", encoding="utf-8")
        assert extract_readme_count(readme) == 5

    def test_case_insensitive(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("**28 Notebooks Python**\n", encoding="utf-8")
        assert extract_readme_count(readme) == 28


# ---------------------------------------------------------------------------
# Constants consistency
# ---------------------------------------------------------------------------

class TestConstants:
    def test_exclude_always_has_expected(self):
        assert ".ipynb_checkpoints" in EXCLUDE_ALWAYS
        assert "__pycache__" in EXCLUDE_ALWAYS

    def test_exclude_pedagogical_has_expected(self):
        assert "research" in EXCLUDE_PEDAGOGICAL
        assert "archive" in EXCLUDE_PEDAGOGICAL
        assert "_output" in EXCLUDE_PEDAGOGICAL
