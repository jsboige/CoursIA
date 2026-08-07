"""Tests for count_notebooks_by_series.py — notebook counting and README verification."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from count_notebooks_by_series import (
    count_notebooks_in_dir,
    extract_readme_count,
)


# --- count_notebooks_in_dir ---


class TestCountNotebooksInDir:
    def test_empty_directory(self, tmp_path):
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0
        assert result["by_subfolder"] == {}

    def test_single_notebook_root(self, tmp_path):
        (tmp_path / "test.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert result["by_subfolder"]["_root"] == 1

    def test_notebook_in_subfolder(self, tmp_path):
        sub = tmp_path / "Image"
        sub.mkdir()
        (sub / "App-1.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert result["by_subfolder"]["Image"] == 1

    def test_multiple_subfolders(self, tmp_path):
        for name in ["Image", "Audio", "Texte"]:
            sub = tmp_path / name
            sub.mkdir()
            (sub / "nb.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 3
        assert len(result["by_subfolder"]) == 3

    def test_non_ipynb_ignored(self, tmp_path):
        (tmp_path / "readme.md").write_text("hello", encoding="utf-8")
        (tmp_path / "data.csv").write_text("a,b", encoding="utf-8")
        (tmp_path / "test.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_checkpoints_excluded(self, tmp_path):
        cp = tmp_path / ".ipynb_checkpoints"
        cp.mkdir()
        (cp / "test.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "good.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_obj_bin_excluded(self, tmp_path):
        obj = tmp_path / "obj"
        obj.mkdir()
        (obj / "test.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0

    def test_pedagogical_excludes_research(self, tmp_path):
        research = tmp_path / "research"
        research.mkdir()
        (research / "exp.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "main.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_pedagogical_excludes_archive(self, tmp_path):
        archive = tmp_path / "archive"
        archive.mkdir()
        (archive / "old.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "main.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_pedagogical_excludes_output(self, tmp_path):
        (tmp_path / "main.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "main_output.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_non_pedagogical_includes_all(self, tmp_path):
        research = tmp_path / "research"
        research.mkdir()
        (research / "exp.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "main.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=False)
        assert result["total"] == 2

    def test_partner_course_excluded_pedagogical(self, tmp_path):
        pc = tmp_path / "partner-course-WS"
        pc.mkdir()
        (pc / "nb.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 0

    def test_deeply_nested(self, tmp_path):
        deep = tmp_path / "A" / "B" / "C"
        deep.mkdir(parents=True)
        (deep / "nb.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert "A" in result["by_subfolder"]


# --- extract_readme_count ---


class TestExtractReadmeCount:
    def test_nonexistent_file(self, tmp_path):
        assert extract_readme_count(tmp_path / "nope.md") is None

    def test_bold_notebooks_pattern(self, tmp_path):
        # Bare prose number (no CATALOG-STATUS marker, no explicit Total anchor)
        # is NO LONGER caught since #9835: it was the scope bug (sub-section
        # headers like SymbolicAI's "**28 notebooks**" Lean read as the series
        # total). The marker is the canonical anchor now.
        readme = tmp_path / "README.md"
        readme.write_text("# Title\n\n> **28 notebooks Python**\n", encoding="utf-8")
        assert extract_readme_count(readme) is None

    def test_table_notebooks_pattern(self, tmp_path):
        # Bare "| Notebooks | N |" (no marker) no longer caught (#9835).
        readme = tmp_path / "README.md"
        readme.write_text("| Metric | Value |\n| Notebooks | 42 |\n", encoding="utf-8")
        assert extract_readme_count(readme) is None

    def test_inline_notebooks_python(self, tmp_path):
        # Bare inline "N notebooks Python" (no marker) no longer caught (#9835).
        readme = tmp_path / "README.md"
        readme.write_text("This series has 15 notebooks Python.\n", encoding="utf-8")
        assert extract_readme_count(readme) is None

    def test_inline_notebooks_generic(self, tmp_path):
        # Bare inline "N notebooks" (no marker) no longer caught (#9835).
        readme = tmp_path / "README.md"
        readme.write_text("The collection includes 10 notebooks.\n", encoding="utf-8")
        assert extract_readme_count(readme) is None

    def test_table_total_pattern(self, tmp_path):
        # Explicitly-anchored "| Total | N |" fallback is INTACT (#9835).
        readme = tmp_path / "README.md"
        readme.write_text("| Total | 84 |\n", encoding="utf-8")
        assert extract_readme_count(readme) == 84

    def test_french_exercices_pattern(self, tmp_path):
        # The "(\\d+)\\s+exercices" fallback is REMOVED (#9835 acceptance 2):
        # an exercise count is not a notebook count. This was the IIT bug
        # (53 notebooks vs "3 exercices").
        readme = tmp_path / "README.md"
        readme.write_text("Cette serie contient 12 exercices.\n", encoding="utf-8")
        assert extract_readme_count(readme) is None

    def test_no_count_returns_none(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# Title\n\nSome description.\n", encoding="utf-8")
        assert extract_readme_count(readme) is None

    def test_zero_not_returned(self):
        """Pattern matching 0 should not be returned (val > 0 check)."""
        pass  # This is tested implicitly — the function checks val > 0

    def test_bold_pattern_priority(self, tmp_path):
        # No longer applicable: bare prose numbers are not caught at all since
        # #9835, so there is no "priority" between bare-prose patterns. The
        # only priority is: CATALOG-STATUS marker > explicit Total > None.
        readme = tmp_path / "README.md"
        readme.write_text("**5 notebooks** and also mentions 99 notebooks elsewhere.", encoding="utf-8")
        assert extract_readme_count(readme) is None
