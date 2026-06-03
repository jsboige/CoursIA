"""Tests for count_notebooks_by_series.py — notebook counting and README extraction."""

import json
import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from count_notebooks_by_series import (
    count_notebooks_in_dir,
    extract_readme_count,
    EXCLUDE_ALWAYS,
    EXCLUDE_PEDAGOGICAL,
)


class TestCountNotebooksInDir:

    def test_empty_dir(self, tmp_path):
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0
        assert result["by_subfolder"] == {}

    def test_single_notebook(self, tmp_path):
        (tmp_path / "test.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert result["by_subfolder"] == {"_root": 1}

    def test_nested_notebook(self, tmp_path):
        sub = tmp_path / "Part1"
        sub.mkdir()
        (sub / "lesson.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert result["by_subfolder"] == {"Part1": 1}

    def test_multiple_subfolders(self, tmp_path):
        for name in ["Part1", "Part2", "Part3"]:
            sub = tmp_path / name
            sub.mkdir()
            (sub / "nb.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 3
        assert len(result["by_subfolder"]) == 3

    def test_excludes_checkpoints(self, tmp_path):
        cp = tmp_path / ".ipynb_checkpoints"
        cp.mkdir()
        (cp / "test-checkpoint.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "real.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_excludes_pycache(self, tmp_path):
        pyc = tmp_path / "__pycache__"
        pyc.mkdir()
        (pyc / "mod.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0

    def test_pedagogical_excludes_research(self, tmp_path):
        research = tmp_path / "research"
        research.mkdir()
        (research / "analysis.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "lesson.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_pedagogical_includes_research_when_all(self, tmp_path):
        research = tmp_path / "research"
        research.mkdir()
        (research / "analysis.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=False)
        assert result["total"] == 1

    def test_pedagogical_excludes_archive(self, tmp_path):
        archive = tmp_path / "archive"
        archive.mkdir()
        (archive / "old.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 0

    def test_pedagogical_excludes_output(self, tmp_path):
        sub = tmp_path / "lessons"
        sub.mkdir()
        (sub / "lesson_output.ipynb").write_text("{}", encoding="utf-8")
        (sub / "lesson.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_non_ipynb_ignored(self, tmp_path):
        (tmp_path / "readme.md").write_text("hi", encoding="utf-8")
        (tmp_path / "script.py").write_text("pass", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0


class TestExtractReadmeCount:

    def test_bold_notebooks(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# Title\n> **28 notebooks Python**\n", encoding="utf-8")
        assert extract_readme_count(readme) == 28

    def test_table_row_notebooks(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("| Notebooks | 15 |\n", encoding="utf-8")
        assert extract_readme_count(readme) == 15

    def test_inline_notebooks_python(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("This series has 42 notebooks Python.\n", encoding="utf-8")
        assert extract_readme_count(readme) == 42

    def test_inline_notebooks(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("Contains 10 notebooks.\n", encoding="utf-8")
        assert extract_readme_count(readme) == 10

    def test_total_row(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("| Total | 84 |\n", encoding="utf-8")
        assert extract_readme_count(readme) == 84

    def test_exercices(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("La serie contient 7 exercices.\n", encoding="utf-8")
        assert extract_readme_count(readme) == 7

    def test_nonexistent_file(self, tmp_path):
        assert extract_readme_count(tmp_path / "nonexistent.md") is None

    def test_no_match(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# Series Title\nSome description.\n", encoding="utf-8")
        assert extract_readme_count(readme) is None

    def test_first_match_wins(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("**10 notebooks** and then 20 notebooks later.\n", encoding="utf-8")
        assert extract_readme_count(readme) == 10
