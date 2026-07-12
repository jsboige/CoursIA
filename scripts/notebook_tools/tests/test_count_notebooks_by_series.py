"""Tests for scripts/notebook_tools/count_notebooks_by_series.py

Covers: count_notebooks_in_dir, extract_readme_count.
Pure functions, no I/O on real repo (uses tmp_path fixtures).
"""

import sys
from pathlib import Path

import pytest

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

from count_notebooks_by_series import count_notebooks_in_dir, extract_readme_count


# --- count_notebooks_in_dir ---

class TestCountNotebooksInDir:
    def test_empty_dir(self, tmp_path):
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0
        assert result["by_subfolder"] == {}

    def test_single_notebook(self, tmp_path):
        (tmp_path / "test.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_nested_notebook(self, tmp_path):
        sub = tmp_path / "Part1"
        sub.mkdir()
        (sub / "lesson.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert result["by_subfolder"]["Part1"] == 1

    def test_excludes_checkpoints(self, tmp_path):
        cp = tmp_path / ".ipynb_checkpoints"
        cp.mkdir()
        (cp / "test-checkpoint.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "real.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_excludes_obj_bin(self, tmp_path):
        obj_dir = tmp_path / "obj"
        obj_dir.mkdir()
        (obj_dir / "test.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0

    def test_pedagogical_excludes_research(self, tmp_path):
        research = tmp_path / "research"
        research.mkdir()
        (research / "experiment.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "lesson.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_pedagogical_excludes_archive(self, tmp_path):
        archive = tmp_path / "archive"
        archive.mkdir()
        (archive / "old.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 0

    def test_pedagogical_excludes_output(self, tmp_path):
        (tmp_path / "lesson_output.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "lesson.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 1

    def test_all_mode_includes_research(self, tmp_path):
        research = tmp_path / "research"
        research.mkdir()
        (research / "experiment.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=False)
        assert result["total"] == 1

    def test_multiple_subfolders(self, tmp_path):
        for name in ["Part1", "Part2", "Part3"]:
            sub = tmp_path / name
            sub.mkdir()
            (sub / "lesson.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 3
        assert result["by_subfolder"]["Part1"] == 1
        assert result["by_subfolder"]["Part2"] == 1
        assert result["by_subfolder"]["Part3"] == 1

    def test_root_level_notebook(self, tmp_path):
        (tmp_path / "standalone.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert result["by_subfolder"].get("_root") == 1

    def test_non_ipynb_ignored(self, tmp_path):
        (tmp_path / "readme.md").write_text("hello", encoding="utf-8")
        (tmp_path / "script.py").write_text("pass", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0

    def test_counts_in_subfolder_correctly(self, tmp_path):
        sub = tmp_path / "SubA"
        sub.mkdir()
        for i in range(5):
            (sub / f"nb{i}.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 5
        assert result["by_subfolder"]["SubA"] == 5

    def test_partner_course_excluded(self, tmp_path):
        pc = tmp_path / "partner-course-2024"
        pc.mkdir()
        (pc / "lesson.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 0


# --- extract_readme_count ---

class TestExtractReadmeCount:
    def test_no_file(self, tmp_path):
        result = extract_readme_count(tmp_path / "nonexistent.md")
        assert result is None

    def test_bold_notebooks(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("Some intro\n\n> **28 notebooks** Python\n", encoding="utf-8")
        assert extract_readme_count(p) == 28

    def test_table_row(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("| Notebooks | 45 |\n", encoding="utf-8")
        assert extract_readme_count(p) == 45

    def test_inline_notebooks_python(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("This series has 12 notebooks Python.\n", encoding="utf-8")
        assert extract_readme_count(p) == 12

    def test_inline_notebooks(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("Contient 7 notebooks de cours.\n", encoding="utf-8")
        assert extract_readme_count(p) == 7

    def test_total_row(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("| Total | 84 |\n", encoding="utf-8")
        assert extract_readme_count(p) == 84

    def test_exercices(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("La serie comprend 15 exercices.\n", encoding="utf-8")
        assert extract_readme_count(p) == 15

    def test_no_match(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("Some random text without numbers.\n", encoding="utf-8")
        assert extract_readme_count(p) is None

    def test_zero_ignored(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("We have 0 notebooks.\n", encoding="utf-8")
        result = extract_readme_count(p)
        assert result is None

    def test_first_pattern_wins(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("**5 notebooks** and also 10 notebooks Python.\n", encoding="utf-8")
        assert extract_readme_count(p) == 5

    def test_case_insensitive(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("**28 Notebooks** in this series.\n", encoding="utf-8")
        assert extract_readme_count(p) == 28

    def test_empty_file(self, tmp_path):
        p = tmp_path / "README.md"
        p.write_text("", encoding="utf-8")
        assert extract_readme_count(p) is None

    def test_examples_excluded(self, tmp_path):
        ex = tmp_path / "examples"
        ex.mkdir()
        (ex / "demo.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path, pedagogical=True)
        assert result["total"] == 0
