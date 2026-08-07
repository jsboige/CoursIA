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

    # --- #9851: EXCLUDE_ALWAYS must match DIRECTORY segments only,
    #     never the filename. A notebook named "Foo-CombinatorialGames.ipynb"
    #     at the series root must be counted (the bug dropped 5 GameTheory
    #     notebooks because "bin" is a substring of "CombinatorialGames").

    def test_filename_with_bin_counted(self, tmp_path):
        """#9851 root fix: 'Foo-CombinatorialGames.ipynb' at root IS counted.
        The substring "bin" in the filename must NOT trigger EXCLUDE_ALWAYS."""
        (tmp_path / "GameTheory-8-CombinatorialGames.ipynb").write_text(
            "{}", encoding="utf-8"
        )
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert result["by_subfolder"].get("_root") == 1

    def test_filename_with_obj_counted(self, tmp_path):
        """Sibling case: 'ObjectDetection.ipynb' at root IS counted.
        The substring "obj" in the filename must NOT trigger EXCLUDE_ALWAYS."""
        (tmp_path / "ObjectDetection.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_filename_with_pycache_counted(self, tmp_path):
        """Sibling case: 'pycache_utils.ipynb' at root IS counted."""
        (tmp_path / "pycache_utils.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_bin_subdir_still_excluded(self, tmp_path):
        """Intent preserved: a notebook UNDER bin/ is still excluded.
        EXCLUDE_ALWAYS still matches 'bin' when 'bin' is a directory segment."""
        bin_dir = tmp_path / "bin"
        bin_dir.mkdir()
        (bin_dir / "compiled_output.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "real.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1
        assert "bin" not in result["by_subfolder"]

    def test_obj_subdir_still_excluded(self, tmp_path):
        """Intent preserved: a notebook UNDER obj/ is still excluded."""
        obj_dir = tmp_path / "obj"
        obj_dir.mkdir()
        (obj_dir / "build.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 0

    def test_checkpoints_subdir_still_excluded(self, tmp_path):
        """Intent preserved: a notebook UNDER .ipynb_checkpoints/ is excluded."""
        cp = tmp_path / ".ipynb_checkpoints"
        cp.mkdir()
        (cp / "lesson-checkpoint.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "lesson.ipynb").write_text("{}", encoding="utf-8")
        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 1

    def test_gametheory_synthetic_regression(self, tmp_path):
        """#9851 acceptance: synthetic GameTheory-like layout reproduces the
        real-world bug. 5 root notebooks with 'bin' in their filenames MUST
        be counted; bin/ subdir notebook MUST be excluded."""
        # 5 root notebooks whose filenames contain 'bin' substring
        for name in [
            "GameTheory-8-CombinatorialGames.ipynb",
            "GameTheory-8-CombinatorialGames-Csharp.ipynb",
            "GameTheory-8b-Lean-CombinatorialGames.ipynb",
            "GameTheory-8c-CombinatorialGames-Csharp.ipynb",
            "GameTheory-8c-CombinatorialGames-Python.ipynb",
        ]:
            (tmp_path / name).write_text("{}", encoding="utf-8")
        # 7 sub-series notebooks (SocialChoice)
        social_choice = tmp_path / "SocialChoice"
        social_choice.mkdir()
        for i in range(7):
            (social_choice / f"sc-{i}.ipynb").write_text("{}", encoding="utf-8")
        # 1 noise: a real bin/ subdir (intentionally excluded)
        bin_dir = tmp_path / "bin"
        bin_dir.mkdir()
        (bin_dir / "compiled.ipynb").write_text("{}", encoding="utf-8")

        result = count_notebooks_in_dir(tmp_path)
        assert result["total"] == 12, (
            f"5 root + 7 SocialChoice = 12; got {result['total']} "
            f"(the bin/ subdir is the ONLY expected exclusion)"
        )
        assert result["by_subfolder"].get("_root") == 5
        assert result["by_subfolder"].get("SocialChoice") == 7
        assert "bin" not in result["by_subfolder"]


# --- extract_readme_count ---

class TestExtractReadmeCount:
    def test_no_file(self, tmp_path):
        result = extract_readme_count(tmp_path / "nonexistent.md")
        assert result is None

    # --- Scope-aware behavior (#9835) -------------------------------------
    # extract_readme_count is anchored on the generated CATALOG-STATUS marker
    # (pedagogical_count). Bare prose numbers are NO LONGER caught: they were
    # the bug (sub-section headers, exercise counts compared to notebooks).

    _MARKER = (
        "<!-- CATALOG-STATUS\n"
        "series: Demo\n"
        "pedagogical_count: {count}\n"
        "breakdown: A=10, B={rest}\n"
        "maturity: BETA={count}\n"
        "-->\n"
    )

    def test_marker_primary(self, tmp_path):
        """With a CATALOG-STATUS marker, return its pedagogical_count."""
        p = tmp_path / "README.md"
        p.write_text(self._MARKER.format(count=226, rest=216), encoding="utf-8")
        assert extract_readme_count(p) == 226

    def test_marker_wins_over_misleading_prose(self, tmp_path):
        """The SymbolicAI bug: marker total (226) must win over a sub-section
        header '**28 notebooks**' that appears in the prose below the marker."""
        p = tmp_path / "README.md"
        body = self._MARKER.format(count=226, rest=216)
        body += "\n## Lean - Verification Formelle\n\n**28 notebooks** dans cette sous-serie.\n"
        p.write_text(body, encoding="utf-8")
        assert extract_readme_count(p) == 226

    def test_marker_exercices_not_caught(self, tmp_path):
        """The IIT bug: marker total (53) must win over an 'exercices' phrase
        that previously served as a fallback and compared notebooks to exercises."""
        p = tmp_path / "README.md"
        body = self._MARKER.format(count=53, rest=43)
        body += "\nLes **3 exercices** vous font varier les sous-systemes.\n"
        p.write_text(body, encoding="utf-8")
        assert extract_readme_count(p) == 53

    def test_total_row_fallback_no_marker(self, tmp_path):
        """Without a marker, an explicitly-anchored '| Total | N |' still works."""
        p = tmp_path / "README.md"
        p.write_text("| Total | 84 |\n", encoding="utf-8")
        assert extract_readme_count(p) == 84

    def test_bare_notebooks_not_caught(self, tmp_path):
        """No marker + bare '**N notebooks**' (often a sub-section header) ->
        None, not the first number. This is the core scope-aware fix (#9835)."""
        p = tmp_path / "README.md"
        p.write_text("Some intro\n\n> **28 notebooks** Python\n", encoding="utf-8")
        assert extract_readme_count(p) is None

    def test_exercices_not_caught(self, tmp_path):
        """No marker + 'N exercices' -> None. An exercise count is not a
        notebook count; the former fallback is removed (#9835)."""
        p = tmp_path / "README.md"
        p.write_text("La serie comprend 15 exercices.\n", encoding="utf-8")
        assert extract_readme_count(p) is None

    def test_no_marker_no_total_is_none(self, tmp_path):
        """Honest silence: no marker and no explicit Total -> None, not a
        number caught at random (#9835 acceptance 4)."""
        p = tmp_path / "README.md"
        p.write_text("Some random text without numbers.\n", encoding="utf-8")
        assert extract_readme_count(p) is None

    def test_marker_zero_falls_through(self, tmp_path):
        """A marker with pedagogical_count: 0 is ignored (val > 0), and the
        function falls through to the prose fallback (or None)."""
        p = tmp_path / "README.md"
        p.write_text(self._MARKER.format(count=0, rest=0), encoding="utf-8")
        assert extract_readme_count(p) is None

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
