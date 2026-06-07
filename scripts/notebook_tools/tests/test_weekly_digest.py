"""Tests for scripts/notebook_tools/weekly_digest.py — weekly repository digest.

Tests focus on the pure function: classify_notebook_changes — covering
series classification, file type counting, edge cases.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from weekly_digest import classify_notebook_changes


# ---------------------------------------------------------------------------
# classify_notebook_changes — series detection
# ---------------------------------------------------------------------------

class TestClassifySeriesDetection:
    """Tests for notebook series detection from file paths."""

    def test_single_notebook_series(self):
        result = classify_notebook_changes({
            "MyIA.AI.Notebooks/Search/Part1-Foundations/nb1.ipynb"
        })
        assert "Search" in result["series"]
        assert result["series"]["Search"]["files"] == 1
        assert result["series"]["Search"]["notebooks"] == 1

    def test_multiple_series(self):
        result = classify_notebook_changes({
            "MyIA.AI.Notebooks/Search/nb1.ipynb",
            "MyIA.AI.Notebooks/Sudoku/nb2.ipynb",
            "MyIA.AI.Notebooks/GenAI/nb3.py",
        })
        assert len(result["series"]) == 3
        assert "Search" in result["series"]
        assert "Sudoku" in result["series"]
        assert "GenAI" in result["series"]

    def test_notebook_names_capped_at_5(self):
        files = {f"MyIA.AI.Notebooks/Search/nb{i}.ipynb" for i in range(10)}
        result = classify_notebook_changes(files)
        names = result["series"]["Search"]["notebook_names"]
        assert len(names) == 5
        assert result["series"]["Search"]["notebooks"] == 10

    def test_non_notebook_file_in_series(self):
        result = classify_notebook_changes({
            "MyIA.AI.Notebooks/Search/README.md",
        })
        assert "Search" in result["series"]
        assert result["series"]["Search"]["files"] == 1
        assert result["series"]["Search"]["notebooks"] == 0

    def test_backslash_path_not_matched(self):
        """Windows backslash paths don't match startswith('MyIA.AI.Notebooks/').

        The code uses startswith with forward slash BEFORE replacing backslashes.
        This is a known limitation — only forward-slash paths are classified into series.
        """
        result = classify_notebook_changes({
            "MyIA.AI.Notebooks" + chr(92) + "Search" + chr(92) + "nb1.ipynb",
        })
        # Falls through to 'other' because startswith("MyIA.AI.Notebooks/") fails
        assert result["series"] == {}
        assert result["other"]["other"] == 1

    def test_shallow_notebook_path(self):
        """MyIA.AI.Notebooks/<file> has parts[1] as file itself (no sub-series)."""
        result = classify_notebook_changes({
            "MyIA.AI.Notebooks/standalone.ipynb",
        })
        # parts = ["MyIA.AI.Notebooks", "standalone.ipynb"] → series = "standalone.ipynb"
        assert len(result["series"]) == 1

    def test_empty_set(self):
        result = classify_notebook_changes(set())
        assert result["series"] == {}
        assert result["other"] == {"python": 0, "csharp": 0, "docs": 0,
                                    "config": 0, "other": 0}


# ---------------------------------------------------------------------------
# classify_notebook_changes — other file types
# ---------------------------------------------------------------------------

class TestClassifyOtherFiles:
    """Tests for non-notebook file classification."""

    def test_python_files(self):
        result = classify_notebook_changes({"scripts/tool.py", "src/main.py"})
        assert result["other"]["python"] == 2

    def test_csharp_files(self):
        result = classify_notebook_changes({"src/Program.cs", "lib/Helper.cs"})
        assert result["other"]["csharp"] == 2

    def test_docs_files(self):
        result = classify_notebook_changes({"README.md", "docs/guide.txt"})
        assert result["other"]["docs"] == 2

    def test_config_files(self):
        result = classify_notebook_changes({"config.json", "settings.yml", "params.yaml"})
        assert result["other"]["config"] == 3

    def test_other_extensions(self):
        result = classify_notebook_changes({"data.csv", "image.png", "Makefile"})
        assert result["other"]["other"] == 3

    def test_mixed_file_types(self):
        result = classify_notebook_changes({
            "script.py", "Main.cs", "README.md", "config.json",
            "data.csv", "MyIA.AI.Notebooks/Search/nb1.ipynb",
        })
        assert result["other"]["python"] == 1
        assert result["other"]["csharp"] == 1
        assert result["other"]["docs"] == 1
        assert result["other"]["config"] == 1
        assert result["other"]["other"] == 1
        assert "Search" in result["series"]


# ---------------------------------------------------------------------------
# classify_notebook_changes — notebook name extraction
# ---------------------------------------------------------------------------

class TestClassifyNotebookNames:
    """Tests for notebook name extraction in series stats."""

    def test_notebook_names_extracted(self):
        result = classify_notebook_changes({
            "MyIA.AI.Notebooks/Search/CSP-7-Soft.ipynb",
            "MyIA.AI.Notebooks/Search/CSP-1-Intro.ipynb",
        })
        names = result["series"]["Search"]["notebook_names"]
        assert "CSP-7-Soft" in names
        assert "CSP-1-Intro" in names

    def test_notebook_names_sorted_by_appearance(self):
        result = classify_notebook_changes({
            "MyIA.AI.Notebooks/Search/aaa.ipynb",
            "MyIA.AI.Notebooks/Search/zzz.ipynb",
        })
        names = result["series"]["Search"]["notebook_names"]
        assert len(names) == 2


# ---------------------------------------------------------------------------
# classify_notebook_changes — edge cases
# ---------------------------------------------------------------------------

class TestClassifyEdgeCases:
    """Tests for edge cases in file classification."""

    def test_deeply_nested_path(self):
        result = classify_notebook_changes({
            "MyIA.AI.Notebooks/GenAI/Image/nb1.ipynb",
        })
        assert "GenAI" in result["series"]

    def test_notebook_path_with_mixed_separators(self):
        """Mixed separators: startswith fails on backslash prefix.

        The code checks startswith('MyIA.AI.Notebooks/') BEFORE any normalization,
        so a backslash in the prefix prevents series detection.
        """
        path = "MyIA.AI.Notebooks" + chr(92) + "GenAI/Image/nb1.ipynb"
        result = classify_notebook_changes({path})
        # Doesn't match the forward-slash prefix, falls to 'other'
        assert result["series"] == {}
        assert result["other"]["other"] == 1

    def test_empty_filename(self):
        result = classify_notebook_changes({""})
        assert result["other"]["other"] == 1

    def test_duplicate_files_counted_once(self):
        """Set semantics prevent duplicates."""
        result = classify_notebook_changes({
            "MyIA.AI.Notebooks/Search/nb1.ipynb",
            "MyIA.AI.Notebooks/Search/nb1.ipynb",
        })
        assert result["series"]["Search"]["files"] == 1
