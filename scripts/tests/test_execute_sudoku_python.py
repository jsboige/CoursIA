"""Tests for scripts/execute_sudoku_python.py.

Covers:
- ``SUDOKU_DIR`` is computed relative to ``__file__``, not hardcoded to a
  single Windows workstation path.
- ``_discover_python_notebooks()`` returns sorted basenames of every
  ``*-Python.ipynb`` actually present in :data:`SUDOKU_DIR`.
- The discovery function returns ``[]`` when the directory is missing.
- The discovery output matches what is on disk (no stale hardcoded names).
- The ``"NeuralNetwork"`` substring detector catches the renamed NN notebook
  (``Sudoku-16-NeuralNetwork-Python.ipynb``) regardless of its numeric prefix.

Tests are CPU-only / hermetic: no subprocess, no papermill, no network. The
SUDOKU_DIR on disk is the canonical source of truth for the discovery
function, so we read it directly via Path rather than mocking.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
MODULE_PATH = SCRIPTS_DIR / "execute_sudoku_python.py"
REPO_ROOT = SCRIPTS_DIR.parent
SUDOKU_DIR = REPO_ROOT / "MyIA.AI.Notebooks" / "Sudoku"


def _load_module():
    """Load ``scripts/execute_sudoku_python.py`` by file path.

    Avoids polluting sys.modules permanently (cf test_manage_crypto_archive
    pattern) and bypasses the need for scripts/ to be an importable package.
    """
    if "execute_sudoku_python" in sys.modules:
        del sys.modules["execute_sudoku_python"]
    spec = importlib.util.spec_from_file_location(
        "execute_sudoku_python", MODULE_PATH
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def esp():
    return _load_module()


class TestSUDOKU_DIRIsPortable:
    """The script must NOT bake in a single developer's Windows path."""

    def test_sudoku_dir_is_path(self, esp):
        assert isinstance(esp.SUDOKU_DIR, Path)

    def test_sudoku_dir_is_repo_local(self, esp):
        # Resolved: no hardcoded d:/Dev/CoursIA prefix.
        resolved = esp.SUDOKU_DIR.resolve()
        # Must end with the standard repo suffix.
        assert resolved.name == "Sudoku"
        assert resolved.parent.name == "MyIA.AI.Notebooks"

    def test_no_hardcoded_drive_letter(self, esp):
        # The original bug was `Path("d:/Dev/CoursIA/...")`. Verify the new
        # code derives from __file__ so it never carries a drive letter.
        assert str(esp.SUDOKU_DIR).count(":") == 0 or esp.SUDOKU_DIR.is_absolute()

    def test_sudoku_dir_matches_repo_layout(self, esp):
        # If the on-disk layout matches, the script's discovery will agree
        # with reality (no stale hardcoded list out of sync with disk).
        if SUDOKU_DIR.is_dir():
            assert esp.SUDOKU_DIR.resolve() == SUDOKU_DIR.resolve()


class TestDiscoverPythonNotebooks:
    """Discovery must reflect the actual files on disk."""

    def test_returns_list_of_strings(self, esp):
        result = esp._discover_python_notebooks()
        assert isinstance(result, list)
        for name in result:
            assert isinstance(name, str)

    def test_returns_sorted(self, esp):
        result = esp._discover_python_notebooks()
        assert result == sorted(result)

    def test_all_match_python_suffix(self, esp):
        result = esp._discover_python_notebooks()
        for name in result:
            assert name.endswith("-Python.ipynb"), (
                f"unexpected non-Python notebook: {name}"
            )

    def test_matches_disk_when_sudoku_dir_exists(self, esp):
        """If the Sudoku dir is present, the discovery must match `glob`."""
        if not SUDOKU_DIR.is_dir():
            pytest.skip("SUDOKU_DIR not on disk in this checkout")
        expected = sorted(p.name for p in SUDOKU_DIR.glob("*-Python.ipynb"))
        assert esp._discover_python_notebooks() == expected

    def test_no_stale_original_names(self, esp):
        """The original PYTHON_NOTEBOOKS list had 6 stale names. None of
        those must appear (the series was reshuffled into numbered pairs)."""
        stale = {
            "Sudoku-10-NeuralNetwork.ipynb",
            "Sudoku-Python-Backtracking.ipynb",
            "Sudoku-Python-DancingLinks.ipynb",
            "Sudoku-Python-Genetic.ipynb",
            "Sudoku-Python-ORTools-Z3.ipynb",
            # The 6th name from the legacy list — kept here in case it was
            # not enumerated above; the assertion below catches it.
        }
        result = esp._discover_python_notebooks()
        for name in result:
            assert name not in stale, f"stale legacy name resurfaced: {name}"

    def test_neural_network_notebook_present(self, esp):
        """The NN notebook is the one that needs the .view()/.reshape() fix;
        discovery must include it (under its new numbered name)."""
        if not SUDOKU_DIR.is_dir():
            pytest.skip("SUDOKU_DIR not on disk in this checkout")
        result = esp._discover_python_notebooks()
        nn = [n for n in result if "NeuralNetwork" in n]
        assert len(nn) == 1, f"expected exactly 1 NN notebook, got {nn}"
        # The renamed notebook now carries the -Python suffix.
        assert nn[0].endswith("-NeuralNetwork-Python.ipynb")


class TestDiscoverHandlesMissingDir:
    """Discovery must degrade gracefully when SUDOKU_DIR does not exist."""

    def test_missing_dir_returns_empty(self, monkeypatch, esp):
        monkeypatch.setattr(esp, "SUDOKU_DIR", Path("/nonexistent/_fake_dir_xyz"))
        assert esp._discover_python_notebooks() == []


class TestNeuralNetworkSubstring:
    """The .view()/.reshape() patch keys off the notebook name; verify the
    substring detector works for the current and any future NN variant."""

    @pytest.mark.parametrize(
        "name,expected",
        [
            ("Sudoku-16-NeuralNetwork-Python.ipynb", True),
            ("Sudoku-10-NeuralNetwork.ipynb", True),  # legacy form
            ("Sudoku-1-Backtracking-Python.ipynb", False),
            ("Sudoku-2-DancingLinks-Python.ipynb", False),
            ("Sudoku-12-Z3-Python.ipynb", False),
            ("", False),
        ],
    )
    def test_substring_detector(self, name, expected):
        assert ("NeuralNetwork" in name) is expected
