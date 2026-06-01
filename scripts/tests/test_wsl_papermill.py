"""Tests for scripts/notebook_tools/wsl_papermill.py — WSL papermill executor.

Tests focus on the pure function: win_to_wsl_path.
WSL-dependent functions (run_wsl, check_env, execute_notebook, batch_execute)
are not tested (require WSL runtime).
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from wsl_papermill import win_to_wsl_path, WSL_VENV, WSL_PAPERMILL_CMD, REPO_ROOT


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    def test_wsl_venv_path(self):
        """WSL_VENV points to home coursia-wsl."""
        assert WSL_VENV == "~/coursia-wsl"

    def test_papermill_cmd_uses_venv(self):
        """WSL_PAPERMILL_CMD activates the venv before papermill."""
        assert "coursia-wsl" in WSL_PAPERMILL_CMD
        assert "papermill" in WSL_PAPERMILL_CMD
        assert "source" in WSL_PAPERMILL_CMD
        assert "activate" in WSL_PAPERMILL_CMD

    def test_repo_root_is_path(self):
        """REPO_ROOT is a Path object."""
        assert isinstance(REPO_ROOT, Path)

    def test_repo_root_points_to_repo(self):
        """REPO_ROOT points to the CoursIA repository root."""
        # Should contain CLAUDE.md
        assert (REPO_ROOT / "CLAUDE.md").exists()


# ---------------------------------------------------------------------------
# win_to_wsl_path
# ---------------------------------------------------------------------------

class TestWinToWslPath:
    def test_simple_c_drive(self):
        """C: drive maps to /mnt/c."""
        result = win_to_wsl_path("C:\\Users\\test\\file.txt")
        assert result.startswith("/mnt/c/")
        assert "Users/test/file.txt" in result

    def test_d_drive(self):
        """D: drive maps to /mnt/d."""
        result = win_to_wsl_path("D:\\dev\\project")
        assert result.startswith("/mnt/d/")
        assert "dev/project" in result

    def test_lowercase_drive(self):
        """Drive letter is lowercased in WSL path."""
        result = win_to_wsl_path("E:\\data")
        assert result.startswith("/mnt/e/")

    def test_uppercase_drive(self):
        """Uppercase drive letter is lowercased."""
        result = win_to_wsl_path("F:\\path")
        assert result.startswith("/mnt/f/")

    def test_forward_slashes(self):
        """Forward slashes in input also work (Path resolves them)."""
        result = win_to_wsl_path("C:/Users/test")
        assert result.startswith("/mnt/c/")

    def test_root_drive(self):
        """Root of a drive."""
        # Path("C:\\").resolve() on Windows typically gives "C:\"
        result = win_to_wsl_path("C:\\")
        assert "/mnt/c/" in result

    def test_long_path(self):
        """Deep nested path."""
        result = win_to_wsl_path("D:\\dev\\CoursIA-2\\MyIA.AI.Notebooks\\Sudoku\\nb.ipynb")
        assert "/mnt/d/" in result
        assert "Sudoku/nb.ipynb" in result

    def test_no_backslash_in_output(self):
        """WSL path never contains backslashes."""
        result = win_to_wsl_path("C:\\Users\\test\\file.txt")
        assert "\\" not in result

    def test_starts_with_mnt(self):
        """Output always starts with /mnt/."""
        result = win_to_wsl_path("D:\\anything")
        assert result.startswith("/mnt/")

    def test_posix_format(self):
        """Output uses forward slashes (POSIX)."""
        result = win_to_wsl_path("C:\\a\\b\\c")
        parts = result.split("/")
        assert "mnt" in parts
        assert "c" in parts
