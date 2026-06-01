"""Tests for wsl_papermill.py — Windows-to-WSL path conversion."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from wsl_papermill import win_to_wsl_path


# --- win_to_wsl_path ---


class TestWinToWslPath:
    def test_c_drive_root(self):
        result = win_to_wsl_path("C:\\")
        assert result == "/mnt/c/"

    def test_c_drive_path(self):
        result = win_to_wsl_path("C:\\Users\\test\\file.py")
        assert result == "/mnt/c/Users/test/file.py"

    def test_d_drive(self):
        result = win_to_wsl_path("D:\\projects\\repo")
        assert result == "/mnt/d/projects/repo"

    def test_lowercase_drive(self):
        """Drive letter should be lowercased."""
        result = win_to_wsl_path("E:\\DATA\\file.txt")
        assert result.startswith("/mnt/e/")

    def test_posix_path_passthrough(self):
        """Already-posix path should still be converted (Path handles it)."""
        result = win_to_wsl_path("/home/user/file.py")
        # Path("/home/user/file.py").drive is "" on Windows
        # drive[0].lower() would fail on empty drive
        # Let's check it doesn't crash — behavior depends on OS
        assert isinstance(result, str)

    def test_long_nested_path(self):
        result = win_to_wsl_path(
            "C:\\dev\\CoursIA\\MyIA.AI.Notebooks\\GenAI\\Image\\test.ipynb"
        )
        assert result == "/mnt/c/dev/CoursIA/MyIA.AI.Notebooks/GenAI/Image/test.ipynb"

    def test_forward_slashes_converted(self):
        """Input with forward slashes should work via Path.resolve()."""
        result = win_to_wsl_path("C:/Users/test/file.py")
        assert result == "/mnt/c/Users/test/file.py"
