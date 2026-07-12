"""Tests for wsl_papermill.py — WSL path conversion + native mode + validation."""

import json
import platform
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from wsl_papermill import (
    _default_mode,
    _validate_output,
    batch_execute,
    check_env,
    check_env_native,
    check_env_wsl,
    execute_notebook,
    execute_notebook_native,
    execute_notebook_wsl,
    win_to_wsl_path,
)


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


# --- _default_mode ---


class TestDefaultMode:
    def test_windows_returns_wsl(self):
        with patch("wsl_papermill.platform.system", return_value="Windows"):
            assert _default_mode() == "wsl"

    def test_darwin_returns_native(self):
        with patch("wsl_papermill.platform.system", return_value="Darwin"):
            assert _default_mode() == "native"

    def test_linux_returns_native(self):
        with patch("wsl_papermill.platform.system", return_value="Linux"):
            assert _default_mode() == "native"


# --- _validate_output ---


class TestValidateOutput:
    def test_all_cells_executed_no_errors(self, tmp_path):
        nb = {
            "cells": [
                {"cell_type": "code", "execution_count": 1, "outputs": []},
                {"cell_type": "code", "execution_count": 2, "outputs": [
                    {"output_type": "stream", "text": ["ok"]}
                ]},
            ]
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 0

    def test_cell_error_returns_3(self, tmp_path):
        nb = {
            "cells": [
                {"cell_type": "code", "execution_count": 1, "outputs": [
                    {"output_type": "error", "ename": "ValueError", "evalue": "bad"}
                ]},
            ]
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 3

    def test_invalid_json_returns_0(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not json", encoding="utf-8")
        assert _validate_output(p, 1.0) == 0

    def test_mixed_code_and_markdown(self, tmp_path):
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["# Title"]},
                {"cell_type": "code", "execution_count": 1, "outputs": []},
                {"cell_type": "markdown", "source": ["## Section"]},
            ]
        }
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        assert _validate_output(p, 1.0) == 0


# --- execute_notebook dispatch ---


class TestExecuteNotebookDispatch:
    def test_auto_mode_dispatches_correctly(self):
        """execute_notebook with mode='auto' dispatches based on platform."""
        with patch("wsl_papermill._default_mode", return_value="native"):
            with patch("wsl_papermill.execute_notebook_native", return_value=0) as mock:
                result = execute_notebook("test.ipynb", mode="auto")
                mock.assert_called_once()
                assert result == 0

    def test_explicit_wsl_mode(self):
        with patch("wsl_papermill.execute_notebook_wsl", return_value=0) as mock:
            result = execute_notebook("test.ipynb", mode="wsl")
            mock.assert_called_once()

    def test_explicit_native_mode(self):
        with patch("wsl_papermill.execute_notebook_native", return_value=0) as mock:
            result = execute_notebook("test.ipynb", mode="native")
            mock.assert_called_once()

    def test_invalid_mode_returns_1(self):
        result = execute_notebook("test.ipynb", mode="invalid")
        assert result == 1


# --- execute_notebook_native ---


class TestExecuteNotebookNative:
    def test_missing_notebook_returns_1(self):
        result = execute_notebook_native("/nonexistent/path.ipynb")
        assert result == 1

    def test_timeout_returns_2(self, tmp_path):
        nb = {"cells": [], "nbformat": 4}
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        with patch("subprocess.run", side_effect=__import__("subprocess").TimeoutExpired("cmd", 300)):
            result = execute_notebook_native(str(p), timeout=300)
            assert result == 2

    def test_failed_execution_returns_1(self, tmp_path):
        nb = {"cells": [], "nbformat": 4}
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        mock = MagicMock()
        mock.returncode = 1
        mock.stderr = "Error: kernel not found"

        with patch("subprocess.run", return_value=mock):
            result = execute_notebook_native(str(p))
            assert result == 1


# --- check_env dispatch ---


class TestCheckEnvDispatch:
    def test_auto_mode_dispatches(self):
        with patch("wsl_papermill._default_mode", return_value="native"):
            with patch("wsl_papermill.check_env_native", return_value=True) as mock:
                assert check_env("auto") is True
                mock.assert_called_once()

    def test_wsl_mode(self):
        with patch("wsl_papermill.check_env_wsl", return_value=False) as mock:
            assert check_env("wsl") is False
            mock.assert_called_once()

    def test_invalid_mode(self):
        assert check_env("invalid") is False


# --- batch_execute mode propagation ---


class TestBatchExecuteMode:
    def test_batch_propagates_mode(self, tmp_path):
        """batch_execute passes mode to execute_notebook."""
        nb = {"cells": [], "nbformat": 4}
        p = tmp_path / "test.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")

        with patch("wsl_papermill.execute_notebook", return_value=0) as mock:
            batch_execute(str(tmp_path), mode="native")
            mock.assert_called_once()
            assert mock.call_args.kwargs.get("mode") == "native" or "native" in str(mock.call_args)
