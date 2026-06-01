#!/usr/bin/env python3
"""
Tests for scripts/genai-stack/commands/notebooks.py

Covers testable units: NotebookValidator init, find_notebooks,
find_notebooks_by_group, find_notebooks_by_batch, save_report.
Network/papermill methods (validate_notebook, run_validation) and
CLI (execute, main, register) are excluded.
"""

import json
import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

# Add genai-stack to sys.path
_genai_dir = str(Path(__file__).resolve().parent.parent / "genai-stack")
if _genai_dir not in sys.path:
    sys.path.insert(0, _genai_dir)

# Mock GenAIAuthManager before importing notebooks to prevent
# real filesystem side-effects in PROJECT_ROOT/.secrets/
_mock_auth = MagicMock()
_mock_auth_instance = MagicMock()
_mock_auth_instance.load_config.return_value = {"bcrypt_hash": "$2b$12$testhash"}
_mock_auth.return_value = _mock_auth_instance

with patch("commands.notebooks.GenAIAuthManager", _mock_auth):
    from commands.notebooks import NotebookValidator


# ─── NotebookValidator.__init__ ──────────────────────────────────────


class TestNotebookValidatorInit:
    def _make(self, target_path):
        with patch("commands.notebooks.GenAIAuthManager", _mock_auth):
            return NotebookValidator(target_path)

    def test_target_path_stored(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert v.target_path == Path(tmpdir)

    def test_token_from_config(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert v.token == "$2b$12$testhash"

    def test_env_vars_is_dict(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert isinstance(v.env_vars, dict)

    def test_env_vars_comfyui_url(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert v.env_vars["COMFYUI_URL"] == "http://localhost:8188"

    def test_env_vars_batch_mode(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert v.env_vars["BATCH_MODE"] == "true"

    def test_env_vars_contains_auth_token(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert "$2b$12$testhash" in v.env_vars["COMFYUI_AUTH_TOKEN"]

    def test_env_vars_has_whisper_device(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert "WHISPER_DEVICE" in v.env_vars

    def test_env_vars_has_audio_output_dir(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert "AUDIO_OUTPUT_DIR" in v.env_vars

    def test_env_vars_has_video_output_dir(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert "VIDEO_OUTPUT_DIR" in v.env_vars


class TestNotebookValidatorInitNoConfig:
    """When auth manager has no config (load_config returns None)."""

    def test_token_none_without_config(self):
        mock_auth = MagicMock()
        # GenAIAuthManager() returns mock_auth(), whose .load_config() returns None
        mock_auth.return_value.load_config.return_value = None
        with tempfile.TemporaryDirectory() as tmpdir:
            with patch("commands.notebooks.GenAIAuthManager", mock_auth):
                # Clear env var to ensure fallback also fails
                with patch.dict(os.environ, {}, clear=True):
                    v = NotebookValidator(tmpdir)
                    assert v.token is None or v.token == ""

    def test_fallback_to_env_var(self):
        mock_auth = MagicMock()
        mock_auth.return_value.load_config.return_value = None
        with tempfile.TemporaryDirectory() as tmpdir:
            with patch("commands.notebooks.GenAIAuthManager", mock_auth):
                with patch.dict(os.environ, {"COMFYUI_AUTH_TOKEN": "env-token-123"}):
                    v = NotebookValidator(tmpdir)
                    assert v.token == "env-token-123"


# ─── NotebookValidator.find_notebooks ────────────────────────────────


class TestNotebookValidatorFindNotebooks:
    def _make(self, target):
        with patch("commands.notebooks.GenAIAuthManager", _mock_auth):
            return NotebookValidator(target)

    def test_single_file_ipynb(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            nb = Path(tmpdir) / "test.ipynb"
            nb.write_text("{}", encoding="utf-8")
            v = self._make(str(nb))
            found = v.find_notebooks()
            assert len(found) == 1
            assert found[0] == nb

    def test_single_file_non_ipynb(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            txt = Path(tmpdir) / "readme.txt"
            txt.write_text("hello", encoding="utf-8")
            v = self._make(str(txt))
            found = v.find_notebooks()
            assert found == []

    def test_directory_with_notebooks(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            (Path(tmpdir) / "a.ipynb").write_text("{}", encoding="utf-8")
            (Path(tmpdir) / "b.ipynb").write_text("{}", encoding="utf-8")
            (Path(tmpdir) / "c.txt").write_text("x", encoding="utf-8")
            v = self._make(tmpdir)
            found = v.find_notebooks()
            assert len(found) == 2
            assert all(f.suffix == ".ipynb" for f in found)

    def test_empty_directory(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            assert v.find_notebooks() == []

    def test_nested_notebooks(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            sub = Path(tmpdir) / "sub"
            sub.mkdir()
            (sub / "nested.ipynb").write_text("{}", encoding="utf-8")
            v = self._make(tmpdir)
            found = v.find_notebooks()
            assert len(found) == 1

    def test_returns_list_of_paths(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            (Path(tmpdir) / "x.ipynb").write_text("{}", encoding="utf-8")
            v = self._make(tmpdir)
            found = v.find_notebooks()
            assert all(isinstance(f, Path) for f in found)


# ─── NotebookValidator.find_notebooks_by_group ───────────────────────


class TestNotebookValidatorFindByGroup:
    def _make(self, target):
        with patch("commands.notebooks.GenAIAuthManager", _mock_auth):
            return NotebookValidator(target)

    def test_unknown_group_returns_empty(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            # Patch NOTEBOOK_SERVICE_MAP to control the test
            with patch("commands.notebooks.NOTEBOOK_SERVICE_MAP", {}):
                result = v.find_notebooks_by_group("nonexistent")
                assert result == []

    def test_group_with_matching_files(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            nb = Path(tmpdir) / "test_nb.ipynb"
            nb.write_text("{}", encoding="utf-8")
            v = self._make(tmpdir)
            with patch("commands.notebooks.NOTEBOOK_SERVICE_MAP", {"img": ["test_nb.ipynb"]}):
                with patch("commands.notebooks.NOTEBOOK_SEARCH_DIRS", {"main": Path(tmpdir)}):
                    with patch("commands.notebooks.GENAI_DIR", Path(tmpdir)):
                        found = v.find_notebooks_by_group("img")
                        assert len(found) == 1

    def test_group_with_missing_notebook(self):
        """Missing notebooks in group are skipped (logged, not raised)."""
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            with patch("commands.notebooks.NOTEBOOK_SERVICE_MAP", {"g": ["absent.ipynb"]}):
                with patch("commands.notebooks.NOTEBOOK_SEARCH_DIRS", {"main": Path(tmpdir)}):
                    with patch("commands.notebooks.GENAI_DIR", Path(tmpdir)):
                        found = v.find_notebooks_by_group("g")
                        assert found == []

    def test_returns_list(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            with patch("commands.notebooks.NOTEBOOK_SERVICE_MAP", {"g": []}):
                result = v.find_notebooks_by_group("g")
                assert isinstance(result, list)


# ─── NotebookValidator.find_notebooks_by_batch ───────────────────────


class TestNotebookValidatorFindByBatch:
    def _make(self, target):
        with patch("commands.notebooks.GenAIAuthManager", _mock_auth):
            return NotebookValidator(target)

    def test_unknown_batch_returns_empty(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            with patch("commands.notebooks.EXECUTION_BATCHES", {}):
                result = v.find_notebooks_by_batch(99)
                assert result == []

    def test_batch_aggregates_groups(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            nb1 = Path(tmpdir) / "a.ipynb"
            nb2 = Path(tmpdir) / "b.ipynb"
            nb1.write_text("{}", encoding="utf-8")
            nb2.write_text("{}", encoding="utf-8")
            v = self._make(tmpdir)
            batches = {1: {"name": "test", "profile": "default", "groups": ["g1", "g2"]}}
            svc_map = {"g1": ["a.ipynb"], "g2": ["b.ipynb"]}
            with patch("commands.notebooks.EXECUTION_BATCHES", batches):
                with patch("commands.notebooks.NOTEBOOK_SERVICE_MAP", svc_map):
                    with patch("commands.notebooks.NOTEBOOK_SEARCH_DIRS", {"m": Path(tmpdir)}):
                        with patch("commands.notebooks.GENAI_DIR", Path(tmpdir)):
                            found = v.find_notebooks_by_batch(1)
                            assert len(found) == 2

    def test_returns_list(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            with patch("commands.notebooks.EXECUTION_BATCHES", {1: {"groups": []}}):
                result = v.find_notebooks_by_batch(1)
                assert isinstance(result, list)


# ─── NotebookValidator.save_report ───────────────────────────────────


class TestNotebookValidatorSaveReport:
    def _make(self, target):
        with patch("commands.notebooks.GenAIAuthManager", _mock_auth):
            return NotebookValidator(target)

    def test_creates_json_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            results = [
                {"notebook": "a.ipynb", "status": "success", "duration": 1.0,
                 "error": None, "output_path": "/tmp/a_out.ipynb"},
            ]
            orig_cwd = os.getcwd()
            os.chdir(tmpdir)
            try:
                v.save_report(results)
                report_path = Path(tmpdir) / "notebook_validation_report.json"
                assert report_path.exists()
            finally:
                os.chdir(orig_cwd)

    def test_report_structure(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            results = [
                {"notebook": "a.ipynb", "status": "success", "duration": 1.0,
                 "error": None, "output_path": "/tmp/a_out.ipynb"},
                {"notebook": "b.ipynb", "status": "failed", "duration": 2.0,
                 "error": "Error msg", "output_path": "/tmp/b_out.ipynb"},
            ]
            orig_cwd = os.getcwd()
            os.chdir(tmpdir)
            try:
                v.save_report(results)
                with open(Path(tmpdir) / "notebook_validation_report.json", encoding="utf-8") as f:
                    report = json.load(f)
                assert "timestamp" in report
                assert report["total_notebooks"] == 2
                assert report["passed"] == 1
                assert report["failed"] == 1
                assert len(report["results"]) == 2
            finally:
                os.chdir(orig_cwd)

    def test_report_all_passed(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            results = [
                {"notebook": "a.ipynb", "status": "success", "duration": 1.0,
                 "error": None, "output_path": "/tmp/a.ipynb"},
            ]
            orig_cwd = os.getcwd()
            os.chdir(tmpdir)
            try:
                v.save_report(results)
                with open(Path(tmpdir) / "notebook_validation_report.json", encoding="utf-8") as f:
                    report = json.load(f)
                assert report["passed"] == 1
                assert report["failed"] == 0
            finally:
                os.chdir(orig_cwd)

    def test_report_empty_results(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            orig_cwd = os.getcwd()
            os.chdir(tmpdir)
            try:
                v.save_report([])
                with open(Path(tmpdir) / "notebook_validation_report.json", encoding="utf-8") as f:
                    report = json.load(f)
                assert report["total_notebooks"] == 0
                assert report["passed"] == 0
                assert report["failed"] == 0
            finally:
                os.chdir(orig_cwd)

    def test_report_json_valid(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            v = self._make(tmpdir)
            results = [
                {"notebook": "a.ipynb", "status": "success", "duration": 0.5,
                 "error": None, "output_path": "/out"},
            ]
            orig_cwd = os.getcwd()
            os.chdir(tmpdir)
            try:
                v.save_report(results)
                with open(Path(tmpdir) / "notebook_validation_report.json", encoding="utf-8") as f:
                    data = json.load(f)
                # Verify all keys are present
                assert set(data.keys()) >= {"timestamp", "total_notebooks", "passed", "failed", "results"}
            finally:
                os.chdir(orig_cwd)


# ─── Cross-invariants ────────────────────────────────────────────────


class TestCrossInvariants:
    def test_find_notebooks_returns_subset_of_init_target(self):
        """All found notebooks should live within the target path."""
        with tempfile.TemporaryDirectory() as tmpdir:
            (Path(tmpdir) / "a.ipynb").write_text("{}", encoding="utf-8")
            with patch("commands.notebooks.GenAIAuthManager", _mock_auth):
                v = NotebookValidator(tmpdir)
            found = v.find_notebooks()
            for f in found:
                assert str(f).startswith(tmpdir)

    def test_env_vars_has_all_expected_keys(self):
        """Check critical env vars are present for notebook execution."""
        with tempfile.TemporaryDirectory() as tmpdir:
            with patch("commands.notebooks.GenAIAuthManager", _mock_auth):
                v = NotebookValidator(tmpdir)
            expected_keys = [
                "COMFYUI_URL", "COMFYUI_AUTH_TOKEN", "BATCH_MODE",
                "WHISPER_DEVICE", "AUDIO_OUTPUT_DIR", "VIDEO_OUTPUT_DIR",
            ]
            for key in expected_keys:
                assert key in v.env_vars, f"Missing env var: {key}"

    def test_report_counts_match_results(self):
        """passed + failed == total_notebooks."""
        with tempfile.TemporaryDirectory() as tmpdir:
            with patch("commands.notebooks.GenAIAuthManager", _mock_auth):
                v = NotebookValidator(tmpdir)
            results = [
                {"notebook": "a.ipynb", "status": "success", "duration": 1, "error": None, "output_path": ""},
                {"notebook": "b.ipynb", "status": "failed", "duration": 2, "error": "err", "output_path": ""},
                {"notebook": "c.ipynb", "status": "success", "duration": 3, "error": None, "output_path": ""},
            ]
            orig_cwd = os.getcwd()
            os.chdir(tmpdir)
            try:
                v.save_report(results)
                with open(Path(tmpdir) / "notebook_validation_report.json", encoding="utf-8") as f:
                    report = json.load(f)
                assert report["total_notebooks"] == 3
                assert report["passed"] + report["failed"] == report["total_notebooks"]
            finally:
                os.chdir(orig_cwd)
