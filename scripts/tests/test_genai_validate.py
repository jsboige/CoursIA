"""Tests for scripts/genai-stack/commands/validate.py — GenAI stack validator.

Tests focus on pure testable logic: BatchNotebookValidator (syntax validation,
group dispatch, full validation, summary) and ModelSwitcher.switch_to (model
name validation, VRAM mock). Network-dependent classes (ComfyUIValidator,
VRAMManager, check_*_api) are excluded — they require live services.
"""

import json
import sys
from pathlib import Path
from typing import Any, Dict, Optional
from unittest.mock import MagicMock

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "genai-stack"))
from commands.validate import BatchNotebookValidator, ModelSwitcher
from config import MODEL_CONFIGS, NOTEBOOK_SERVICE_MAP, NOTEBOOK_SERIES


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


class FakeVRAMManager:
    """Mock VRAMManager with controllable stats."""

    def __init__(self, stats: Optional[Dict] = None, free_error: bool = False):
        self._stats = stats or {}
        self._free_error = free_error

    def free_vram(self, unload_models: bool = True) -> dict:
        if self._free_error:
            return {"error": "connection failed"}
        return {"freed": True}

    def get_vram_stats(self) -> dict:
        return self._stats


def _write_nb(path: Path, cells: list | None = None, metadata: dict | None = None) -> Path:
    """Write a minimal notebook file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    if cells is None:
        cells = [{"cell_type": "code", "source": "print('hello')"}]
    nb = {
        "cells": cells,
        "metadata": metadata or {"kernelspec": {"display_name": "Python 3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# ModelSwitcher.switch_to
# ---------------------------------------------------------------------------


class TestModelSwitcher:
    """Tests for ModelSwitcher.switch_to logic."""

    def test_unknown_model_returns_false(self):
        """Switching to unknown model returns False."""
        vram = FakeVRAMManager()
        switcher = ModelSwitcher(vram)
        assert switcher.switch_to("nonexistent_model") is False

    def test_known_model_returns_true(self):
        """Switching to known model returns True."""
        vram = FakeVRAMManager(stats={"vram_free": 20 * 1024 * 1024 * 1024})
        switcher = ModelSwitcher(vram)
        assert switcher.switch_to("nunchaku") is True

    def test_same_model_no_switch(self):
        """Switching to same model returns True without VRAM free."""
        vram = FakeVRAMManager()
        switcher = ModelSwitcher(vram)
        switcher.current_model = "qwen"
        assert switcher.switch_to("qwen") is True

    def test_switch_updates_current_model(self):
        """After switch, current_model is updated."""
        vram = FakeVRAMManager(stats={"vram_free": 20 * 1024 * 1024 * 1024})
        switcher = ModelSwitcher(vram)
        switcher.switch_to("nunchaku")
        assert switcher.current_model == "nunchaku"

    def test_switch_with_vram_error_still_succeeds(self):
        """VRAM free error is warned but switch still proceeds."""
        vram = FakeVRAMManager(free_error=True)
        switcher = ModelSwitcher(vram)
        assert switcher.switch_to("qwen") is True

    def test_all_model_configs_switchable(self):
        """Every entry in MODEL_CONFIGS is a valid switch target."""
        vram = FakeVRAMManager(stats={"vram_free": 30 * 1024 * 1024 * 1024})
        switcher = ModelSwitcher(vram)
        for model_name in MODEL_CONFIGS:
            assert switcher.switch_to(model_name) is True


# ---------------------------------------------------------------------------
# BatchNotebookValidator._validate_notebook_syntax
# ---------------------------------------------------------------------------


class TestValidateNotebookSyntax:
    """Tests for notebook JSON syntax validation."""

    def _make_validator(self, tmp_path: Path) -> BatchNotebookValidator:
        switcher = MagicMock()
        switcher.switch_to.return_value = True
        return BatchNotebookValidator(switcher, notebooks_dir=tmp_path)

    def test_valid_notebook(self, tmp_path):
        """Valid notebook returns valid=True with cell counts."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "x = 1"},
            {"cell_type": "markdown", "source": "# Title"},
            {"cell_type": "code", "source": "y = 2"},
        ])
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 3
        assert result["code_cells"] == 2

    def test_missing_cells_key(self, tmp_path):
        """Notebook without cells key returns error."""
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text(json.dumps({"metadata": {}}), encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "cells" in result["error"]

    def test_missing_metadata_key(self, tmp_path):
        """Notebook without metadata key returns error."""
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text(json.dumps({"cells": []}), encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "metadata" in result["error"]

    def test_invalid_json(self, tmp_path):
        """Invalid JSON returns error."""
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text("{invalid json", encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "JSON" in result["error"]

    def test_empty_notebook(self, tmp_path):
        """Empty notebook (0 cells) is valid with cell_count=0."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [])
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 0
        assert result["code_cells"] == 0

    def test_path_included_in_result(self, tmp_path):
        """Result includes the notebook path."""
        nb_path = _write_nb(tmp_path / "test.ipynb")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert str(nb_path) in result.get("path", "")

    def test_all_markdown_cells(self, tmp_path):
        """Notebook with only markdown cells has code_cells=0."""
        nb_path = _write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown", "source": "# A"},
            {"cell_type": "markdown", "source": "## B"},
        ])
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["code_cells"] == 0


# ---------------------------------------------------------------------------
# BatchNotebookValidator._find_notebook
# ---------------------------------------------------------------------------


class TestFindNotebook:
    """Tests for notebook file discovery."""

    def _make_validator(self, tmp_path: Path) -> BatchNotebookValidator:
        switcher = MagicMock()
        return BatchNotebookValidator(switcher, notebooks_dir=tmp_path)

    def test_exact_match(self, tmp_path):
        """Finds notebook by exact name."""
        _write_nb(tmp_path / "01-Intro.ipynb")
        v = self._make_validator(tmp_path)
        result = v._find_notebook("01-Intro.ipynb")
        assert result is not None
        assert result.name == "01-Intro.ipynb"

    def test_subdirectory_match(self, tmp_path):
        """Finds notebook in subdirectory."""
        _write_nb(tmp_path / "Image" / "01-Intro.ipynb")
        v = self._make_validator(tmp_path)
        result = v._find_notebook("01-Intro.ipynb")
        assert result is not None

    def test_fuzzy_match(self, tmp_path):
        """Finds notebook by partial name match."""
        _write_nb(tmp_path / "01-1-OpenAI-DALL-E-3.ipynb")
        v = self._make_validator(tmp_path)
        result = v._find_notebook("DALL-E-3")
        assert result is not None

    def test_not_found(self, tmp_path):
        """Returns None for non-existent notebook."""
        v = self._make_validator(tmp_path)
        result = v._find_notebook("nonexistent.ipynb")
        assert result is None

    def test_fuzzy_skips_non_ipynb(self, tmp_path):
        """Fuzzy match ignores non-.ipynb files."""
        (tmp_path / "notes.txt").write_text("not a notebook", encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._find_notebook("notes")
        assert result is None


# ---------------------------------------------------------------------------
# BatchNotebookValidator.validate_group
# ---------------------------------------------------------------------------


class TestValidateGroup:
    """Tests for group-level validation dispatch."""

    def _make_validator(self, tmp_path: Path) -> BatchNotebookValidator:
        switcher = MagicMock()
        return BatchNotebookValidator(switcher, notebooks_dir=tmp_path)

    def test_unknown_group(self, tmp_path):
        """Unknown group returns error dict."""
        v = self._make_validator(tmp_path)
        result = v.validate_group("nonexistent_group")
        assert "error" in result

    def test_valid_group_with_notebooks(self, tmp_path):
        """Valid group finds and validates notebooks."""
        for nb_name in NOTEBOOK_SERVICE_MAP.get("cloud", []):
            _write_nb(tmp_path / nb_name)
        v = self._make_validator(tmp_path)
        result = v.validate_group("cloud")
        assert "cloud" in v.results
        for nb_name in NOTEBOOK_SERVICE_MAP["cloud"]:
            assert nb_name in result

    def test_missing_notebook_reported(self, tmp_path):
        """Missing notebooks are reported as invalid."""
        v = self._make_validator(tmp_path)
        # "cloud" group exists but no files written
        result = v.validate_group("cloud")
        for nb_name in NOTEBOOK_SERVICE_MAP["cloud"]:
            assert result[nb_name]["valid"] is False

    def test_results_stored(self, tmp_path):
        """Results are stored in validator.results dict."""
        v = self._make_validator(tmp_path)
        v.validate_group("cloud")
        assert "cloud" in v.results


# ---------------------------------------------------------------------------
# BatchNotebookValidator.run_full_validation
# ---------------------------------------------------------------------------


class TestRunFullValidation:
    """Tests for full validation orchestration."""

    def _make_validator(self, tmp_path: Path) -> BatchNotebookValidator:
        switcher = MagicMock()
        return BatchNotebookValidator(switcher, notebooks_dir=tmp_path)

    def test_specific_series(self, tmp_path):
        """Validating a specific series only checks that series' groups."""
        v = self._make_validator(tmp_path)
        v.run_full_validation(series="image")
        # Image series groups should be in results
        for group in NOTEBOOK_SERIES["image"]:
            assert group in v.results

    def test_all_groups_when_no_series(self, tmp_path):
        """No series specified validates all groups."""
        v = self._make_validator(tmp_path)
        v.run_full_validation()
        assert len(v.results) == len(NOTEBOOK_SERVICE_MAP)

    def test_unknown_series_as_single_group(self, tmp_path):
        """Unknown series name is treated as a single group."""
        v = self._make_validator(tmp_path)
        v.run_full_validation(series="cloud")
        # "cloud" is a valid group name but not a series name
        # It should try to validate it as a group
        assert len(v.results) >= 1

    def test_returns_results_dict(self, tmp_path):
        """Returns the results dictionary."""
        v = self._make_validator(tmp_path)
        result = v.run_full_validation()
        assert isinstance(result, dict)


# ---------------------------------------------------------------------------
# BatchNotebookValidator.print_summary
# ---------------------------------------------------------------------------


class TestPrintSummary:
    """Tests for print_summary logic."""

    def _make_validator(self, tmp_path: Path) -> BatchNotebookValidator:
        switcher = MagicMock()
        return BatchNotebookValidator(switcher, notebooks_dir=tmp_path)

    def test_all_valid_returns_true(self, tmp_path):
        """All valid notebooks returns True."""
        v = self._make_validator(tmp_path)
        v.results = {
            "cloud": {
                "nb1.ipynb": {"valid": True},
                "nb2.ipynb": {"valid": True},
            }
        }
        assert v.print_summary() is True

    def test_some_invalid_returns_false(self, tmp_path):
        """Some invalid notebooks returns False."""
        v = self._make_validator(tmp_path)
        v.results = {
            "cloud": {
                "nb1.ipynb": {"valid": True},
                "nb2.ipynb": {"valid": False, "error": "missing"},
            }
        }
        assert v.print_summary() is False

    def test_empty_results_returns_true(self, tmp_path):
        """No results to summarize returns True (vacuous truth)."""
        v = self._make_validator(tmp_path)
        v.results = {}
        assert v.print_summary() is True

    def test_all_invalid_returns_false(self, tmp_path):
        """All invalid returns False."""
        v = self._make_validator(tmp_path)
        v.results = {
            "cloud": {
                "nb1.ipynb": {"valid": False, "error": "x"},
            }
        }
        assert v.print_summary() is False


# ---------------------------------------------------------------------------
# Integration: validate_group with real notebooks
# ---------------------------------------------------------------------------


class TestValidateGroupIntegration:
    """Integration tests for validate_group with real notebook files."""

    def _make_validator(self, tmp_path: Path) -> BatchNotebookValidator:
        switcher = MagicMock()
        return BatchNotebookValidator(switcher, notebooks_dir=tmp_path)

    def test_cloud_group_all_found(self, tmp_path):
        """Cloud group with all notebooks present validates fully."""
        for nb_name in NOTEBOOK_SERVICE_MAP["cloud"]:
            _write_nb(tmp_path / nb_name)
        v = self._make_validator(tmp_path)
        result = v.validate_group("cloud")
        valid_count = sum(1 for r in result.values() if r.get("valid"))
        assert valid_count == len(NOTEBOOK_SERVICE_MAP["cloud"])

    def test_mixed_found_missing(self, tmp_path):
        """Some notebooks present, some missing."""
        group_nbs = NOTEBOOK_SERVICE_MAP["cloud"]
        _write_nb(tmp_path / group_nbs[0])
        # Skip the rest
        v = self._make_validator(tmp_path)
        result = v.validate_group("cloud")
        assert result[group_nbs[0]]["valid"] is True
        assert result[group_nbs[1]]["valid"] is False

    def test_invalid_notebook_detected(self, tmp_path):
        """Invalid JSON in a notebook is caught."""
        nb_name = NOTEBOOK_SERVICE_MAP["cloud"][0]
        nb_path = tmp_path / nb_name
        nb_path.write_text("NOT VALID JSON{{{", encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v.validate_group("cloud")
        assert result[nb_name]["valid"] is False
        assert "JSON" in result[nb_name]["error"]

    def test_notebook_missing_cells_detected(self, tmp_path):
        """Notebook without cells key is caught."""
        nb_name = NOTEBOOK_SERVICE_MAP["cloud"][0]
        nb_path = tmp_path / nb_name
        nb_path.write_text(json.dumps({"metadata": {}}), encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v.validate_group("cloud")
        assert result[nb_name]["valid"] is False
