"""Round 3 tests for genai-stack — validate.py + notebooks.py pure logic.

Targets: BatchNotebookValidator._validate_notebook_syntax, _find_notebook,
validate_group, print_summary, ModelSwitcher.switch_to (partial mock),
NotebookValidator.find_notebooks, save_report.
"""

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# conftest.py adds genai-stack root to sys.path


# =============================================================================
# BatchNotebookValidator._validate_notebook_syntax
# =============================================================================


class TestValidateNotebookSyntax:
    """Tests for BatchNotebookValidator._validate_notebook_syntax."""

    def _make_validator(self, tmp_path):
        from commands.validate import BatchNotebookValidator
        switcher = MagicMock()
        switcher.switch_to.return_value = True
        return BatchNotebookValidator(switcher, notebooks_dir=tmp_path)

    def test_valid_notebook(self, tmp_path):
        """Valid notebook returns valid=True with cell counts."""
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text(json.dumps({
            "cells": [
                {"cell_type": "code", "source": ["print('hi')"]},
                {"cell_type": "markdown", "source": ["# Title"]},
            ],
            "metadata": {"kernelspec": {}},
            "nbformat": 4,
            "nbformat_minor": 5,
        }), encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 2
        assert result["code_cells"] == 1

    def test_missing_cells_key(self, tmp_path):
        """Notebook without 'cells' key is invalid."""
        nb_path = tmp_path / "bad.ipynb"
        nb_path.write_text(json.dumps({"metadata": {}}), encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "cells" in result["error"]

    def test_missing_metadata_key(self, tmp_path):
        """Notebook without 'metadata' key is invalid."""
        nb_path = tmp_path / "bad.ipynb"
        nb_path.write_text(json.dumps({"cells": []}), encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "metadata" in result["error"]

    def test_invalid_json(self, tmp_path):
        """Invalid JSON returns error."""
        nb_path = tmp_path / "bad.ipynb"
        nb_path.write_text("{invalid json", encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is False
        assert "JSON" in result["error"]

    def test_empty_cells(self, tmp_path):
        """Notebook with empty cells list is valid."""
        nb_path = tmp_path / "empty.ipynb"
        nb_path.write_text(json.dumps({"cells": [], "metadata": {}}), encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert result["valid"] is True
        assert result["cell_count"] == 0
        assert result["code_cells"] == 0

    def test_path_included_in_result(self, tmp_path):
        """Result includes the notebook path."""
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text(json.dumps({"cells": [], "metadata": {}}), encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._validate_notebook_syntax(nb_path)
        assert str(nb_path) == result["path"]


# =============================================================================
# BatchNotebookValidator._find_notebook
# =============================================================================


class TestFindNotebook:
    """Tests for BatchNotebookValidator._find_notebook."""

    def _make_validator(self, tmp_path):
        from commands.validate import BatchNotebookValidator
        switcher = MagicMock()
        return BatchNotebookValidator(switcher, notebooks_dir=tmp_path)

    def test_exact_match(self, tmp_path):
        """Finds notebook by exact name."""
        (tmp_path / "sub").mkdir()
        (tmp_path / "sub" / "my_notebook.ipynb").write_text("{}", encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._find_notebook("my_notebook.ipynb")
        assert result is not None
        assert result.name == "my_notebook.ipynb"

    def test_partial_match_fallback(self, tmp_path):
        """Fuzzy match when exact name not found."""
        (tmp_path / "sub").mkdir()
        (tmp_path / "sub" / "GenAI-Image-01-Intro.ipynb").write_text("{}", encoding="utf-8")
        v = self._make_validator(tmp_path)
        result = v._find_notebook("Image-01")
        assert result is not None
        assert "Image-01" in result.name

    def test_not_found(self, tmp_path):
        """Returns None when notebook not found."""
        v = self._make_validator(tmp_path)
        result = v._find_notebook("nonexistent.ipynb")
        assert result is None


# =============================================================================
# BatchNotebookValidator.validate_group
# =============================================================================


class TestValidateGroup:
    """Tests for BatchNotebookValidator.validate_group."""

    def test_unknown_group(self, tmp_path):
        """Unknown group returns error."""
        from commands.validate import BatchNotebookValidator
        switcher = MagicMock()
        v = BatchNotebookValidator(switcher, notebooks_dir=tmp_path)
        result = v.validate_group("nonexistent_group_xyz")
        assert "error" in result

    def test_group_with_notebooks(self, tmp_path):
        """Valid group with real notebooks returns results."""
        from commands.validate import BatchNotebookValidator
        # Use a real group from NOTEBOOK_SERVICE_MAP
        import config
        first_group = next(iter(config.NOTEBOOK_SERVICE_MAP.keys()))
        nb_list = config.NOTEBOOK_SERVICE_MAP[first_group]
        if not nb_list:
            pytest.skip("First group has no notebooks")
        # Create a dummy notebook matching first entry
        nb_name = nb_list[0]
        # Write it in a subdirectory that rglob will find
        (tmp_path / nb_name).write_text(json.dumps({"cells": [], "metadata": {}}), encoding="utf-8")
        switcher = MagicMock()
        v = BatchNotebookValidator(switcher, notebooks_dir=tmp_path)
        result = v.validate_group(first_group)
        assert isinstance(result, dict)


# =============================================================================
# BatchNotebookValidator.print_summary
# =============================================================================


class TestPrintSummary:
    """Tests for BatchNotebookValidator.print_summary."""

    def test_all_valid(self):
        """All valid notebooks returns True."""
        from commands.validate import BatchNotebookValidator
        switcher = MagicMock()
        v = BatchNotebookValidator(switcher)
        v.results = {
            "group1": {
                "nb1.ipynb": {"valid": True},
                "nb2.ipynb": {"valid": True},
            }
        }
        assert v.print_summary() is True

    def test_partial_failure(self):
        """Some invalid notebooks returns False."""
        from commands.validate import BatchNotebookValidator
        switcher = MagicMock()
        v = BatchNotebookValidator(switcher)
        v.results = {
            "group1": {
                "nb1.ipynb": {"valid": True},
                "nb2.ipynb": {"valid": False, "error": "missing"},
            }
        }
        assert v.print_summary() is False

    def test_empty_results(self):
        """Empty results returns True (vacuous)."""
        from commands.validate import BatchNotebookValidator
        switcher = MagicMock()
        v = BatchNotebookValidator(switcher)
        v.results = {}
        assert v.print_summary() is True


# =============================================================================
# ModelSwitcher.switch_to (partial, no network)
# =============================================================================


class TestModelSwitcher:
    """Tests for ModelSwitcher.switch_to — logic-only paths."""

    def test_unknown_model_returns_false(self):
        """Unknown model name returns False."""
        from commands.validate import ModelSwitcher, VRAMManager
        import config
        vram = MagicMock(spec=VRAMManager)
        switcher = ModelSwitcher(vram)
        result = switcher.switch_to("definitely_not_a_model_xyz")
        assert result is False

    def test_already_loaded_returns_true(self):
        """Already-loaded model returns True without VRAM call."""
        from commands.validate import ModelSwitcher, VRAMManager
        vram = MagicMock()
        switcher = ModelSwitcher(vram)
        # Get a real model name from config
        import config
        if not config.MODEL_CONFIGS:
            pytest.skip("No MODEL_CONFIGS available")
        model_name = next(iter(config.MODEL_CONFIGS.keys()))
        switcher.current_model = model_name
        result = switcher.switch_to(model_name)
        assert result is True
        vram.free_vram.assert_not_called()

    def test_switch_calls_free_vram(self):
        """Switching to a different model calls free_vram."""
        from commands.validate import ModelSwitcher, VRAMManager
        vram = MagicMock()
        vram.free_vram.return_value = {}
        vram.get_vram_stats.return_value = {"vram_free": 10 * 1024 * 1024 * 1024}
        switcher = ModelSwitcher(vram)
        import config
        if len(config.MODEL_CONFIGS) < 2:
            pytest.skip("Need >= 2 MODEL_CONFIGS")
        models = list(config.MODEL_CONFIGS.keys())
        switcher.current_model = models[0]
        with patch("commands.validate.time"):  # skip sleep
            result = switcher.switch_to(models[1])
        assert result is True
        vram.free_vram.assert_called_once()


# =============================================================================
# NotebookValidator.find_notebooks
# =============================================================================


class TestNotebookValidatorFindNotebooks:
    """Tests for NotebookValidator.find_notebooks."""

    def test_file_input_ipynb(self, tmp_path):
        """Single .ipynb file returns list with that file."""
        nb = tmp_path / "test.ipynb"
        nb.write_text("{}", encoding="utf-8")
        with patch("commands.notebooks.GenAIAuthManager"):
            from commands.notebooks import NotebookValidator
            v = NotebookValidator(str(nb))
            result = v.find_notebooks()
            assert len(result) == 1
            assert result[0].name == "test.ipynb"

    def test_file_input_non_ipynb(self, tmp_path):
        """Non-.ipynb file returns empty list."""
        txt = tmp_path / "test.txt"
        txt.write_text("hello", encoding="utf-8")
        with patch("commands.notebooks.GenAIAuthManager"):
            from commands.notebooks import NotebookValidator
            v = NotebookValidator(str(txt))
            result = v.find_notebooks()
            assert result == []

    def test_directory_input(self, tmp_path):
        """Directory returns all .ipynb files found."""
        (tmp_path / "a.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "b.ipynb").write_text("{}", encoding="utf-8")
        (tmp_path / "c.txt").write_text("text", encoding="utf-8")
        with patch("commands.notebooks.GenAIAuthManager"):
            from commands.notebooks import NotebookValidator
            v = NotebookValidator(str(tmp_path))
            result = v.find_notebooks()
            names = {p.name for p in result}
            assert names == {"a.ipynb", "b.ipynb"}

    def test_empty_directory(self, tmp_path):
        """Empty directory returns empty list."""
        empty = tmp_path / "empty"
        empty.mkdir()
        with patch("commands.notebooks.GenAIAuthManager"):
            from commands.notebooks import NotebookValidator
            v = NotebookValidator(str(empty))
            result = v.find_notebooks()
            assert result == []


# =============================================================================
# NotebookValidator.save_report
# =============================================================================


class TestNotebookValidatorSaveReport:
    """Tests for NotebookValidator.save_report."""

    def test_report_structure(self, tmp_path, monkeypatch):
        """Report JSON has required keys."""
        monkeypatch.chdir(tmp_path)
        with patch("commands.notebooks.GenAIAuthManager"):
            from commands.notebooks import NotebookValidator
            v = NotebookValidator(str(tmp_path))
            results = [
                {"notebook": "a.ipynb", "status": "success", "duration": 1.0, "error": None, "output_path": "/tmp/a_out.ipynb"},
                {"notebook": "b.ipynb", "status": "failed", "duration": 2.0, "error": "cell error", "output_path": "/tmp/b_out.ipynb"},
            ]
            v.save_report(results)
            report_path = tmp_path / "notebook_validation_report.json"
            assert report_path.exists()
            report = json.loads(report_path.read_text(encoding="utf-8"))
            assert report["total_notebooks"] == 2
            assert report["passed"] == 1
            assert report["failed"] == 1
            assert len(report["results"]) == 2

    def test_empty_report(self, tmp_path, monkeypatch):
        """Empty results produce valid report with 0 counts."""
        monkeypatch.chdir(tmp_path)
        with patch("commands.notebooks.GenAIAuthManager"):
            from commands.notebooks import NotebookValidator
            v = NotebookValidator(str(tmp_path))
            v.save_report([])
            report_path = tmp_path / "notebook_validation_report.json"
            report = json.loads(report_path.read_text(encoding="utf-8"))
            assert report["total_notebooks"] == 0
            assert report["passed"] == 0
            assert report["failed"] == 0
