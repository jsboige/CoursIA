"""Tests for scripts/mcp_buffering_smoke_test.py — MCP buffering smoke test helpers."""

import importlib.util
import json
from pathlib import Path

import pytest

# Load module by file path
_MOD_PATH = (
    Path(__file__).resolve().parent.parent.parent.parent
    / "scripts"
    / "mcp_buffering_smoke_test.py"
)
_spec = importlib.util.spec_from_file_location("mcp_buffering_smoke_test", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

create_stress_notebook = _mod.create_stress_notebook


# --- create_stress_notebook ---


class TestCreateStressNotebook:
    def test_returns_dict(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        assert isinstance(nb, dict)

    def test_nbformat(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        assert nb["nbformat"] == 4
        assert nb["nbformat_minor"] == 5

    def test_kernelspec(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        ks = nb["metadata"]["kernelspec"]
        assert ks["display_name"] == "Python 3"
        assert ks["language"] == "python"
        assert ks["name"] == "python3"

    def test_language_info(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        li = nb["metadata"]["language_info"]
        assert li["name"] == "python"

    def test_file_written(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        create_stress_notebook(nb_path, mode="long_output")
        assert Path(nb_path).exists()
        content = json.loads(Path(nb_path).read_text(encoding="utf-8"))
        assert content["nbformat"] == 4

    def test_long_output_has_four_cells(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        assert len(nb["cells"]) == 4

    def test_reconnect_has_one_cell(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="reconnect")
        assert len(nb["cells"]) == 1

    def test_rapid_calls_has_one_cell(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="rapid_calls")
        assert len(nb["cells"]) == 1

    def test_unknown_mode_empty_cells(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="nonexistent_mode")
        assert len(nb["cells"]) == 0

    def test_all_cells_are_code(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        for cell in nb["cells"]:
            assert cell["cell_type"] == "code"

    def test_cells_have_required_fields(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        for cell in nb["cells"]:
            assert "execution_count" in cell
            assert "metadata" in cell
            assert "outputs" in cell
            assert "source" in cell

    def test_cells_have_null_execution_count(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        for cell in nb["cells"]:
            assert cell["execution_count"] is None

    def test_cells_have_empty_outputs(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        for cell in nb["cells"]:
            assert cell["outputs"] == []

    def test_source_is_list(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        for cell in nb["cells"]:
            assert isinstance(cell["source"], list)

    def test_reconnect_cell_content(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="reconnect")
        source = "".join(nb["cells"][0]["source"])
        assert "test_variable" in source
        assert "preserved_after_restart" in source

    def test_rapid_calls_cell_content(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="rapid_calls")
        source = "".join(nb["cells"][0]["source"])
        assert "import time" in source
        assert "result = sum" in source

    def test_long_output_first_cell_mentions_stress(self, tmp_path):
        nb_path = str(tmp_path / "test.ipynb")
        nb = create_stress_notebook(nb_path, mode="long_output")
        source = "".join(nb["cells"][0]["source"])
        assert "Stress Test" in source


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
