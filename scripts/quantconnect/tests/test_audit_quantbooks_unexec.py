"""Tests for audit_quantbooks_unexec.py — QuantBook unexecuted-cell classifier.

All tests are hermetic: build a temp directory tree of synthetic quantbooks
covering each classification branch + config.json edge cases, then run the
real ``scan_notebook`` / ``scan_projects`` / ``main`` functions against it.

Coverage:
  - ``_is_unexecuted_code`` cell filter (code only, no execution_count, no outputs)
  - ``_has_strip_marker`` markdown Stop&Repair regex (case-insensitive, multiple phrasings)
  - ``scan_notebook`` classification: HEALTHY / STOP_REPAIR_STRIPPED / PREEXISTING_UNEXEC / ERROR
  - ``_config_status`` config.json parsing: ALIVE / DEAD / MISSING / malformed
  - ``scan_projects`` glob + ordering + missing root
  - ``main`` --json / --project / --check exit codes / --md write
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import audit_quantbooks_unexec as aqm  # noqa: E402


# -- helpers --

def _cell(cell_type, source="", execution_count=None, outputs=None):
    """Build a minimal notebook cell dict."""
    return {
        "cell_type": cell_type,
        "source": source,
        "execution_count": execution_count,
        "outputs": outputs if outputs is not None else [],
    }


def _nb(cells, kernel="python3"):
    """Build a minimal notebook dict with kernelspec."""
    return {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel}},
    }


def _write_project(root: Path, name: str, cells, config: dict | None = None,
                   kernel: str = "python3") -> Path:
    """Create ``root/<name>/quantbook.ipynb`` (+ optional config.json)."""
    proj = root / name
    proj.mkdir(parents=True, exist_ok=True)
    nb = _nb(cells, kernel=kernel)
    (proj / "quantbook.ipynb").write_text(
        json.dumps(nb, ensure_ascii=False), encoding="utf-8"
    )
    if config is not None:
        (proj / "config.json").write_text(
            json.dumps(config, ensure_ascii=False), encoding="utf-8"
        )
    return proj


# -- _is_unexecuted_code --

class TestIsUnexecutedCode:
    def test_code_cell_without_exec_count(self):
        c = _cell("code", execution_count=None, outputs=[])
        assert aqm._is_unexecuted_code(c) is True

    def test_code_cell_with_exec_count(self):
        c = _cell("code", execution_count=1, outputs=[])
        assert aqm._is_unexecuted_code(c) is False

    def test_code_cell_with_outputs_but_no_exec_count(self):
        c = _cell("code", execution_count=None, outputs=[{"output_type": "stream"}])
        assert aqm._is_unexecuted_code(c) is False

    def test_markdown_cell_ignored(self):
        c = _cell("markdown", execution_count=None, outputs=[])
        assert aqm._is_unexecuted_code(c) is False

    def test_outputs_none_treated_as_empty(self):
        # Cell where outputs key is missing entirely
        c = {"cell_type": "code", "execution_count": None}
        assert aqm._is_unexecuted_code(c) is True


# -- _has_strip_marker --

class TestHasStripMarker:
    def _md(self, text):
        return _cell("markdown", source=text)

    def test_no_marker(self):
        nb = _nb([self._md("hello world")])
        assert aqm._has_strip_marker(nb) is False

    def test_sortie_strippee(self):
        nb = _nb([self._md("> Sortie strippee (FABRICATED). Re-execution required.")])
        assert aqm._has_strip_marker(nb) is True

    def test_fabricated_caps(self):
        nb = _nb([self._md("> **FABRICATED** row marker.")])
        assert aqm._has_strip_marker(nb) is True

    def test_blank_png_hyphenated(self):
        nb = _nb([self._md("Cell emitted a blank-PNG (1x1, 70B).")])
        assert aqm._has_strip_marker(nb) is True

    def test_case_insensitive(self):
        nb = _nb([self._md("> sortie Strippée")])
        assert aqm._has_strip_marker(nb) is True

    def test_source_as_list(self):
        nb = _nb([{"cell_type": "markdown", "source": ["> Sortie ", "strippee."]}])
        assert aqm._has_strip_marker(nb) is True

    def test_marker_in_code_cell_ignored(self):
        # Markers live in markdown only; we don't double-count code cells.
        nb = _nb([_cell("code", source="sortie strippee", execution_count=None)])
        assert aqm._has_strip_marker(nb) is False


# -- _config_status --

class TestConfigStatus:
    def test_no_config(self, tmp_path):
        r = aqm._config_status(tmp_path)
        assert r["status"] == "MISSING"
        assert r["has_config"] is False

    def test_config_alive(self, tmp_path):
        (tmp_path / "config.json").write_text(json.dumps({"cloud-id": 12345}))
        r = aqm._config_status(tmp_path)
        assert r["status"] == "ALIVE"
        assert r["cloud_id"] == 12345

    def test_config_dead_zero(self, tmp_path):
        (tmp_path / "config.json").write_text(json.dumps({"cloud-id": 0}))
        r = aqm._config_status(tmp_path)
        assert r["status"] == "DEAD"
        assert r["cloud_id"] == 0

    def test_config_dead_negative(self, tmp_path):
        (tmp_path / "config.json").write_text(json.dumps({"cloud-id": -1}))
        r = aqm._config_status(tmp_path)
        assert r["status"] == "DEAD"

    def test_config_missing_cloud_id(self, tmp_path):
        (tmp_path / "config.json").write_text(json.dumps({"language": "Py"}))
        r = aqm._config_status(tmp_path)
        assert r["status"] == "MISSING"
        assert r["cloud_id"] is None

    def test_config_malformed_json(self, tmp_path):
        (tmp_path / "config.json").write_text("{not json")
        r = aqm._config_status(tmp_path)
        assert r["status"] == "MISSING"
        assert "error" in r


# -- scan_notebook classification --

class TestScanNotebook:
    def test_healthy_all_executed(self, tmp_path):
        nb_cells = [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "def foo(): pass", execution_count=2, outputs=[]),
        ]
        proj = _write_project(tmp_path, "P", nb_cells)
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["classification"] == "HEALTHY"
        assert r["code_total"] == 2
        assert r["code_unexecuted"] == 0
        assert r["code_executed"] == 2

    def test_strip_marker_with_unexec(self, tmp_path):
        nb_cells = [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "y = 2", execution_count=None, outputs=[]),
            _cell("markdown", "> Sortie strippee (FABRICATED). Re-execution required."),
        ]
        proj = _write_project(tmp_path, "P", nb_cells)
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["classification"] == "STOP_REPAIR_STRIPPED"
        assert r["code_unexecuted"] == 1
        assert r["strip_marker"] is True

    def test_preexisting_unexec_no_marker(self, tmp_path):
        nb_cells = [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "y = 2", execution_count=None, outputs=[]),
            _cell("code", "z = 3", execution_count=None, outputs=[]),
        ]
        proj = _write_project(tmp_path, "P", nb_cells)
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["classification"] == "PREEXISTING_UNEXEC"
        assert r["code_unexecuted"] == 2
        assert r["unexecuted_indexes"] == [1, 2]
        assert r["strip_marker"] is False

    def test_error_unreadable(self, tmp_path):
        proj = tmp_path / "BadProj"
        proj.mkdir()
        (proj / "quantbook.ipynb").write_text("{not json", encoding="utf-8")
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["classification"] == "ERROR"
        assert "error" in r

    def test_kernel_passed_through(self, tmp_path):
        proj = _write_project(tmp_path, "P", [_cell("code")], kernel="csharp")
        r = aqm.scan_notebook(proj / "quantbook.ipynb")
        assert r["kernel"] == "csharp"


# -- scan_projects glob --

class TestScanProjects:
    def test_scans_only_quantbook(self, tmp_path):
        _write_project(tmp_path, "A", [_cell("code")])
        _write_project(tmp_path, "B", [_cell("code", execution_count=None)])
        # A non-quantbook file must be ignored
        (tmp_path / "C").mkdir()
        (tmp_path / "C" / "research.ipynb").write_text("{}", encoding="utf-8")
        # A project with no quantbook must be ignored
        (tmp_path / "D").mkdir()
        (tmp_path / "D" / "main.py").write_text("# code", encoding="utf-8")

        results = aqm.scan_projects(tmp_path)
        names = sorted(Path(r["path"]).parent.name for r in results)
        assert names == ["A", "B"]

    def test_ordered(self, tmp_path):
        for n in ["Z", "A", "M"]:
            _write_project(tmp_path, n, [_cell("code")])
        results = aqm.scan_projects(tmp_path)
        names = [Path(r["path"]).parent.name for r in results]
        assert names == ["A", "M", "Z"]

    def test_missing_root_raises(self, tmp_path):
        with pytest.raises(FileNotFoundError):
            aqm.scan_projects(tmp_path / "nope")


# -- main --

class TestMain:
    def test_json_output_to_stdout(self, tmp_path, capsys):
        # Healthy = all code cells executed; pass an exec_count + outputs.
        _write_project(tmp_path, "P", [
            _cell("code", "x = 1", execution_count=1,
                  outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
        ])
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".", "--json"])
        assert rc == 0
        out = json.loads(capsys.readouterr().out)
        assert out["scanned"] == 1
        assert out["by_class"]["HEALTHY"] == 1
        assert out["results"][0]["classification"] == "HEALTHY"

    def test_project_filter(self, tmp_path, capsys):
        _write_project(tmp_path, "Good", [_cell("code", execution_count=1)])
        _write_project(tmp_path, "Bad", [_cell("code", execution_count=None)])
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".",
                       "--project", "Bad", "--json"])
        assert rc == 0
        out = json.loads(capsys.readouterr().out)
        assert out["scanned"] == 1
        assert out["results"][0]["classification"] == "PREEXISTING_UNEXEC"

    def test_project_not_found_exits_2(self, tmp_path):
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".",
                       "--project", "NOPE"])
        assert rc == 2

    def test_quant_root_missing_exits_2(self, tmp_path):
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", "nope"])
        assert rc == 2

    def test_check_exits_1_when_preexisting(self, tmp_path):
        _write_project(tmp_path, "Bad", [_cell("code", execution_count=None)])
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".", "--check"])
        assert rc == 1

    def test_check_exits_0_when_clean(self, tmp_path):
        _write_project(tmp_path, "Good", [_cell("code", execution_count=1)])
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".", "--check"])
        assert rc == 0

    def test_md_write(self, tmp_path):
        _write_project(tmp_path, "P", [_cell("code", execution_count=1)])
        out_path = tmp_path / "report.md"
        rc = aqm.main(["--root", str(tmp_path), "--quant-root", ".",
                       "--md", str(out_path)])
        assert rc == 0
        assert out_path.exists()
        content = out_path.read_text(encoding="utf-8")
        assert "QuantBooks scanned" in content
        assert "HEALTHY" in content


# -- integration: realistic multi-project scenario matching #6891 --

class TestIntegration6891:
    """Simulate the bug-class matrix observed in #6891 follow-up."""

    def test_matrix(self, tmp_path):
        # HEALTHY: all exec, no marker
        _write_project(tmp_path, "Healthy", [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
        ])
        # STOP_REPAIR_STRIPPED: has unexec + has marker (body #6891 scope)
        _write_project(tmp_path, "Stripped", [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "y = 2", execution_count=None, outputs=[]),
            _cell("markdown", "> **Sortie strippee** (FABRICATED). Re-execution required."),
        ], config={"cloud-id": 12345})
        # PREEXISTING_UNEXEC: has unexec, no marker
        _write_project(tmp_path, "Preexisting", [
            _cell("code", "x = 1", execution_count=1, outputs=[{"output_type": "stream", "name": "stdout", "text": "ok"}]),
            _cell("code", "y = 2", execution_count=None, outputs=[]),
        ], config={"cloud-id": 0})
        # DEAD cloud-id case (FamaFrench-like)
        _write_project(tmp_path, "DeadCloud", [
            _cell("code", "y = 2", execution_count=None, outputs=[]),
        ], config={"cloud-id": 0})

        results = aqm.scan_projects(tmp_path)
        by_name = {Path(r["path"]).parent.name: r for r in results}

        assert by_name["Healthy"]["classification"] == "HEALTHY"
        assert by_name["Stripped"]["classification"] == "STOP_REPAIR_STRIPPED"
        assert by_name["Preexisting"]["classification"] == "PREEXISTING_UNEXEC"
        assert by_name["DeadCloud"]["classification"] == "PREEXISTING_UNEXEC"
        assert by_name["Stripped"]["config"]["status"] == "ALIVE"
        assert by_name["DeadCloud"]["config"]["status"] == "DEAD"
        assert by_name["Preexisting"]["config"]["status"] == "DEAD"
