"""Tests for ResearchNotebookValidator in validate_qc_notebooks.py."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from validate_qc_notebooks import ResearchNotebookValidator, validate_projects


def _make_notebook(cells, kernelspec_name="python3"):
    """Build a minimal notebook dict with the given cells."""
    return {
        "nbformat": 4,
        "nbformat_minor": 5,
        "metadata": {
            "kernelspec": {
                "name": kernelspec_name,
                "display_name": "Python 3",
            },
            "language_info": {"name": "python"},
        },
        "cells": cells,
    }


def _code_cell(source, outputs=None, execution_count=1):
    """Build a code cell with optional outputs."""
    cell = {
        "cell_type": "code",
        "source": source.split("\n"),
        "metadata": {},
        "execution_count": execution_count,
        "outputs": outputs or [],
    }
    return cell


def _markdown_cell(source):
    return {
        "cell_type": "markdown",
        "source": source.split("\n"),
        "metadata": {},
    }


def _output_text(text):
    return [{"output_type": "execute_result", "data": {"text/plain": [text]}, "metadata": {}}]


def _write_nb(path: Path, nb: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb), encoding="utf-8")


class TestExecutionCheck:
    def test_zero_percent_executed_fails(self, tmp_path):
        nb = _make_notebook([
            _code_cell("x = 1"),
            _code_cell("y = 2"),
            _code_cell("z = 3"),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        valid, errors, _ = v.validate_project(tmp_path)
        assert not valid
        assert any("0% code cells executed" in e for e in errors)

    def test_above_30_percent_passes(self, tmp_path):
        nb = _make_notebook([
            _code_cell("x = 1", outputs=_output_text("1")),
            _code_cell("y = 2"),
            _code_cell("z = 3"),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        valid, errors, _ = v.validate_project(tmp_path)
        assert valid
        assert not any("executed" in e for e in errors)

    def test_below_30_percent_fails(self, tmp_path):
        # 1/5 = 20% < 30%
        cells = [_code_cell(f"x = {i}", outputs=(_output_text(str(i)) if i == 0 else [])) for i in range(5)]
        nb = _make_notebook(cells)
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        valid, errors, _ = v.validate_project(tmp_path)
        assert not valid
        assert any("20%" in e for e in errors)

    def test_all_executed_passes(self, tmp_path):
        nb = _make_notebook([
            _code_cell("x = 1", outputs=_output_text("1")),
            _code_cell("y = 2", outputs=_output_text("2")),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        valid, _, _ = v.validate_project(tmp_path)
        assert valid


class TestSectionCheck:
    def test_all_sections_present(self, tmp_path):
        nb = _make_notebook([
            _markdown_cell("# Exploration des donnees"),
            _code_cell("qb = QuantBook()", outputs=_output_text("QB")),
            _markdown_cell("# Iterations et Grid Search"),
            _code_cell("for p in params: ...", outputs=_output_text("done")),
            _markdown_cell("# Conclusion et Calibration"),
            _code_cell("print('done')", outputs=_output_text("done")),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        _, _, warnings = v.validate_project(tmp_path)
        section_warnings = [w for w in warnings if "Section" in w and "not found" in w]
        assert len(section_warnings) == 0

    def test_missing_iterations_section(self, tmp_path):
        nb = _make_notebook([
            _markdown_cell("# Exploration"),
            _code_cell("qb = QuantBook()", outputs=_output_text("QB")),
            _markdown_cell("# Conclusion"),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        _, _, warnings = v.validate_project(tmp_path)
        assert any("Iterations" in w for w in warnings)


class TestQuantBookCheck:
    def test_quantbook_present(self, tmp_path):
        nb = _make_notebook([
            _code_cell("from AlgorithmImports import *\nqb = QuantBook()", outputs=_output_text("QB")),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        _, _, warnings = v.validate_project(tmp_path)
        assert not any("QuantBook" in w for w in warnings)

    def test_quantbook_missing_warns(self, tmp_path):
        nb = _make_notebook([
            _code_cell("x = 1", outputs=_output_text("1")),
            _code_cell("y = 2", outputs=_output_text("2")),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        _, _, warnings = v.validate_project(tmp_path)
        assert any("QuantBook" in w for w in warnings)

    def test_csharp_project_skips_quantbook_check(self, tmp_path):
        (tmp_path / "Main.cs").write_text("// C# algo", encoding="utf-8")
        nb = _make_notebook([
            _code_cell("x = 1", outputs=_output_text("1")),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        _, _, warnings = v.validate_project(tmp_path)
        assert not any("QuantBook" in w for w in warnings)


class TestStubCopyPaste:
    def test_identical_cells_warns(self, tmp_path):
        same_src = "print('hello')"
        nb = _make_notebook([
            _code_cell(same_src, outputs=_output_text("hello")),
            _code_cell(same_src, outputs=_output_text("hello")),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        _, _, warnings = v.validate_project(tmp_path)
        assert any("identique" in w.lower() or "copy-paste" in w.lower() for w in warnings)

    def test_different_cells_no_warning(self, tmp_path):
        nb = _make_notebook([
            _code_cell("x = 1", outputs=_output_text("1")),
            _code_cell("y = 2", outputs=_output_text("2")),
        ])
        nb_path = tmp_path / "research.ipynb"
        _write_nb(nb_path, nb)

        v = ResearchNotebookValidator()
        _, _, warnings = v.validate_project(tmp_path)
        assert not any("copy-paste" in w.lower() for w in warnings)


class TestNoResearchNotebook:
    def test_project_without_notebook_passes(self, tmp_path):
        (tmp_path / "main.py").write_text("pass", encoding="utf-8")
        # No notebook files

        v = ResearchNotebookValidator()
        valid, _, warnings = v.validate_project(tmp_path)
        assert valid
        assert any("no research notebook" in w for w in warnings)

    def test_empty_project_passes(self, tmp_path):
        v = ResearchNotebookValidator()
        valid, errors, _ = v.validate_project(tmp_path)
        assert valid
        assert len(errors) == 0


class TestValidateProjects:
    def test_batch_validation(self, tmp_path):
        proj1 = tmp_path / "GoodProject"
        nb1 = _make_notebook([
            _code_cell("qb = QuantBook()", outputs=_output_text("QB")),
            _code_cell("# Grid search iteration\nprint('done')", outputs=_output_text("done")),
            _markdown_cell("# Exploration des donnees"),
            _markdown_cell("# Conclusion"),
        ])
        _write_nb(proj1 / "research.ipynb", nb1)

        proj2 = tmp_path / "BadProject"
        nb2 = _make_notebook([_code_cell("x = 1")])
        _write_nb(proj2 / "research.ipynb", nb2)

        results = validate_projects(tmp_path)
        assert results["total"] == 2
        assert results["valid"] == 1
        assert results["invalid"] == 1

    def test_skips_dirs_without_notebooks(self, tmp_path):
        proj = tmp_path / "CodeOnly"
        proj.mkdir()
        (proj / "main.py").write_text("pass", encoding="utf-8")

        results = validate_projects(tmp_path)
        assert results["total"] == 0

    def test_skips_underscore_dirs(self, tmp_path):
        hidden = tmp_path / "_archives"
        hidden.mkdir()
        nb = _make_notebook([_code_cell("x = 1")])
        _write_nb(hidden / "research.ipynb", nb)

        results = validate_projects(tmp_path)
        assert results["total"] == 0
