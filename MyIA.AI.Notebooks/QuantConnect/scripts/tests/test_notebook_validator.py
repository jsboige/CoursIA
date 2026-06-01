"""Tests for NotebookValidator from validate_qc_notebooks.py.

ResearchNotebookValidator already covered by test_validate_qc_research.py.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from validate_qc_notebooks import NotebookValidator


def _nb(cells=None, metadata=None, nbformat=4):
    """Build a notebook dict skeleton."""
    return {
        "cells": cells or [],
        "metadata": metadata or {},
        "nbformat": nbformat,
        "nbformat_minor": 5,
    }


def _md(text):
    return {"cell_type": "markdown", "source": text.split("\n") if isinstance(text, str) else text}


def _code(source, outputs=None, execution_count=None):
    return {
        "cell_type": "code",
        "source": source.split("\n") if isinstance(source, str) else source,
        "outputs": outputs or [],
        "execution_count": execution_count,
    }


# --- _detect_language ---
#
# Quirk documented: `'py' in filename.lower()` matches the literal 'py' inside
# the '.ipynb' extension itself, so any *.ipynb name returns 'python' unless
# the upper-case 'CS' branch wins first (which only happens when the .ipynb
# extension is absent — e.g. "QC-CS-01-Algo"). The csharp branch is
# therefore unreachable for real *.ipynb filenames. These tests pin the
# current behaviour; a future fix would tighten the regex.

class TestDetectLanguage:
    def setup_method(self):
        self.v = NotebookValidator()

    def test_python_upper_py(self):
        assert self.v._detect_language("QC-Py-01-Setup.ipynb") == "python"

    def test_python_lower_py(self):
        assert self.v._detect_language("foo-py-bar.ipynb") == "python"

    def test_ipynb_extension_collides_with_py_substring(self):
        # Documents the known limitation: .ipynb itself contains 'py'.
        assert self.v._detect_language("QC-CS-01-Setup.ipynb") == "python"
        assert self.v._detect_language("random.ipynb") == "python"

    def test_csharp_without_ipynb_extension(self):
        # Without .ipynb extension, the CS branch can fire.
        assert self.v._detect_language("QC-CS-01-Algo") == "csharp"

    def test_unknown_returns_none(self):
        # Filename with no .ipynb AND no Py/CS/csharp markers.
        assert self.v._detect_language("notebook.txt") is None


# --- _validate_metadata ---

class TestValidateMetadata:
    def setup_method(self):
        self.v = NotebookValidator()

    def test_python_kernel_ok_no_warning(self):
        nb = _nb(metadata={
            "kernelspec": {"name": "python3"},
            "language_info": {"name": "python"},
        })
        self.v._validate_metadata(nb, "python", fix=False)
        assert not any("Kernel inattendu" in w for w in self.v.warnings)

    def test_python_kernel_unexpected_warning(self):
        nb = _nb(metadata={
            "kernelspec": {"name": "bash"},
            "language_info": {"name": "python"},
        })
        self.v._validate_metadata(nb, "python", fix=False)
        assert any("Kernel inattendu" in w for w in self.v.warnings)

    def test_python_kernel_fix_applied(self):
        nb = _nb(metadata={
            "kernelspec": {"name": "wrong"},
            "language_info": {"name": "python"},
        })
        self.v._validate_metadata(nb, "python", fix=True)
        assert nb["metadata"]["kernelspec"]["name"] == "python3"
        assert any("Kernel" in f for f in self.v.fixes_applied)

    def test_csharp_kernel_fix(self):
        nb = _nb(metadata={
            "kernelspec": {"name": "wrong"},
            "language_info": {"name": "C#"},
        })
        self.v._validate_metadata(nb, "csharp", fix=True)
        assert nb["metadata"]["kernelspec"]["name"] == ".net-csharp"

    def test_missing_language_info_warning(self):
        nb = _nb(metadata={"kernelspec": {"name": "python3"}})
        self.v._validate_metadata(nb, "python", fix=False)
        assert any("language_info" in w for w in self.v.warnings)

    def test_missing_language_info_fix_python(self):
        nb = _nb(metadata={"kernelspec": {"name": "python3"}})
        self.v._validate_metadata(nb, "python", fix=True)
        assert nb["metadata"]["language_info"]["name"] == "python"

    def test_missing_language_info_fix_csharp(self):
        nb = _nb(metadata={"kernelspec": {"name": ".net-csharp"}})
        self.v._validate_metadata(nb, "csharp", fix=True)
        assert nb["metadata"]["language_info"]["name"] == "C#"


# --- _validate_cells ---

class TestValidateCells:
    def setup_method(self):
        self.v = NotebookValidator()

    def test_empty_notebook_errors(self):
        self.v._validate_cells(_nb(), "python", fix=False)
        assert any("vide" in e for e in self.v.errors)

    def test_first_cell_not_markdown_warns(self):
        nb = _nb(cells=[_code("from AlgorithmImports import *\nimport pandas\nimport numpy")])
        self.v._validate_cells(nb, "python", fix=False)
        assert any("markdown" in w.lower() for w in self.v.warnings)

    def test_first_markdown_no_title_warns(self):
        nb = _nb(cells=[_md("no title"), _code("from AlgorithmImports import *\nimport pandas\nimport numpy")])
        self.v._validate_cells(nb, "python", fix=False)
        assert any("titre" in w.lower() for w in self.v.warnings)

    def test_markdown_only_warns_not_errors(self):
        nb = _nb(cells=[_md("# Title")])
        self.v._validate_cells(nb, "python", fix=False)
        assert any("markdown-only" in w for w in self.v.warnings)
        assert not self.v.errors

    def test_missing_imports_python_warns(self):
        nb = _nb(cells=[_md("# T"), _code("x = 1")])
        self.v._validate_cells(nb, "python", fix=False)
        assert any("Imports manquants" in w for w in self.v.warnings)

    def test_missing_imports_csharp_warns(self):
        nb = _nb(cells=[_md("# T"), _code("var x = 1;")])
        self.v._validate_cells(nb, "csharp", fix=False)
        assert any("Imports manquants" in w for w in self.v.warnings)

    def test_imports_present_no_warning(self):
        src = "from AlgorithmImports import *\nimport pandas\nimport numpy"
        nb = _nb(cells=[_md("# T"), _code(src)])
        self.v._validate_cells(nb, "python", fix=False)
        assert not any("Imports manquants" in w for w in self.v.warnings)

    def test_executed_cells_warning(self):
        src = "from AlgorithmImports import *\nimport pandas\nimport numpy"
        nb = _nb(cells=[
            _md("# T"),
            _code(src, outputs=[{"output_type": "stream"}], execution_count=1),
        ])
        self.v._validate_cells(nb, "python", fix=False)
        assert any("outputs" in w for w in self.v.warnings)


# --- _validate_no_theatrical_outputs ---

class TestTheatricalOutputs:
    def setup_method(self):
        self.v = NotebookValidator()

    def test_algorithme_charge_detected(self):
        nb = _nb(cells=[_code('print("Algorithme charge: 1234 chars")')])
        self.v._validate_no_theatrical_outputs(nb)
        assert any("théâtral" in e for e in self.v.errors)

    def test_lignes_de_code_detected(self):
        nb = _nb(cells=[_code('print("Lignes de code: 42")')])
        self.v._validate_no_theatrical_outputs(nb)
        assert self.v.errors

    def test_workflow_deploiement_detected(self):
        nb = _nb(cells=[_code('print("Workflow de deploiement MCP")')])
        self.v._validate_no_theatrical_outputs(nb)
        assert self.v.errors

    def test_placeholder_results_detected(self):
        nb = _nb(cells=[_code('print("Placeholder pour les resultats")')])
        self.v._validate_no_theatrical_outputs(nb)
        assert self.v.errors

    def test_qc_cloud_fake_sync_detected(self):
        nb = _nb(cells=[_code('"Resultats sync depuis QC Cloud projet 9999"')])
        self.v._validate_no_theatrical_outputs(nb)
        assert self.v.errors

    def test_clean_code_no_error(self):
        nb = _nb(cells=[_code('history = qb.History(symbol, 100, Resolution.Daily)')])
        self.v._validate_no_theatrical_outputs(nb)
        assert not self.v.errors

    def test_markdown_cell_skipped(self):
        nb = _nb(cells=[_md("Algorithme charge: this is markdown text")])
        self.v._validate_no_theatrical_outputs(nb)
        assert not self.v.errors


# --- _validate_structure ---

class TestValidateStructure:
    def setup_method(self):
        self.v = NotebookValidator()

    def test_old_nbformat_errors(self):
        nb = _nb(nbformat=3)
        self.v._validate_structure(nb, "python")
        assert any("nbformat" in e for e in self.v.errors)

    def test_current_nbformat_ok(self):
        nb = _nb(nbformat=4)
        self.v._validate_structure(nb, "python")
        assert not any("nbformat" in e for e in self.v.errors)


# --- _validate_naming ---

class TestValidateNaming:
    def setup_method(self):
        self.v = NotebookValidator()

    def test_valid_python_name(self):
        self.v._validate_naming(Path("QC-Py-01-Setup.ipynb"), "python")
        assert not any("non conforme" in w for w in self.v.warnings)

    def test_invalid_python_name(self):
        self.v._validate_naming(Path("random.ipynb"), "python")
        assert any("non conforme" in w for w in self.v.warnings)

    def test_valid_csharp_name(self):
        self.v._validate_naming(Path("QC-CS-05-Algo.ipynb"), "csharp")
        assert not any("non conforme" in w for w in self.v.warnings)

    def test_invalid_csharp_name(self):
        self.v._validate_naming(Path("foo.ipynb"), "csharp")
        assert any("non conforme" in w for w in self.v.warnings)


# --- validate_notebook integration ---

class TestValidateNotebook:
    def test_missing_file(self, tmp_path):
        v = NotebookValidator()
        ok, errs, _ = v.validate_notebook(tmp_path / "does-not-exist.ipynb")
        assert ok is False
        assert any("non trouvé" in e for e in errs)

    def test_invalid_json(self, tmp_path):
        nb_path = tmp_path / "QC-Py-01-Bad.ipynb"
        nb_path.write_text("not json {", encoding="utf-8")
        v = NotebookValidator()
        ok, errs, _ = v.validate_notebook(nb_path)
        assert ok is False
        assert any("JSON" in e for e in errs)

    def test_unknown_language_from_name(self, tmp_path):
        # Use a non-.ipynb extension so _detect_language returns None
        # (see TestDetectLanguage notes — .ipynb itself contains 'py').
        nb_path = tmp_path / "notebook.json"
        nb_path.write_text(json.dumps(_nb(cells=[_md("# T")])), encoding="utf-8")
        v = NotebookValidator()
        ok, errs, _ = v.validate_notebook(nb_path)
        assert ok is False
        assert any("langage" in e for e in errs)

    def test_minimal_valid_notebook(self, tmp_path):
        nb_path = tmp_path / "QC-Py-01-Setup.ipynb"
        nb = _nb(
            cells=[
                _md("# Setup"),
                _code("from AlgorithmImports import *\nimport pandas\nimport numpy"),
            ],
            metadata={"kernelspec": {"name": "python3"}, "language_info": {"name": "python"}},
        )
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        v = NotebookValidator()
        ok, errs, _ = v.validate_notebook(nb_path)
        assert ok is True, f"errors: {errs}"

    def test_theatrical_pattern_fails_validation(self, tmp_path):
        nb_path = tmp_path / "QC-Py-01-Theatre.ipynb"
        nb = _nb(
            cells=[_md("# T"), _code('print("Algorithme charge: 999")')],
            metadata={"kernelspec": {"name": "python3"}, "language_info": {"name": "python"}},
        )
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        v = NotebookValidator()
        ok, errs, _ = v.validate_notebook(nb_path)
        assert ok is False
        assert any("théâtral" in e for e in errs)

    def test_fix_writes_back(self, tmp_path):
        nb_path = tmp_path / "QC-Py-01-Fix.ipynb"
        nb = _nb(
            cells=[
                _md("# T"),
                _code("from AlgorithmImports import *\nimport pandas\nimport numpy"),
            ],
            metadata={"kernelspec": {"name": "wrong"}},
        )
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        v = NotebookValidator()
        v.validate_notebook(nb_path, fix=True)
        rewritten = json.loads(nb_path.read_text(encoding="utf-8"))
        assert rewritten["metadata"]["kernelspec"]["name"] == "python3"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
