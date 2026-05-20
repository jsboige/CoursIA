"""Tests for generate_catalog.py — catalog generation heuristics.

Covers: detect_kernel, extract_title, detect_requirements, check_errors,
determine_status, count_todos, has_markdown_intro_conclusion,
classify_maturity.
"""

import json
import sys
import tempfile
from pathlib import Path

import pytest

# Add parent dir to path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from generate_catalog import (
    NOTEBOOKS_DIR,
    check_errors,
    classify_maturity,
    count_todos,
    detect_kernel,
    detect_requirements,
    determine_status,
    extract_title,
    has_markdown_intro_conclusion,
)


def _nb(cells, metadata=None):
    """Build a minimal notebook dict."""
    nb = {"cells": cells, "metadata": {}}
    if metadata:
        nb["metadata"] = metadata
    return nb


def _md(source, cell_type="markdown"):
    """Build a markdown/code cell with newline-terminated source."""
    if isinstance(source, str):
        source = [source + "\n"]
    return {"cell_type": cell_type, "source": source, "outputs": [],
            "execution_count": 1}


def _code(source, outputs=None, execution_count=1):
    """Build a code cell."""
    if isinstance(source, str):
        source = [source + "\n"]
    return {
        "cell_type": "code",
        "source": source,
        "outputs": outputs or [],
        "execution_count": execution_count,
    }


def _error_output(ename="RuntimeError", evalue="test error"):
    """Build an error output dict."""
    return {
        "output_type": "error",
        "ename": ename,
        "evalue": evalue,
        "traceback": [],
    }


def _stream_output(text="hello"):
    """Build a stdout stream output."""
    return {"output_type": "stream", "name": "stdout", "text": [text]}


# --- detect_kernel ---

class TestDetectKernel:
    def test_display_name(self):
        nb = _nb([], metadata={"kernelspec": {"display_name": "Python 3", "name": "python3"}})
        assert detect_kernel(nb) == "Python 3"

    def test_fallback_to_name(self):
        nb = _nb([], metadata={"kernelspec": {"name": "python3"}})
        assert detect_kernel(nb) == "python3"

    def test_no_kernelspec(self):
        nb = _nb([], metadata={})
        assert detect_kernel(nb) == "unknown"

    def test_empty_kernelspec(self):
        nb = _nb([], metadata={"kernelspec": {}})
        assert detect_kernel(nb) == "unknown"


# --- extract_title ---

class TestExtractTitle:
    def test_h1_title(self):
        nb = _nb([_md("# Mon Titre")])
        assert extract_title(nb) == "Mon Titre"

    def test_h2_title(self):
        nb = _nb([_md("## Section Title")])
        assert extract_title(nb) == "Section Title"

    def test_skips_non_heading(self):
        nb = _nb([_md("Some text\n## Real Title")])
        assert extract_title(nb) == "Real Title"

    def test_no_markdown_cells(self):
        nb = _nb([_code("x = 1")])
        assert extract_title(nb) == ""

    def test_empty_cells(self):
        nb = _nb([])
        assert extract_title(nb) == ""


# --- detect_requirements ---

class TestDetectRequirements:
    def test_no_requirements(self):
        nb = _nb([_code("x = 1")])
        reqs = detect_requirements(nb)
        assert all(not v for v in reqs.values())

    def test_api_requirement(self):
        nb = _nb([_code("import openai")])
        reqs = detect_requirements(nb)
        assert reqs["requires_api"] is True

    def test_gpu_requirement(self):
        nb = _nb([_code("device = torch.device('cuda')")])
        reqs = detect_requirements(nb)
        assert reqs["requires_gpu"] is True

    def test_cloud_requirement(self):
        nb = _nb([_code("qb = QuantBook()")])
        reqs = detect_requirements(nb)
        assert reqs["requires_cloud"] is True

    def test_wsl_requirement(self):
        nb = _nb([_code("import wsl_helper")])
        reqs = detect_requirements(nb)
        assert reqs["requires_wsl"] is True

    def test_multiple_requirements(self):
        nb = _nb([_code("openai.api_key = x\ntorch.cuda.is_available()")])
        reqs = detect_requirements(nb)
        assert reqs["requires_api"] is True
        assert reqs["requires_gpu"] is True

    def test_ignores_markdown(self):
        nb = _nb([_md("# openai is cool")])
        reqs = detect_requirements(nb)
        assert reqs["requires_api"] is False


# --- check_errors ---

class TestCheckErrors:
    def test_no_errors(self):
        assert check_errors([_stream_output()]) == []

    def test_single_error(self):
        assert check_errors([_error_output("ImportError")]) == ["ImportError"]

    def test_multiple_errors(self):
        errors = check_errors([_error_output("Err1"), _stream_output(), _error_output("Err2")])
        assert errors == ["Err1", "Err2"]

    def test_empty_outputs(self):
        assert check_errors([]) == []


# --- determine_status ---

class TestDetermineStatus:
    def _make_path(self, name="Test.ipynb"):
        return NOTEBOOKS_DIR / name

    def test_research_path(self):
        nb = _nb([_code("x=1", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=False) == "RESEARCH"

    def test_ready_with_outputs(self):
        nb = _nb([_code("x=1", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "READY"

    def test_broken_with_errors(self):
        nb = _nb([_code("x=1", [_error_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "BROKEN"

    def test_broken_no_outputs_no_deps(self):
        nb = _nb([_code("x=1")])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "BROKEN"

    def test_demo_no_outputs_with_api(self):
        nb = _nb([_code("openai.api_key = 'x'")])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": True, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "DEMO"

    def test_demo_with_outputs_and_gpu(self):
        nb = _nb([_code("torch.cuda()", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        reqs = {"requires_api": False, "requires_gpu": True, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "DEMO"

    def test_ready_empty_code_cells(self):
        nb = _nb([_md("# Title")])
        code_cells = []
        reqs = {"requires_api": False, "requires_gpu": False, "requires_cloud": False, "requires_wsl": False}
        assert determine_status(self._make_path(), nb, code_cells, reqs, pedagogical=True) == "READY"


# --- count_todos ---

class TestCountTodos:
    def test_no_todos(self):
        nb = _nb([_code("x = 1")])
        assert count_todos(nb) == 0

    def test_single_todo(self):
        nb = _nb([_code("x = None  # TODO student")])
        assert count_todos(nb) == 1

    def test_multiple_todos(self):
        nb = _nb([
            _code("x = None  # TODO step 1"),
            _code("y = None  # TODO step 2"),
        ])
        assert count_todos(nb) == 2

    def test_case_insensitive(self):
        nb = _nb([_code("# todo: implement")])
        assert count_todos(nb) == 1

    def test_ignores_markdown(self):
        nb = _nb([_md("# TODO list")])
        assert count_todos(nb) == 0


# --- has_markdown_intro_conclusion ---

class TestHasMarkdownIntroConclusion:
    def test_both_present(self):
        cells = [
            _md("# Introduction et objectifs"),
            _code("x = 1"),
            _md("## Conclusion et résumé"),
        ]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is True
        assert conclusion is True

    def test_no_intro(self):
        cells = [
            _md("# Something else"),
            _code("x = 1"),
            _md("## Conclusion"),
        ]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is False
        assert conclusion is True

    def test_no_conclusion(self):
        cells = [
            _md("# Introduction"),
            _code("x = 1"),
            _md("## More content"),
        ]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is True
        assert conclusion is False

    def test_no_markdown(self):
        cells = [_code("x = 1")]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is False
        assert conclusion is False

    def test_french_keywords(self):
        cells = [
            _md("# Objectif du TP"),
            _md("## Pour aller plus loin"),
        ]
        intro, conclusion = has_markdown_intro_conclusion(cells)
        assert intro is True
        assert conclusion is True


# --- classify_maturity ---

class TestClassifyMaturity:
    def _full_nb(self, cells):
        return _nb(cells, metadata={"kernelspec": {"display_name": "Python 3", "name": "python3"}})

    def test_production(self):
        nb = self._full_nb([
            _md("# Introduction"),
            _code("x = 1", [_stream_output()]),
            _md("## Conclusion"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "PRODUCTION"

    def test_beta_missing_conclusion(self):
        nb = self._full_nb([
            _md("# Introduction"),
            _code("x = 1", [_stream_output()]),
            _md("## More"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "BETA"

    def test_alpha_partial_outputs(self):
        nb = self._full_nb([
            _md("# Title"),
            _code("x = 1", [_stream_output()]),
            _code("y = 2"),  # no outputs
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "ALPHA"

    def test_alpha_many_todos(self):
        code_cells = [_code(f"x{i} = None  # TODO {i}", [_stream_output()]) for i in range(7)]
        nb = self._full_nb([_md("# Title")] + code_cells)
        assert classify_maturity(nb, code_cells, "Python 3") == "ALPHA"

    def test_draft_no_outputs(self):
        nb = self._full_nb([
            _md("# Title"),
            _code("x = 1"),
        ])
        code_cells = [c for c in nb["cells"] if c["cell_type"] == "code"]
        assert classify_maturity(nb, code_cells, "Python 3") == "DRAFT"

    def test_draft_no_markdown(self):
        nb = self._full_nb([_code("x = 1", [_stream_output()])])
        code_cells = [nb["cells"][0]]
        assert classify_maturity(nb, code_cells, "Python 3") == "DRAFT"

    def test_draft_too_many_todos(self):
        code_cells = [_code(f"x{i} = None  # TODO {i}", [_stream_output()]) for i in range(12)]
        nb = self._full_nb([_md("# Title")] + code_cells)
        assert classify_maturity(nb, code_cells, "Python 3") == "DRAFT"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
