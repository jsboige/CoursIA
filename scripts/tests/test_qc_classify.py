"""Tests for scripts/notebook_tools/qc_classify.py — QC notebook classifier.

Tests focus on pure functions: _is_quantbook, _is_reference, _is_stub,
_is_shallow, classify, category. All use synthetic notebook dicts.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from qc_classify import (
    _is_quantbook,
    _is_reference,
    _is_shallow,
    _is_stub,
    category,
    classify,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _nb(cells: list[dict], **extra) -> dict:
    """Build a minimal notebook dict."""
    nb = {"cells": cells, "metadata": {}}
    nb.update(extra)
    return nb


def _code(source: str, exec_count: int | None = None, outputs: list | None = None) -> dict:
    return {
        "cell_type": "code",
        "source": [source],
        "execution_count": exec_count,
        "outputs": outputs or [],
    }


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


# ---------------------------------------------------------------------------
# _is_quantbook
# ---------------------------------------------------------------------------

class TestIsQuantbook:
    def test_quantbook_constructor(self):
        assert _is_quantbook("qb = quantbook()") is True

    def test_qcalgorithm(self):
        assert _is_quantbook("from qcalgorithm import *") is True

    def test_algorithmimports(self):
        assert _is_quantbook("from algorithmimports import *") is True

    def test_mixed_case_not_matched(self):
        """Function checks lowercase strings; mixed case won't match."""
        assert _is_quantbook("qb = QuantBook()") is False

    def test_regular_python(self):
        assert _is_quantbook("import pandas as pd") is False

    def test_empty_string(self):
        assert _is_quantbook("") is False


# ---------------------------------------------------------------------------
# _is_reference
# ---------------------------------------------------------------------------

class TestIsReference:
    def test_reference_qc_marker(self):
        nb = _nb([_md("# [Reference QC] This is a doc")])
        assert _is_reference(nb) is True

    def test_document_de_reference(self):
        nb = _nb([_md("Ce document de reference...")])
        assert _is_reference(nb) is True

    def test_normal_notebook(self):
        nb = _nb([_md("# My Research Notebook")])
        assert _is_reference(nb) is False

    def test_empty_cells(self):
        nb = _nb([])
        assert _is_reference(nb) is False

    def test_code_only(self):
        nb = _nb([_code("print('hello')")])
        assert _is_reference(nb) is False


# ---------------------------------------------------------------------------
# _is_stub
# ---------------------------------------------------------------------------

class TestIsStub:
    def test_stub_marker_analysis_tool(self):
        cells = [_code("qb = QuantBook()  # QuantBook Analysis Tool")]
        sources = "qb = QuantBook()  # QuantBook Analysis Tool"
        assert _is_stub(cells, sources) is True

    def test_stub_marker_for_more_information(self):
        cells = [_code("# For more information see the docs")]
        sources = "# For more information see the docs"
        assert _is_stub(cells, sources) is True

    def test_too_many_cells(self):
        cells = [_code("a"), _code("b"), _code("c")]
        sources = "a | b | c"
        assert _is_stub(cells, sources) is False

    def test_too_many_chars(self):
        long_src = "x" * 700
        cells = [_code(long_src)]
        assert _is_stub(cells, long_src) is False

    def test_qb_init_with_spy_lowercase(self):
        """_is_stub lowercases internally, but AddEquity != add_equity."""
        src = 'qb = QuantBook()\nqb.AddEquity("SPY")'
        cells = [_code(src)]
        # AddEquity lower = addequity, not add_equity — so spy check fails
        assert _is_stub(cells, src) is False

    def test_qb_init_with_history_only(self):
        """History check works regardless of equity."""
        src = "qb = QuantBook()\nqb.History("
        cells = [_code(src)]
        assert _is_stub(cells, src) is True

    def test_qb_init_with_history(self):
        src = "qb = QuantBook()\nqb.History("
        cells = [_code(src)]
        assert _is_stub(cells, src) is True

    def test_real_notebook_not_stub(self):
        src = "x" * 500  # > 400 chars, no markers
        cells = [_code(src)]
        assert _is_stub(cells, src) is False


# ---------------------------------------------------------------------------
# _is_shallow
# ---------------------------------------------------------------------------

class TestIsShallow:
    def test_few_cells_few_chars(self):
        cells = [_code("a = 1"), _code("b = 2")]
        assert _is_shallow(cells) is True

    def test_too_many_cells(self):
        cells = [_code(f"x{i}") for i in range(6)]
        assert _is_shallow(cells) is False

    def test_too_many_chars(self):
        cells = [_code("x" * 3001)]
        assert _is_shallow(cells) is False

    def test_exact_threshold(self):
        cells = [_code("x" * 3000)]
        assert _is_shallow(cells) is True

    def test_empty_cells(self):
        assert _is_shallow([]) is True


# ---------------------------------------------------------------------------
# classify
# ---------------------------------------------------------------------------

class TestClassify:
    def test_no_code_cells(self):
        nb = _nb([_md("# Title")])
        assert classify(nb) == "NO_CODE"

    def test_quantbook_reference(self):
        nb = _nb([_md("[Reference QC]"), _code("qb = QuantBook()")])
        assert classify(nb) == "QUANTBOOK_REFERENCE"

    def test_quantbook_stub_via_history(self):
        nb = _nb([_code("qb = QuantBook()\nqb.History(")])
        assert classify(nb) == "QUANTBOOK_STUB"

    def test_quantbook_shallow(self):
        src = "qb = QuantBook()\n" + "result = compute_something(data)\n"
        nb = _nb([_code(src)] * 3)  # 3 cells, < 3000 chars
        assert classify(nb) == "QUANTBOOK_SHALLOW"

    def test_quantbook_real(self):
        nb = _nb([_code("from AlgorithmImports import *\n" + "x" * 400)] * 6)
        assert classify(nb) == "QUANTBOOK_REAL"

    def test_local_py_yfinance(self):
        nb = _nb([_code("import yfinance as yf\ndata = yf.download('SPY')")])
        assert classify(nb) == "LOCAL_PY"

    def test_local_py_binance(self):
        nb = _nb([_code("from binance.client import Client")])
        assert classify(nb) == "LOCAL_PY"

    def test_other(self):
        nb = _nb([_code("import numpy as np")])
        assert classify(nb) == "OTHER"


# ---------------------------------------------------------------------------
# category
# ---------------------------------------------------------------------------

class TestCategory:
    def test_a_all_executed(self):
        nb = _nb([_code("a", exec_count=1), _code("b", exec_count=2)])
        assert category(nb) == "A"

    def test_b_partial_exec(self):
        nb = _nb([_code("a", exec_count=1), _code("b")])
        assert category(nb) == "B"

    def test_c_no_exec(self):
        nb = _nb([_code("a"), _code("b")])
        assert category(nb) == "C"

    def test_d_has_error(self):
        nb = _nb([_code("a", exec_count=1, outputs=[{"output_type": "error"}])])
        assert category(nb) == "D"

    def test_no_code(self):
        nb = _nb([_md("# Title")])
        assert category(nb) == "NO_CODE"

    def test_mixed_error_takes_priority(self):
        """Error takes priority over partial execution."""
        nb = _nb([
            _code("a", exec_count=1),
            _code("b", exec_count=2, outputs=[{"output_type": "error"}]),
        ])
        assert category(nb) == "D"

    def test_empty_cells(self):
        nb = _nb([])
        assert category(nb) == "NO_CODE"
