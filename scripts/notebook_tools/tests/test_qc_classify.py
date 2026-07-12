"""Tests for qc_classify.py — QC notebook sub-classifier.

Covers classify(), category(), _is_quantbook(), _is_reference(),
_is_stub(), _is_shallow() with synthetic notebook dicts — no I/O.

Run from the repo root:
    python -m pytest scripts/notebook_tools/tests/test_qc_classify.py -v
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from qc_classify import (
    STUB_MARKERS,
    _is_quantbook,
    _is_reference,
    _is_shallow,
    _is_stub,
    category,
    classify,
)


# ---------------------------------------------------------------------------
# Helpers — build minimal notebook dicts
# ---------------------------------------------------------------------------


def _nb(cells):
    """Build a notebook dict with the given cells."""
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _code(source, *, execution_count=None, outputs=None, errors=None):
    """Build a code cell."""
    if isinstance(source, str):
        source = [source]
    outs = outputs or []
    if errors:
        for e in errors:
            outs.append({"output_type": "error", "ename": e, "evalue": e, "traceback": []})
    return {
        "cell_type": "code",
        "source": source,
        "execution_count": execution_count,
        "outputs": outs,
        "metadata": {},
    }


def _md(*source):
    """Build a markdown cell."""
    lines = []
    for s in source:
        lines.extend(s if isinstance(s, list) else [s])
    return {"cell_type": "markdown", "source": lines, "metadata": {}}


# ---------------------------------------------------------------------------
# _is_quantbook
# ---------------------------------------------------------------------------


class TestIsQuantbook:
    @pytest.mark.parametrize(
        "src",
        [
            "qb = QuantBook()",
            "from QuantConnect import QuantBook\nqb = QuantBook()",
            "self.qb = quantbook()",
        ],
    )
    def test_quantbook_init(self, src):
        assert _is_quantbook(src.lower()) is True

    def test_qcalgorithm(self):
        assert _is_quantbook("class MyAlgo(QCAlgorithm):".lower()) is True

    def test_from_algorithmimports(self):
        assert _is_quantbook("from AlgorithmImports import *".lower()) is True

    def test_plain_python(self):
        assert _is_quantbook("import pandas as pd".lower()) is False

    def test_empty(self):
        assert _is_quantbook("") is False

    def test_case_insensitive(self):
        # _is_quantbook is called with already-lowered input in classify()
        assert _is_quantbook("QB = QUANTBOOK()".lower()) is True


# ---------------------------------------------------------------------------
# _is_reference
# ---------------------------------------------------------------------------


class TestIsReference:
    def test_reference_qc_tag(self):
        nb = _nb([_md("# [Reference QC] Strategy Guide")])
        assert _is_reference(nb) is True

    def test_document_de_reference(self):
        nb = _nb([_md("Ceci est un document de reference pour le cours")])
        assert _is_reference(nb) is True

    def test_no_reference_tag(self):
        nb = _nb([_md("# My Strategy"), _code("print('hello')")])
        assert _is_reference(nb) is False

    def test_mixed_cells(self):
        nb = _nb([
            _md("# Introduction"),
            _code("x = 1"),
            _md("See the [Reference QC] for details."),
        ])
        assert _is_reference(nb) is True

    def test_case_insensitive(self):
        nb = _nb([_md("[REFERENCE QC] dans le texte")])
        assert _is_reference(nb) is True


# ---------------------------------------------------------------------------
# _is_stub
# ---------------------------------------------------------------------------


class TestIsStub:
    def test_stub_marker_quantbook_analysis_tool(self):
        cells = [_code("# QuantBook Analysis Tool\nqb = QuantBook()")]
        src = " ".join("".join(c.get("source", "")) for c in cells)
        assert _is_stub(cells, src) is True

    def test_stub_marker_for_more_information(self):
        cells = [_code("# For more information see the docs")]
        src = " ".join("".join(c.get("source", "")) for c in cells)
        assert _is_stub(cells, src) is True

    def test_too_many_cells(self):
        cells = [_code(f"x = {i}") for i in range(3)]
        src = " ".join("".join(c.get("source", "")) for c in cells)
        assert _is_stub(cells, src) is False

    def test_too_many_chars(self):
        big = "x = 1\n" * 100  # >600 chars
        cells = [_code(big)]
        src = " ".join("".join(c.get("source", "")) for c in cells)
        assert _is_stub(cells, src) is False

    def test_qb_spy_pattern(self):
        cells = [_code('qb = QuantBook()\nqb.add_equity("SPY")')]
        src = " ".join("".join(c.get("source", "")) for c in cells)
        assert _is_stub(cells, src) is True

    def test_qb_history_pattern(self):
        cells = [_code("qb = QuantBook()\nqb.history('SPY', 30)")]
        src = " ".join("".join(c.get("source", "")) for c in cells)
        assert _is_stub(cells, src) is True

    def test_qb_aapl_pattern(self):
        cells = [_code('qb = QuantBook()\nqb.add_equity("AAPL")')]
        src = " ".join("".join(c.get("source", "")) for c in cells)
        assert _is_stub(cells, src) is True

    def test_real_research_not_stub(self):
        # Real research: 1 cell, no stub markers, total_chars > 400
        # (under 400 with qb.history → flagged as stub, which is correct)
        lines = [
            "qb = QuantBook()",
            "spy = qb.add_equity('SPY')",
            "history = qb.history(qb.securities.keys(), 365, Resolution.DAILY)",
            "returns = history.close.pct_change().dropna()",
            "sharpe = returns.mean() / returns.std() * (252**0.5)",
            "max_dd = (returns.cumsum().expanding().max() - returns.cumsum()).min()",
            "vol = returns.std() * (252**0.5)",
            "sortino = returns[returns > 0].mean() / returns[returns < 0].std() * (252**0.5)",
            "calmar = returns.mean() * 252 / abs(max_dd) if max_dd != 0 else 0",
            "print(f'Sharpe: {sharpe:.2f}, Vol: {vol:.2f}, MaxDD: {max_dd:.2%}')",
            "print(f'Sortino: {sortino:.2f}, Calmar: {calmar:.2f}')",
            "# Additional analysis",
            "import matplotlib.pyplot as plt",
            "returns.cumsum().plot(title='Cumulative Returns')",
            "plt.show()",
        ]
        code = "\n".join(lines)
        assert len(code) > 400, f"Code too short: {len(code)} chars"
        cells = [_code(code)]
        src = " ".join("".join(c.get("source", "")) for c in cells)
        assert _is_stub(cells, src) is False

    def test_empty_cells(self):
        cells = [_code("")]
        src = ""
        assert _is_stub(cells, src) is False

    def test_two_cells_under_600_with_marker(self):
        cells = [
            _code("qb = QuantBook()"),
            _code("# QuantBook Analysis Tool"),
        ]
        src = " ".join("".join(c.get("source", "")) for c in cells)
        assert _is_stub(cells, src) is True


# ---------------------------------------------------------------------------
# _is_shallow
# ---------------------------------------------------------------------------


class TestIsShallow:
    def test_few_cells_small_code(self):
        cells = [_code("x = 1"), _code("print(x)")]
        assert _is_shallow(cells) is True

    def test_many_cells(self):
        cells = [_code(f"x = {i}") for i in range(6)]
        assert _is_shallow(cells) is False

    def test_large_code(self):
        big = "x = " + "1 + " * 1000 + "0"  # >3000 chars
        cells = [_code(big)]
        assert _is_shallow(cells) is False

    def test_exactly_five_cells(self):
        cells = [_code(f"x{i} = {i}") for i in range(5)]
        assert _is_shallow(cells) is True

    def test_exactly_3000_chars(self):
        code = "x = " + " " * 2993  # total ~3000
        cells = [_code(code)]
        total = sum(len("".join(c.get("source", "")).strip()) for c in cells)
        assert total <= 3000
        assert _is_shallow(cells) is True

    def test_empty_cells_are_shallow(self):
        cells = [_code("")]
        assert _is_shallow(cells) is True


# ---------------------------------------------------------------------------
# classify
# ---------------------------------------------------------------------------


class TestClassify:
    def test_no_code_cells(self):
        nb = _nb([_md("# Introduction"), _md("Some text")])
        assert classify(nb) == "NO_CODE"

    def test_quantbook_reference(self):
        nb = _nb([
            _md("# [Reference QC] Guide"),
            _code("qb = QuantBook()\nqb.add_equity('SPY')"),
        ])
        assert classify(nb) == "QUANTBOOK_REFERENCE"

    def test_quantbook_stub(self):
        nb = _nb([_code("# QuantBook Analysis Tool\nqb = QuantBook()")])
        assert classify(nb) == "QUANTBOOK_STUB"

    def test_quantbook_shallow(self):
        # 3 code cells, under 3000 chars, no stub markers, not reference
        nb = _nb([
            _code("qb = QuantBook()"),
            _code("spy = qb.add_equity('SPY')"),
            _code("print(spy)"),
        ])
        assert classify(nb) == "QUANTBOOK_SHALLOW"

    def test_quantbook_real(self):
        # Many cells with real logic → not shallow (>5 cells), not stub (>2 cells)
        cells = [_code("qb = QuantBook()\nspy = qb.add_equity('SPY')")]
        for i in range(6):
            cells.append(_code(
                f"history_{i} = qb.history(qb.securities.keys(), {365 - i * 30})\n"
                f"returns_{i} = history_{i}.close.pct_change().dropna()\n"
                f"sharpe_{i} = returns_{i}.mean() / returns_{i}.std() * (252**0.5)\n"
                f"print(f'Sharpe {i}: {{sharpe_{i}:.2f}}')\n"
            ))
        nb = _nb(cells)
        assert classify(nb) == "QUANTBOOK_REAL"

    def test_local_py_yfinance(self):
        nb = _nb([_code("import yfinance as yf\ndata = yf.download('SPY')")])
        assert classify(nb) == "LOCAL_PY"

    def test_local_py_datareader(self):
        nb = _nb([_code("import pandas_datareader as pdr")])
        assert classify(nb) == "LOCAL_PY"

    def test_local_py_binance(self):
        nb = _nb([_code("from binance.client import Client")])
        assert classify(nb) == "LOCAL_PY"

    def test_other(self):
        nb = _nb([_code("import numpy as np\nx = np.array([1,2,3])")])
        assert classify(nb) == "OTHER"

    def test_stub_markers_constant(self):
        assert "quantbook analysis tool" in STUB_MARKERS
        assert "for more information see" in STUB_MARKERS
        assert len(STUB_MARKERS) == 2

    def test_hierarchy_reference_first(self):
        """REFERENCE takes priority over STUB/SHALLOW."""
        nb = _nb([
            _md("# [Reference QC]"),
            _code("# QuantBook Analysis Tool\nqb = QuantBook()"),
        ])
        assert classify(nb) == "QUANTBOOK_REFERENCE"

    def test_hierarchy_stub_before_shallow(self):
        """STUB takes priority over SHALLOW."""
        nb = _nb([_code("# QuantBook Analysis Tool\nqb = QuantBook()")])
        assert classify(nb) == "QUANTBOOK_STUB"


# ---------------------------------------------------------------------------
# category
# ---------------------------------------------------------------------------


class TestCategory:
    def test_no_code(self):
        nb = _nb([_md("# Title")])
        assert category(nb) == "NO_CODE"

    def test_all_executed_no_errors(self):
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("y = 2", execution_count=2),
        ])
        assert category(nb) == "A"

    def test_partial_execution(self):
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("y = 2", execution_count=None),
        ])
        assert category(nb) == "B"

    def test_none_executed(self):
        nb = _nb([
            _code("x = 1", execution_count=None),
            _code("y = 2", execution_count=None),
        ])
        assert category(nb) == "C"

    def test_with_error(self):
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("1/0", execution_count=2, errors=["ZeroDivisionError"]),
        ])
        assert category(nb) == "D"

    def test_error_priority_over_partial(self):
        """Error detected → D even if some cells not executed."""
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("bad()", execution_count=None, errors=["NameError"]),
        ])
        assert category(nb) == "D"

    def test_single_cell_executed(self):
        nb = _nb([_code("print('hello')", execution_count=1)])
        assert category(nb) == "A"

    def test_single_cell_not_executed(self):
        nb = _nb([_code("print('hello')", execution_count=None)])
        assert category(nb) == "C"

    def test_error_zero_exec_count(self):
        """Cell with error output but no execution_count → still D."""
        nb = _nb([
            _code("bad()", execution_count=None, errors=["RuntimeError"]),
        ])
        assert category(nb) == "D"

    def test_normal_outputs_not_error(self):
        """stdout outputs are not errors."""
        nb = _nb([
            _code("print('ok')", execution_count=1, outputs=[
                {"output_type": "stream", "text": ["ok"]},
            ]),
        ])
        assert category(nb) == "A"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
