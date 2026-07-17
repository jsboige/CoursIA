"""Tests for scripts/notebook_tools/detect_svg_empty_display.py — empty-display
(chart `display()`-ed but output empty = white figure on GitHub) detector.

Tests focus on pure functions: detect_cell, detect_cell_detail, scan_notebook,
and the main() exit codes. Uses synthetic notebook dicts and tmp_path for
filesystem isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_svg_empty_display import (  # noqa: E402
    detect_cell,
    detect_cell_detail,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code_cell(source: str, exec_count=1, outputs=None) -> dict:
    """A code cell with given source, execution_count, and outputs (default empty)."""
    return {
        "cell_type": "code",
        "execution_count": exec_count,
        "source": [source] if isinstance(source, str) else source,
        "outputs": outputs if outputs is not None else [],
    }


def _svg_output(svg: str = '<svg viewBox="0 0 10 10"><rect width="10" height="10"/></svg>') -> dict:
    """A display_data output carrying an inline SVG (the happy-path chart output)."""
    return {"data": {"text/html": svg}, "metadata": {}, "output_type": "display_data"}


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": ".net-csharp"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# detect_cell — the zero-FP 3-condition signature
# ---------------------------------------------------------------------------

class TestDetectCell:
    def test_flags_display_svgcharthelper_empty_output(self):
        # The #6963 signature: display(SvgChartHelper.Bar(...)) + ran + empty output.
        cell = _code_cell('display(SvgChartHelper.Bar("title", labels, vals));')
        assert detect_cell(cell) is True

    def test_flags_display_html_empty_output(self):
        # display(HTML("<svg ...>")) wrapper + ran + empty output.
        cell = _code_cell('display(HTML("<svg><rect/></svg>"));')
        assert detect_cell(cell) is True

    def test_flags_scattersvg_builder_empty_output(self):
        cell = _code_cell("var c = BuildScatterSvg(xs, ys); display(c);")
        assert detect_cell(cell) is True

    def test_passes_when_output_has_svg(self):
        # Happy path: chart display AND the SVG is in the output (not a white figure).
        cell = _code_cell(
            'display(SvgChartHelper.Bar("t", l, v));',
            outputs=[_svg_output()],
        )
        assert detect_cell(cell) is False

    def test_passes_when_exec_count_null(self):
        # Not executed -> outputs=[] is legitimate (not a white-figure regression).
        cell = _code_cell('display(SvgChartHelper.Bar("t", l, v));', exec_count=None)
        assert detect_cell(cell) is False

    def test_passes_when_outputs_nonempty_stream(self):
        # Has a stream output (Console.WriteLine) -> not the empty-display signature.
        cell = _code_cell(
            'Console.WriteLine("hi"); display(SvgChartHelper.Bar("t", l, v));',
            outputs=[{"name": "stdout", "output_type": "stream", "text": ["hi"]}],
        )
        assert detect_cell(cell) is False

    def test_passes_when_outputs_nonempty_error(self):
        # Has an error output -> different problem (caught by H.1), not flagged here.
        cell = _code_cell(
            'display(SvgChartHelper.Bar("t", l, v));',
            outputs=[{"output_type": "error", "ename": "Exception", "evalue": "boom"}],
        )
        assert detect_cell(cell) is False

    def test_passes_when_no_chart_display_pattern(self):
        # A legitimately silent cell (defines a function, no display(chart)) -> not flagged.
        cell = _code_cell("double Mean(double[] xs) => xs.Average();")
        assert detect_cell(cell) is False

    def test_passes_markdown_cell(self):
        assert detect_cell({"cell_type": "markdown", "source": ["# hi"], "outputs": []}) is False

    def test_passes_case_insensitive_display(self):
        # DISPLAY( vs display( — C# is case-insensitive; source may use either.
        cell = _code_cell('DISPLAY(SvgChartHelper.Bar("t", l, v));')
        assert detect_cell(cell) is True


# ---------------------------------------------------------------------------
# detect_cell_detail — reporting fields
# ---------------------------------------------------------------------------

class TestDetectCellDetail:
    def test_detail_returns_exec_count_and_pattern(self):
        cell = _code_cell('display(SvgChartHelper.Bar("t", l, v));', exec_count=7)
        d = detect_cell_detail(cell)
        assert d is not None
        assert d["exec_count"] == 7
        assert "SvgChartHelper" in d["matched_pattern"]

    def test_detail_returns_none_for_clean(self):
        cell = _code_cell("var x = 1;", outputs=[_svg_output()])
        assert detect_cell_detail(cell) is None


# ---------------------------------------------------------------------------
# scan_notebook (filesystem)
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_broken_notebook_flagged(self, tmp_path):
        # Mirror of #6963: 4 chart cells with empty output.
        cells = [
            _code_cell('display(SvgChartHelper.Bar("a", la, va));', exec_count=1),
            _code_cell('Console.WriteLine("setup");', exec_count=2,
                       outputs=[{"name": "stdout", "output_type": "stream", "text": ["setup"]}]),
            _code_cell('display(SvgChartHelper.Bar("b", lb, vb));', exec_count=3),
        ]
        p = _write_nb(tmp_path / "broken.ipynb", cells)
        result = scan_notebook(p)
        assert result["error"] is None
        assert len(result["hits"]) == 2
        assert {h["cell_index"] for h in result["hits"]} == {0, 2}

    def test_clean_notebook_no_hits(self, tmp_path):
        # Happy path: chart cells carry their SVG in the output.
        cells = [_code_cell('display(SvgChartHelper.Bar("t", l, v));', outputs=[_svg_output()])]
        p = _write_nb(tmp_path / "clean.ipynb", cells)
        result = scan_notebook(p)
        assert result["error"] is None
        assert result["hits"] == []

    def test_unreadable_notebook_error(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("{ not json", encoding="utf-8")
        result = scan_notebook(p)
        assert result["error"] is not None
        assert result["hits"] == []


# ---------------------------------------------------------------------------
# main() exit codes
# ---------------------------------------------------------------------------

class TestMainExitCodes:
    def test_check_clean_exit_0(self, tmp_path):
        p = _write_nb(tmp_path / "clean.ipynb",
                      [_code_cell('display(SvgChartHelper.Bar("t", l, v));', outputs=[_svg_output()])])
        assert main([str(p), "--check"]) == 0

    def test_check_broken_exit_1(self, tmp_path):
        p = _write_nb(tmp_path / "broken.ipynb",
                      [_code_cell('display(SvgChartHelper.Bar("t", l, v));')])
        assert main([str(p), "--check"]) == 1

    def test_missing_notebook_exit_2(self, tmp_path):
        assert main([str(tmp_path / "nope.ipynb")]) == 2

    def test_json_mode(self, tmp_path, capsys):
        p = _write_nb(tmp_path / "broken.ipynb",
                      [_code_cell('display(SvgChartHelper.Bar("t", l, v));', exec_count=5)])
        rc = main([str(p), "--json"])
        out = capsys.readouterr().out
        payload = json.loads(out)
        assert payload["total_hits"] == 1
        assert payload["results"][0]["hits"][0]["cell_index"] == 0
        assert rc == 0  # without --check, exit 0 even with hits
