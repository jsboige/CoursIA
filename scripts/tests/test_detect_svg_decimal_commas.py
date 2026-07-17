"""Tests for scripts/notebook_tools/detect_svg_decimal_commas.py (#6959).

The detector (canon, merged in #6959, wired as a per-PR CI gate in #6965)
prevents a silent rendering regression: an inline-C# SVG builder that formats
coordinates with culture-sensitive ``:F1`` emits a decimal COMMA on fr-FR
machines, which Chromium reads as a coordinate separator (so ``cx="70,0"``
becomes "Expected length" -> 0, and a polyline ``70,0,334,4`` becomes 4 points
instead of 2). The defect is invisible to every code forensic (CI validates
structure, the SVG tag is present) -- only render QA catches it (PRs #6946
Infer-17, #6960 MGS-15, found by po-2024 vision-QA c.581). The detector + CI
gate make it un-committable.

These tests lock the detector's two unambiguous bug signatures AND confirm
Graphviz legit-integer SVGs do NOT trip them (the naive ``\\d,\\d`` regex
would flag ~56 Graphviz SVGs as false positives -- the precise detection
is the detector's whole value).

Targets the public API: ``detect_svg`` (one SVG block), ``detect_cell`` (one
code cell, possibly multi-SVG / multi-mime), ``scan_notebook`` (file-level).
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

from detect_svg_decimal_commas import (  # noqa: E402
    detect_cell,
    detect_svg,
    scan_notebook,
)


# --- detect_svg: the two bug signatures --------------------------------------


def test_clean_decimal_dot_svg_has_no_defect():
    # The CORRECT output: comma is the coordinate separator, values use decimal dot.
    svg = (
        "<svg viewBox='0 0 820 480'>"
        "<polyline points='70,334.362 84.694,342.457'/>"
        "<circle cx='12.5' cy='45.7' r='2.5'/>"
        "</svg>"
    )
    assert detect_svg(svg) is None


def test_multi_comma_polyline_point_is_defect():
    # The #6946 regression: "70,0,334,4" is 4 numbers (>2 parts), never a valid x,y.
    svg = "<svg><polyline points='70,0,334,4 84,7,342,5'/></svg>"
    finding = detect_svg(svg)
    assert finding is not None
    assert finding["points_tokens"], "expected at least one buggy points token"
    # the sample token "70,0,334,4" must be captured
    samples = [t for pt in finding["points_tokens"] for t in pt["sample_tokens"]]
    assert any("70,0,334,4" in t for t in samples)


def test_single_attr_decimal_comma_is_defect():
    # cx="70,0" (comma inside a single coord value) = decimal-comma bug.
    svg = '<svg><circle cx="70,0" cy="4,5" r="3"/></svg>'
    finding = detect_svg(svg)
    assert finding is not None
    attrs = {f["attr"] for f in finding["coord_attrs"]}
    assert "cx" in attrs
    assert "cy" in attrs


def test_graphviz_integer_coords_not_flagged():
    # Graphviz model diagrams use legit integer coords: "points='10,20 30,40'".
    # Each token is exactly "x,y" (one comma -> 2 parts) and cx="100" is a bare
    # integer. This MUST NOT trip the detector (the naive \d,\d regex would flag
    # ~56 Graphviz SVGs as false positives repo-wide).
    svg = (
        '<svg width="236pt" height="289pt" viewBox="0.00 0.00 236.00 289.00">'
        '<g id="graph0" class="graph" transform="scale(1 1)">'
        '<polygon points="10,20 30,40 50,60"/>'
        '<ellipse cx="100" cy="200" rx="5" ry="5"/>'
        "</g></svg>"
    )
    assert detect_svg(svg) is None


def test_valid_two_part_decimal_pair_not_flagged():
    # A correctly-formatted decimal pair: "70.0,334.4" = 2 parts, decimal dot.
    svg = "<svg><polyline points='70.0,334.4 84.7,342.5'/></svg>"
    assert detect_svg(svg) is None


def test_empty_points_not_flagged():
    svg = "<svg><polyline points=''/></svg>"
    assert detect_svg(svg) is None


def test_no_svg_block_returns_none():
    assert detect_svg("<div>hello</div>") is None


# --- detect_cell: cell-level (multi-mime, multi-SVG) ------------------------


def _code_cell_with_html(html, as_list=False):
    blob = [html] if as_list else html
    return {
        "cell_type": "code",
        "execution_count": 1,
        "source": ["// x"],
        "outputs": [{"data": {"text/html": blob}}],
        "metadata": {},
    }


def test_detect_cell_clean_returns_empty():
    cell = _code_cell_with_html("<svg><circle cx='12.5' cy='45.7'/></svg>")
    assert detect_cell(cell) == []


def test_detect_cell_defective_returns_finding():
    cell = _code_cell_with_html("<svg><polyline points='70,0,334,4'/></svg>")
    findings = detect_cell(cell)
    assert len(findings) == 1
    assert findings[0]["output_index"] == 0
    assert "text/html" in findings[0]["mime"]


def test_detect_cell_handles_list_html_blob():
    # On-disk text/html is a list[str]; the detector must join then extract.
    cell = _code_cell_with_html("<svg><polyline points='70,0,334,4'/></svg>", as_list=True)
    findings = detect_cell(cell)
    assert len(findings) == 1


# --- scan_notebook: file-level integration -----------------------------------


def _write_nb(tmp_path, outputs_html):
    nb = {
        "cells": [
            {"cell_type": "code", "execution_count": 1, "source": ["// x"],
             "outputs": [{"data": {"text/html": outputs_html}}], "metadata": {}}
        ],
        "metadata": {"kernelspec": {"name": ".net-csharp", "display_name": ".NET (C#)"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "t.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    return Path(p)


def test_scan_notebook_clean(tmp_path):
    p = _write_nb(tmp_path, "<svg><circle cx='12.5' cy='45.7'/></svg>")
    result = scan_notebook(p)
    assert result["error"] is None
    assert result["hits"] == []
    assert result["kernel"] == ".net-csharp"


def test_scan_notebook_defective_reports_cell_index(tmp_path):
    p = _write_nb(tmp_path, "<svg><polyline points='70,0,334,4'/></svg>")
    result = scan_notebook(p)
    assert result["error"] is None
    assert len(result["hits"]) == 1
    assert result["hits"][0]["cell_index"] == 0


def test_scan_notebook_missing_file_reports_error(tmp_path):
    result = scan_notebook(tmp_path / "does-not-exist.ipynb")
    assert result["error"] is not None
    assert result["hits"] == []
