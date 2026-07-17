"""Tests for scripts/notebook_tools/detect_svg_decimal_comma.py.

The detector prevents a silent rendering regression: an inline-C# SVG builder
that formats coordinates with culture-sensitive ``:F1`` emits a decimal COMMA on
fr-FR machines, which Chromium reads as a coordinate separator (so ``cx='70,0'``
becomes "Expected length" -> 0, and a polyline ``70,0,334,4`` becomes 4 points
instead of 2). The defect is invisible to every code forensic (CI validates
structure, the SVG tag is present) — only render QA catches it (PRs #6946
Infer-17, #6960 MGS-15, found by po-2024 vision-QA c.581). This detector makes
it un-committable via the CI guard.

These tests lock the two unambiguous bug signatures and confirm Graphviz
legit-integer SVGs do NOT trip them (the naive ``\\d,\\d`` regex would).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

from detect_svg_decimal_comma import (  # noqa: E402
    find_decimal_comma_defects,
    scan_notebook,
)


# --- find_decimal_comma_defects: the two bug signatures ----------------------


def test_clean_decimal_dot_svg_has_no_defects():
    # The CORRECT output: comma is the coordinate separator, values use decimal dot.
    html = (
        "<svg viewBox='0 0 820 480'>"
        "<polyline points='70,334.362 84.694,342.457'/>"
        "<circle cx='12.5' cy='45.7' r='2.5'/>"
        "</svg>"
    )
    assert find_decimal_comma_defects(html) == []


def test_multi_comma_polyline_point_is_defect():
    # The #6946 regression: "70,0,334,4" is 4 numbers, never a valid x,y pair.
    html = "<svg><polyline points='70,0,334,4 84,7,342,5'/></svg>"
    defects = find_decimal_comma_defects(html)
    assert len(defects) == 1
    assert "70,0,334,4" in defects[0]


def test_single_attr_decimal_comma_is_defect():
    # cx='70,0' (comma inside a single coord value) = decimal-comma bug.
    html = "<svg><circle cx='70,0' cy='4,5' r='3'/></svg>"
    defects = find_decimal_comma_defects(html)
    # cx and cy both flagged
    assert any("cx=" in d for d in defects)
    assert any("cy=" in d for d in defects)


def test_graphviz_integer_coords_not_flagged():
    # Graphviz model diagrams use legit integer coords: "points='10,20 30,40'".
    # Each token is exactly "x,y" (one comma) and cx='10' is a bare integer.
    # This MUST NOT trip the detector (confirmed repo-wide: the naive \d,\d
    # regex would flag ~56 Graphviz SVGs as false positives).
    html = (
        "<svg width='236pt' height='289pt' viewBox='0.00 0.00 236.00 289.00'>"
        "<g id='graph0' class='graph' transform='scale(1 1)'>"
        "<polygon points='10,20 30,40 50,60'/>"
        "<ellipse cx='100' cy='200' rx='5' ry='5'/>"
        "</g></svg>"
    )
    assert find_decimal_comma_defects(html) == []


def test_no_svg_returns_empty():
    assert find_decimal_comma_defects("<div>hello</div>") == []


def test_empty_points_not_flagged():
    html = "<svg><polyline points=''/></svg>"
    assert find_decimal_comma_defects(html) == []


# --- scan_notebook: notebook-level integration -------------------------------


def _write_nb(tmp_path, outputs_html):
    """Write a minimal .ipynb with one code cell whose output is outputs_html."""
    nb = {
        "cells": [
            {"cell_type": "code", "execution_count": 1, "source": ["// x"],
             "outputs": [{"data": {"text/html": outputs_html}}], "metadata": {}}
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "t.ipynb"
    p.write_text(__import__("json").dumps(nb), encoding="utf-8")
    return str(p)


def test_scan_clean_notebook(tmp_path):
    p = _write_nb(tmp_path, "<svg><circle cx='12.5' cy='45.7'/></svg>")
    assert scan_notebook(p) == []


def test_scan_defective_notebook(tmp_path):
    p = _write_nb(tmp_path, "<svg><polyline points='70,0,334,4'/></svg>")
    found = scan_notebook(p)
    assert len(found) == 1
    ci, defects = found[0]
    assert ci == 0
    assert len(defects) >= 1


def test_scan_list_format_html_blob(tmp_path):
    # On-disk text/html is a list[str]; verify the detector handles it.
    import json
    nb = {
        "cells": [
            {"cell_type": "code", "execution_count": 1, "source": ["// x"],
             "outputs": [{"data": {"text/html": ["<svg><polyline points='70,0,334,4'/></svg>"]}}],
             "metadata": {}}
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "list.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    assert len(scan_notebook(str(p))) == 1
