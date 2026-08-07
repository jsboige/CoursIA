"""Tests for scripts/notebook_tools/detect_svg_broken_geometry.py (#7007/#6927).

The detector (canon, wired as the per-PR CI gate ``svg-broken-geometry-gate``)
catches a silent rendering regression that every other check misses: an inline
SVG whose ``<rect>/<use>/<image>`` element has a NEGATIVE ``width`` or
``height``. By the SVG spec a negative dimension is invalid and the element
does not render (invisible bar). The defect is invisible to code forensics
(the ``<svg>`` tag is present, the cell executed, the output non-empty) -- it
was the exact hole through which a buggy ``logY`` plot was merged (#7007): a
``PlotLayout`` built in LINEAR bounds while the projection ``YF`` mapped in
log10 pushed bars more than a decade below the max UNDER the plot floor,
producing ``<rect height='-893'>`` bars that vanished from the committed
figure while CI stayed green. The detector + gate make it un-committable.

Key correctness property: the check is DETERMINISTIC and ZERO false-positive.
Per the module docstring, ``width``/``height`` are never relocated by a
``transform`` (only position is) and no legitimate SVG emitter produces a
negative dimension, so every hit is a real defect. Crucially the regex anchors
on ``\\b(width|height)`` so a negative ``strokeWidth``/``patternWidth`` (which
CAN legitimately be negative in some contexts) does NOT trip it -- locking
that zero-FP property is a core test target.

Targets the public API: ``detect_svg`` (one SVG block), ``detect_cell`` (one
code cell, possibly multi-SVG / multi-mime), ``scan_notebook`` (file-level),
and the ``main`` exit codes (CI-ready ``--check``).
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

from detect_svg_broken_geometry import (  # noqa: E402
    _extract_svgs,
    _negative_dims,
    detect_cell,
    detect_svg,
    main,
    scan_notebook,
)


# --- detect_svg: the negative-dimension bug signature -----------------------


def test_clean_svg_no_defect():
    svg = (
        "<svg viewBox='0 0 820 480'>"
        "<rect x='10' y='20' width='100' height='50' fill='steelblue'/>"
        "<line x1='0' y1='0' x2='100' y2='100'/>"
        "</svg>"
    )
    assert detect_svg(svg) is None


def test_negative_height_flagged():
    # The #7007 signature: a bar projected under the plot floor.
    svg = "<svg><rect x='0' y='0' width='10' height='-893'/></svg>"
    f = detect_svg(svg)
    assert f is not None
    assert f["negative_dims"]["count"] == 1
    assert f["negative_dims"]["samples"][0] == {"attr": "height", "value": "-893"}


def test_negative_width_flagged():
    svg = "<svg><rect width='-42' height='5'/></svg>"
    f = detect_svg(svg)
    assert f is not None
    assert f["negative_dims"]["samples"][0]["attr"] == "width"
    assert f["negative_dims"]["samples"][0]["value"] == "-42"


def test_negative_decimal_dimension_flagged():
    svg = "<svg><rect width='-1.5' height='-2.25'/></svg>"
    f = detect_svg(svg)
    assert f is not None
    assert f["negative_dims"]["count"] == 2


def test_single_and_double_quotes_both_matched():
    # The regex backreferences the opening quote: width='...' and width="..." both valid.
    svg_sq = "<svg><rect width='-5' height='3'/></svg>"
    svg_dq = '<svg><rect width="-5" height="3"/></svg>'
    assert detect_svg(svg_sq) is not None
    assert detect_svg(svg_dq) is not None


def test_multiple_neg_dims_counted_and_capped_at_5_samples():
    # 8 negative dimensions -> count=8, samples capped at 5.
    rects = "".join(f"<rect width='-{i}' height='-{i}'/>" for i in range(1, 5))
    svg = "<svg>" + rects + "</svg>"
    f = detect_svg(svg)
    assert f is not None
    assert f["negative_dims"]["count"] == 8
    assert len(f["negative_dims"]["samples"]) == 5


def test_strokewidth_negative_not_flagged():
    # CRITICAL zero-FP property: \\b(width|height) must NOT match strokeWidth
    # (no word boundary between 'e' and 'w'). A negative strokeWidth is a
    # different attribute and must not trip this detector.
    svg = "<svg><line x1='0' y1='0' x2='10' y2='10' strokeWidth='-2'/></svg>"
    assert detect_svg(svg) is None


def test_coordinate_negative_not_flagged():
    # Negative x/y coordinates ARE legitimate (relocated by a transform); only
    # dimensions are defects. This is the explicit design choice (see module
    # docstring "Pourquoi PAS de test coordonnee hors viewBox").
    svg = "<svg><rect x='-50' y='-30' width='100' height='40'/></svg>"
    assert detect_svg(svg) is None


def test_zero_and_positive_dimensions_clean():
    svg = "<svg><rect width='0' height='0'/><rect width='1000' height='0.5'/></svg>"
    assert detect_svg(svg) is None


# --- _extract_svgs: payload handling ----------------------------------------


def test_extract_svgs_from_string():
    payload = "<svg><rect/></svg><svg><circle/></svg>"
    blocks = _extract_svgs(payload)
    assert len(blocks) == 2


def test_extract_svgs_from_list_joined():
    # nbformat stores multi-line outputs as a list of string fragments.
    payload = ["<svg><rect", " width='5'/></svg>"]
    blocks = _extract_svgs(payload)
    assert len(blocks) == 1
    assert "width='5'" in blocks[0]


def test_extract_svgs_non_string_returns_empty():
    assert _extract_svgs(None) == []
    assert _extract_svgs(123) == []
    assert _extract_svgs([]) == []


def test_negative_dims_returns_attr_value_dicts():
    svg = "<svg><rect width='-9' height='-4'/></svg>"
    dims = _negative_dims(svg)
    assert dims == [{"attr": "width", "value": "-9"}, {"attr": "height", "value": "-4"}]


# --- detect_cell: cell-level aggregation ------------------------------------


def _code_cell(outputs):
    return {"cell_type": "code", "outputs": outputs, "execution_count": 1}


def test_detect_cell_svg_xml_mime():
    cell = _code_cell([{"output_type": "display_data",
                        "data": {"image/svg+xml":
                                 "<svg><rect height='-12'/></svg>"}}])
    findings = detect_cell(cell)
    assert len(findings) == 1
    assert findings[0]["mime"] == "image/svg+xml"
    assert findings[0]["output_index"] == 0
    assert findings[0]["negative_dims"]["count"] == 1
    assert findings[0]["svg_chars"] > 0


def test_detect_cell_html_mime():
    # SVG can also ride inside a text/html output (Plotly/altair wrappers).
    cell = _code_cell([{"output_type": "display_data",
                        "data": {"text/html":
                                 "<div><svg><rect width='-7'/></svg></div>"}}])
    findings = detect_cell(cell)
    assert len(findings) == 1
    assert findings[0]["mime"] == "text/html"


def test_detect_cell_clean_svg_no_finding():
    cell = _code_cell([{"output_type": "display_data",
                        "data": {"image/svg+xml":
                                 "<svg><rect width='10' height='5'/></svg>"}}])
    assert detect_cell(cell) == []


def test_detect_cell_no_svg_data_empty():
    cell = _code_cell([{"output_type": "stream", "name": "stdout", "text": ["hello"]}])
    assert detect_cell(cell) == []


def test_detect_cell_multiple_outputs_indexed():
    cell = _code_cell([
        {"output_type": "display_data",
         "data": {"image/svg+xml": "<svg><rect width='10'/></svg>"}},
        {"output_type": "display_data",
         "data": {"image/svg+xml": "<svg><rect height='-3'/></svg>"}},
    ])
    findings = detect_cell(cell)
    assert len(findings) == 1
    assert findings[0]["output_index"] == 1  # only the 2nd output is defective


# --- scan_notebook: file-level ----------------------------------------------


def _write_nb(tmp_path, cells, kernel="python3"):
    nb = {"cells": cells,
          "metadata": {"kernelspec": {"name": kernel, "display_name": "Py3",
                                       "language": "python"}},
          "nbformat": 4, "nbformat_minor": 5}
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def test_scan_notebook_clean(tmp_path):
    md = {"cell_type": "markdown", "metadata": {}, "source": ["# title"]}
    code = _code_cell([{"output_type": "display_data",
                        "data": {"image/svg+xml":
                                 "<svg><rect width='5' height='5'/></svg>"}}])
    p = _write_nb(tmp_path, [md, code])
    r = scan_notebook(p)
    assert r["hits"] == []
    assert r["error"] is None
    assert r["kernel"] == "python3"


def test_scan_notebook_finds_defect_with_cell_index(tmp_path):
    code = _code_cell([{"output_type": "display_data",
                        "data": {"image/svg+xml":
                                 "<svg><rect height='-66'/></svg>"}}])
    md = {"cell_type": "markdown", "source": ["intro"]}
    p = _write_nb(tmp_path, [md, code])  # code cell is index 1
    r = scan_notebook(p)
    assert len(r["hits"]) == 1
    assert r["hits"][0]["cell_index"] == 1
    assert r["error"] is None


def test_scan_notebook_skips_non_code_cells(tmp_path):
    # A markdown cell carrying a negative-dim SVG string in its SOURCE must
    # not be scanned (we only inspect code-cell OUTPUTS).
    md = {"cell_type": "markdown",
          "source": ["<svg><rect height='-5'/></svg>"]}
    p = _write_nb(tmp_path, [md])
    r = scan_notebook(p)
    assert r["hits"] == []


def test_scan_notebook_unreadable_file_returns_error(tmp_path):
    bad = tmp_path / "broken.ipynb"
    bad.write_text("{not valid json", encoding="utf-8")
    r = scan_notebook(bad)
    assert r["error"] is not None
    assert r["hits"] == []


def test_scan_notebook_missing_file_returns_error(tmp_path):
    r = scan_notebook(tmp_path / "ghost.ipynb")
    assert r["error"] is not None


# --- main: exit codes (CI-ready --check) ------------------------------------


def test_main_clean_check_exits_zero(tmp_path, capsys):
    code = _code_cell([{"output_type": "display_data",
                        "data": {"image/svg+xml":
                                 "<svg><rect width='5' height='5'/></svg>"}}])
    p = _write_nb(tmp_path, [code])
    rc = main([str(p), "--check"])
    assert rc == 0


def test_main_defect_check_exits_one(tmp_path, capsys):
    code = _code_cell([{"output_type": "display_data",
                        "data": {"image/svg+xml":
                                 "<svg><rect height='-100'/></svg>"}}])
    p = _write_nb(tmp_path, [code])
    rc = main([str(p), "--check"])
    assert rc == 1


def test_main_not_found_exits_two(capsys):
    rc = main(["definitely_missing_notebook_xyz.ipynb"])
    assert rc == 2


def test_main_json_output_shape(tmp_path, capsys):
    code = _code_cell([{"output_type": "display_data",
                        "data": {"image/svg+xml":
                                 "<svg><rect height='-3'/></svg>"}}])
    p = _write_nb(tmp_path, [code])
    rc = main([str(p), "--json"])
    out = json.loads(capsys.readouterr().out)
    assert out["notebooks_scanned"] == 1
    assert out["total_hits"] == 1
    assert rc == 0  # no --check, so exit 0 even with a defect
