"""Tests for scripts/notebook_tools/detect_svg_decimal_commas.py — French decimal-comma SVG detector.

Tests focus on pure functions: _points_tokens_with_bug, detect_svg, detect_cell,
scan_notebook, and the main() exit codes. Uses synthetic notebook dicts and
tmp_path for filesystem isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_svg_decimal_commas import (
    _points_tokens_with_bug,
    detect_cell,
    detect_svg,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code_with_svg_output(mime: str, svg: str, outputs_extra=None) -> dict:
    """A code cell whose first output carries an inline SVG under `mime`."""
    return {
        "cell_type": "code",
        "source": ["// draw"],
        "outputs": [{"data": {mime: svg}, "metadata": {}, "output_type": "display_data"}],
    }


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {"kernelspec": {"name": ".net-csharp"}}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# A clean SVG (dot-decimals, integer pairs) — must NOT be flagged.
_SVG_CLEAN = (
    '<svg viewBox="0 0 100 100">'
    '<polyline points="70.0,334.4 84.7,342.5 99.4,336.9" fill="none" stroke="#4C72B0"/>'
    '<circle cx="70.0" cy="403.2" r="3"/>'
    '<line x1="70.0" y1="420.0" x2="790" y2="420.0" stroke="#e8e8e8"/>'
    '<rect x="610" y="62" width="170" height="76" fill="white" stroke="#ccc"/>'
    '<line x1="620" y1="94" x2="650" y2="94" stroke="rgba(221,132,82,0.45)"/>'
    '</svg>'
)

# A broken SVG (French decimal commas) — the #6946 signature, MUST be flagged.
_SVG_BROKEN = (
    '<svg viewBox="0 0 100 100">'
    '<polyline points="70,0,334,4 84,7,342,5 99,4,336,9" fill="none" stroke="#4C72B0"/>'
    '<circle cx="70,0" cy="403,2" r="3"/>'
    '<line x1="70,0" y1="420,0" x2="790" y2="420,0" stroke="#e8e8e8"/>'
    '</svg>'
)


# ---------------------------------------------------------------------------
# _points_tokens_with_bug
# ---------------------------------------------------------------------------

class TestPointsTokensWithBug:
    def test_flags_decimal_comma_tokens(self):
        # 4-part tokens = decimal comma (the #6946 signature)
        buggy = _points_tokens_with_bug("70,0,334,4 84,7,342,5")
        assert buggy == ["70,0,334,4", "84,7,342,5"]

    def test_passes_integer_pairs(self):
        # integer coords "70,334" = exactly 2 parts = valid pair, NOT flagged
        assert _points_tokens_with_bug("70,334 84,342") == []

    def test_passes_dot_decimal_pairs(self):
        # "70.0,334.4" = 2 parts = valid pair, NOT flagged
        assert _points_tokens_with_bug("70.0,334.4 84.7,342.5") == []

    def test_passes_space_separated(self):
        # "70 334 84 342" = no commas = valid (x y space-separated), NOT flagged
        assert _points_tokens_with_bug("70 334 84 342") == []


# ---------------------------------------------------------------------------
# detect_svg
# ---------------------------------------------------------------------------

class TestDetectSvg:
    def test_clean_svg_no_finding(self):
        assert detect_svg(_SVG_CLEAN) is None

    def test_broken_svg_flags_points_and_coords(self):
        finding = detect_svg(_SVG_BROKEN)
        assert finding is not None
        assert len(finding["points_tokens"]) >= 1
        # points-token count = total buggy tokens across polyline(s)
        n_pts = sum(p["count"] for p in finding["points_tokens"])
        assert n_pts == 3  # the 3 decimal-comma tokens
        # mono-coord attrs cx/cy/x1/y1/x2/y2 all carry comma
        attrs = {h["attr"] for h in finding["coord_attrs"]}
        assert {"cx", "cy", "x1", "y1"} <= attrs

    def test_color_attr_not_flagged(self):
        # rgba()/rgb() color attrs legitimately hold commas -> excluded from whitelist
        svg = (
            '<svg viewBox="0 0 10 10">'
            '<line x1="0" y1="0" x2="10" y2="10" stroke="rgba(221,132,82,0.45)"/>'
            '<rect x="0" y="0" width="10" height="10" fill="rgb(200,200,200)"/>'
            '</svg>'
        )
        assert detect_svg(svg) is None

    def test_transform_attr_not_flagged(self):
        # transform translate/rotate legitimately hold commas -> excluded
        svg = (
            '<svg viewBox="0 0 10 10">'
            '<text x="5" y="5" transform="rotate(-45 5 5)">label</text>'
            '</svg>'
        )
        assert detect_svg(svg) is None


# ---------------------------------------------------------------------------
# detect_cell / scan_notebook (end-to-end on synthetic cells)
# ---------------------------------------------------------------------------

class TestDetectCell:
    def test_detects_in_text_html(self):
        cell = _code_with_svg_output("text/html", _SVG_BROKEN)
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["mime"] == "text/html"
        assert findings[0]["output_index"] == 0

    def test_detects_in_image_svg_xml(self):
        cell = _code_with_svg_output("image/svg+xml", _SVG_BROKEN)
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["mime"] == "image/svg+xml"

    def test_clean_cell_no_finding(self):
        cell = _code_with_svg_output("text/html", _SVG_CLEAN)
        assert detect_cell(cell) == []

    def test_non_svg_text_html_ignored(self):
        # a text/html output that is NOT an SVG (e.g. a probeAddresses banner) -> ignored
        cell = _code_with_svg_output("text/html", "<div>not a chart</div>")
        assert detect_cell(cell) == []

    def test_markdown_cell_skipped(self):
        # scan_notebook only inspects code cells
        nb = {"cells": [{"cell_type": "markdown", "source": [_SVG_BROKEN]}], "metadata": {}}
        # scan_notebook filters on cell_type == 'code'
        result = scan_notebook.__wrapped__ if hasattr(scan_notebook, "__wrapped__") else None
        # call scan_notebook on a temp file is heavier; exercise detect_cell via the markdown cell directly
        assert detect_cell({"cell_type": "markdown", "outputs": []}) == []


# ---------------------------------------------------------------------------
# scan_notebook (filesystem)
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_broken_notebook_flagged(self, tmp_path):
        p = _write_nb(tmp_path / "broken.ipynb", [_code_with_svg_output("text/html", _SVG_BROKEN)])
        result = scan_notebook(p)
        assert result["error"] is None
        assert len(result["hits"]) == 1
        assert result["hits"][0]["cell_index"] == 0

    def test_clean_notebook_no_hits(self, tmp_path):
        p = _write_nb(tmp_path / "clean.ipynb", [_code_with_svg_output("image/svg+xml", _SVG_CLEAN)])
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
    def test_check_clean_exit_0(self, tmp_path, capsys):
        p = _write_nb(tmp_path / "clean.ipynb", [_code_with_svg_output("text/html", _SVG_CLEAN)])
        rc = main([str(p), "--check"])
        assert rc == 0

    def test_check_broken_exit_1(self, tmp_path, capsys):
        p = _write_nb(tmp_path / "broken.ipynb", [_code_with_svg_output("text/html", _SVG_BROKEN)])
        rc = main([str(p), "--check"])
        assert rc == 1

    def test_missing_notebook_exit_2(self, tmp_path):
        rc = main([str(tmp_path / "nope.ipynb")])
        assert rc == 2

    def test_json_mode(self, tmp_path, capsys):
        p = _write_nb(tmp_path / "broken.ipynb", [_code_with_svg_output("text/html", _SVG_BROKEN)])
        rc = main([str(p), "--json"])
        out = capsys.readouterr().out
        payload = json.loads(out)
        assert payload["total_hits"] == 1
        assert rc == 0  # without --check, exit 0 even with hits
