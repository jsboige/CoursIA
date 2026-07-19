"""Tests for detect_svg_decimal_commas — fr-FR decimal-comma SVG defect scanner.

This scanner (#6959) guards the inline-SVG rollout (#6927) against the founding
incident #6946 (Infer-17 Kalman, fr-FR machine): a C# cell formatting coords
with `:F1` / `ToString()` emits decimal commas (`334.4` -> `334,4`), which
Chromium parses as a coordinate SEPARATOR -> zigzag charts. Every sibling
`detect_*` scanner has a `test_detect_*` except this one. These tests pin the
"zero false-positive" contract and the exact founding-incident signature.

Covers:
- ``_points_tokens_with_bug``: the >2-comma-parts signature (zero FP on integer
  pairs and dot-decimal pairs)
- ``_coord_attr_commas``: mono-coord attrs (cx/cy/x/y/...) with ``\\d,\\d``
- ``detect_svg``: end-to-end on a full <svg> block, single + double quotes
- ``_extract_svgs``: list/str payload, multiple blocks, non-SVG html
- ``scan_notebook``: cell-level wiring, no-SVG notebook = 0 hits, error path
- transform/rgba exclusion (no FP on legitimate CSS-like commas)

All fixtures are synthetic SVG strings — no notebook files, no network.
Runs in well under a second.
"""

from __future__ import annotations

import json
import os
import sys
import tempfile

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from detect_svg_decimal_commas import (  # noqa: E402
    _coord_attr_commas,
    _extract_svgs,
    _points_tokens_with_bug,
    detect_cell,
    detect_svg,
    scan_notebook,
)


# ── _points_tokens_with_bug ─────────────────────────────────────────────────

class TestPointsTokensWithBug:
    def test_founding_incident_4_parts_flagged(self) -> None:
        # PR #6946 signature: "70,0,334,4" = 4 comma-parts = decimal-comma bug.
        buggy = _points_tokens_with_bug("70,0,334,4 110,2,334,9")
        assert "70,0,334,4" in buggy
        assert "110,2,334,9" in buggy
        assert len(buggy) == 2

    def test_integer_pair_zero_false_positive(self) -> None:
        # "70,334" = exactly 2 parts = valid integer (x,y) pair -> NOT flagged.
        assert _points_tokens_with_bug("70,334 110,200 90,180") == []

    def test_dot_decimal_pair_zero_false_positive(self) -> None:
        # "70.0,334.4" = 2 parts (dot, not comma) = valid decimal pair -> OK.
        assert _points_tokens_with_bug("70.0,334.4 110.2,200.9") == []

    def test_mixed_valid_and_buggy_tokens(self) -> None:
        # Only the >2-parts token is flagged; the valid 2-parts tokens are clean.
        buggy = _points_tokens_with_bug("70,334 12,5,334,4 110,200")
        assert buggy == ["12,5,334,4"]

    def test_empty_and_whitespace_handled(self) -> None:
        assert _points_tokens_with_bug("") == []
        assert _points_tokens_with_bug("   ") == []


# ── _coord_attr_commas ──────────────────────────────────────────────────────

class TestCoordAttrCommas:
    def test_mono_coord_decimal_comma_flagged(self) -> None:
        svg = '<circle cx="70,5" cy="334,4" r="3"/>'
        out = _coord_attr_commas(svg)
        attrs = {f["attr"] for f in out}
        assert "cx" in attrs
        assert "cy" in attrs

    def test_dot_decimal_not_flagged(self) -> None:
        svg = '<circle cx="70.5" cy="334.4" r="3"/>'
        assert _coord_attr_commas(svg) == []

    def test_integer_coord_not_flagged(self) -> None:
        svg = '<rect x="10" y="20" width="100" height="50"/>'
        assert _coord_attr_commas(svg) == []

    def test_transform_excluded(self) -> None:
        # transform="translate(334,4)" uses comma as a SEPARATOR between two
        # integer coords -> legitimate. transform is NOT in the coord-attr
        # whitelist -> must never be flagged (no FP).
        svg = '<g transform="translate(334,4) rotate(45,10,10)"><rect/></g>'
        out = _coord_attr_commas(svg)
        assert all(f["attr"] != "transform" for f in out)

    def test_single_and_double_quotes_both_parsed(self) -> None:
        # C# interpolation emits either cx='{v}' or cx="{v}" depending on the
        # quote style; both must parse (backreferenced quote group).
        sv = '<circle cx=\'70,5\'/><circle cx="90,2"/>'
        out = _coord_attr_commas(sv)
        assert len(out) == 2


# ── detect_svg (end-to-end on a block) ──────────────────────────────────────

class TestDetectSvg:
    def test_clean_svg_returns_none(self) -> None:
        clean = '<svg><polyline points="10,20 30,40"/><circle cx="5" cy="6" r="2"/></svg>'
        assert detect_svg(clean) is None

    def test_buggy_points_detected(self) -> None:
        buggy = '<svg><polyline points="70,0,334,4 110,2,200,9"/></svg>'
        out = detect_svg(buggy)
        assert out is not None
        assert out["points_tokens"]
        assert out["points_tokens"][0]["count"] == 2

    def test_buggy_coord_attr_detected(self) -> None:
        buggy = '<svg><circle cx="70,5" cy="334,4" r="3"/></svg>'
        out = detect_svg(buggy)
        assert out is not None
        assert out["coord_attrs"]
        assert len(out["coord_attrs"]) == 2

    def test_both_defect_classes_reported_together(self) -> None:
        buggy = ('<svg><polyline points="70,0,334,4"/>'
                 '<circle cx="11,2" cy="33,4" r="3"/></svg>')
        out = detect_svg(buggy)
        assert out is not None
        assert out["points_tokens"]
        assert out["coord_attrs"]


# ── _extract_svgs ───────────────────────────────────────────────────────────

class TestExtractSvgs:
    def test_str_payload(self) -> None:
        payload = 'foo <svg><rect/></svg> bar'
        assert len(_extract_svgs(payload)) == 1

    def test_list_payload_concatenated(self) -> None:
        # notebook outputs sometimes carry a list of string chunks.
        payload = ["<svg><rect/", "/></svg>"]
        assert len(_extract_svgs(payload)) == 1

    def test_multiple_blocks(self) -> None:
        payload = '<svg><rect/></svg> mid <svg><circle/></svg>'
        assert len(_extract_svgs(payload)) == 2

    def test_non_svg_html_returns_empty(self) -> None:
        assert _extract_svgs("<div><p>hello</p></div>") == []

    def test_non_str_returns_empty(self) -> None:
        assert _extract_svgs(None) == []
        assert _extract_svgs(123) == []


# ── detect_cell / scan_notebook (wiring) ────────────────────────────────────

def _nb_with_svg_output(svg: str, mime: str = "image/svg+xml") -> dict:
    """Minimal notebook: one code cell whose first output carries `svg`."""
    return {
        "metadata": {"kernelspec": {"name": ".net-csharp"}},
        "cells": [
            {
                "cell_type": "code",
                "outputs": [
                    {"data": {mime: svg}},
                ],
            }
        ],
    }


class TestDetectCell:
    def test_clean_svg_output_no_findings(self) -> None:
        cell = _nb_with_svg_output(
            '<svg><polyline points="10,20 30,40"/></svg>'
        )["cells"][0]
        assert detect_cell(cell) == []

    def test_buggy_svg_output_findings(self) -> None:
        cell = _nb_with_svg_output(
            '<svg><polyline points="70,0,334,4"/></svg>'
        )["cells"][0]
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["output_index"] == 0
        assert findings[0]["mime"] == "image/svg+xml"
        assert findings[0]["points_tokens"]

    def test_svg_in_text_html_mime_also_scanned(self) -> None:
        # text/html outputs can carry inline SVG too (both MIMEs scanned).
        cell = _nb_with_svg_output(
            '<div><svg><circle cx="11,2" cy="3,3" r="1"/></svg></div>',
            mime="text/html",
        )["cells"][0]
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["mime"] == "text/html"


class TestScanNotebook:
    def test_no_svg_notebook_zero_hits(self) -> None:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".ipynb", delete=False, encoding="utf-8"
        ) as f:
            json.dump({
                "metadata": {"kernelspec": {"name": "python3"}},
                "cells": [
                    {"cell_type": "code", "outputs": [{"data": {"text/plain": "42"}}]},
                    {"cell_type": "markdown", "source": ["# no svg here"]},
                ],
            }, f)
            path = f.name
        try:
            res = scan_notebook(__import__("pathlib").Path(path))
            assert res["hits"] == []
            assert res["error"] is None
            assert res["kernel"] == "python3"
        finally:
            os.unlink(path)

    def test_buggy_notebook_reports_hit_with_cell_index(self) -> None:
        nb = _nb_with_svg_output('<svg><polyline points="70,0,334,4"/></svg>')
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".ipynb", delete=False, encoding="utf-8"
        ) as f:
            json.dump(nb, f)
            path = f.name
        try:
            from pathlib import Path
            res = scan_notebook(Path(path))
            assert len(res["hits"]) == 1
            assert res["hits"][0]["cell_index"] == 0
            assert res["kernel"] == ".net-csharp"
        finally:
            os.unlink(path)

    def test_unreadable_file_returns_error_not_raise(self) -> None:
        from pathlib import Path
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".ipynb", delete=False, encoding="utf-8"
        ) as f:
            f.write("{not valid json")
            path = f.name
        try:
            res = scan_notebook(Path(path))
            assert res["error"] is not None
            assert res["hits"] == []
        finally:
            os.unlink(path)
