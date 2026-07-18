"""Tests for scripts/notebook_tools/detect_svg_offscreen_flat.py -- flat-SVG
data geometry projected far off the viewBox (>15% of its height) detector.

Tests focus on the pure helpers (_extract_svgs, _f), the core detect_svg
contract (viewBox parsing, moving-transform deferral, rect/line/circle
bounds, 15% margin, text exclusion, sample cap), detect_cell MIME routing,
scan_notebook filesystem + error handling, _should_skip filtering, and the
main() exit codes. Uses synthetic SVG fragments and tmp_path for isolation.

See #7032 (gate MERGED, detector live), EPIC #3801 (SOTA axe-2), See #6927.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_svg_offscreen_flat import (  # noqa: E402
    _extract_svgs,
    _f,
    _should_skip,
    detect_cell,
    detect_svg,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _svg(body: str = "", viewBox: str = "0 0 100 100") -> str:
    """Wrap geometry in a minimal <svg> with the given viewBox (default 0..100)."""
    return f'<svg viewBox="{viewBox}">{body}</svg>'


def _offscreen_rect(y: float = -893.0, height: float = 10.0) -> str:
    return f'<rect x="0" y="{y}" width="10" height="{height}"/>'


def _code_cell(outputs: list[dict], source: str = "display(chart);", exec_count=1) -> dict:
    return {
        "cell_type": "code",
        "execution_count": exec_count,
        "source": [source],
        "outputs": outputs,
    }


def _svg_output(svg: str, mime: str = "image/svg+xml") -> dict:
    return {"data": {mime: svg}, "metadata": {}, "output_type": "display_data"}


def _write_nb(path: Path, cells: list[dict], kernel: str = ".net-csharp") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# _extract_svgs
# ---------------------------------------------------------------------------

class TestExtractSvgs:
    def test_string_payload_finds_blocks(self):
        out = _extract_svgs('<svg viewBox="0 0 1 1"><rect/></svg>text<svg></svg>')
        assert len(out) == 2

    def test_list_payload_is_joined(self):
        # SVG split across list fragments (notebook cell output form) is reassembled.
        out = _extract_svgs(['<svg viewBox="0 0 1 1">', "<rect/></svg>"])
        assert len(out) == 1

    def test_non_string_payload_returns_empty(self):
        assert _extract_svgs(None) == []
        assert _extract_svgs(42) == []
        assert _extract_svgs({"k": "v"}) == []

    def test_no_svg_returns_empty(self):
        assert _extract_svgs("just text, no markup") == []


# ---------------------------------------------------------------------------
# _f (float parse)
# ---------------------------------------------------------------------------

class TestF:
    def test_parses_int_and_decimal(self):
        assert _f("100") == 100.0
        assert _f("-893.5") == -893.5

    def test_returns_none_on_garbage(self):
        assert _f("abc") is None
        assert _f("1.2.3") is None  # double dot -- the unparseable-but-regex-match branch

    def test_returns_none_on_none(self):
        assert _f(None) is None


# ---------------------------------------------------------------------------
# detect_svg -- viewBox parsing + None cases
# ---------------------------------------------------------------------------

class TestDetectSvgViewBox:
    def test_no_viewbox_returns_none(self):
        assert detect_svg("<svg><rect/></svg>") is None

    def test_zero_height_returns_none(self):
        # viewBox height == 0 -> degenerate frame, cannot bound-check.
        assert detect_svg(_svg(viewBox="0 0 100 0", body=_offscreen_rect())) is None

    def test_negative_height_returns_none(self):
        assert detect_svg(_svg(viewBox="0 0 100 -5", body=_offscreen_rect())) is None

    def test_unparseable_height_returns_none(self):
        # "1.2.3" passes the viewBox regex char class but float() rejects it.
        assert detect_svg(_svg(viewBox="0 0 100 1.2.3", body=_offscreen_rect())) is None

    def test_clean_geometry_within_viewbox_returns_none(self):
        # A healthy chart draws everything inside [minY, minY+h].
        assert detect_svg(_svg(body='<rect x="0" y="50" width="10" height="10"/>')) is None

    def test_rect_filling_viewbox_exactly_returns_none(self):
        # Edge-to-edge (no overshoot) is on-screen.
        assert detect_svg(_svg(body='<rect x="0" y="0" width="100" height="100"/>')) is None


# ---------------------------------------------------------------------------
# detect_svg -- moving-transform deferral (the anti-FP filter)
# ---------------------------------------------------------------------------

class TestDetectSvgMovingTransform:
    def test_translate_deferred_to_vision(self):
        svg = _svg(body=f'<g transform="translate(10,20)">{_offscreen_rect()}</g>')
        assert detect_svg(svg) is None

    def test_matrix_deferred_to_vision(self):
        svg = _svg(body=f'<g transform="matrix(1,0,0,1,5,5)">{_offscreen_rect()}</g>')
        assert detect_svg(svg) is None

    def test_scale_deferred_to_vision(self):
        svg = _svg(body=f'<g transform="scale(2)">{_offscreen_rect()}</g>')
        assert detect_svg(svg) is None

    def test_rotate_is_not_deferred(self):
        # rotate pivots labels (text), does not translate data geometry off-frame:
        # bounds are still checked and the offscreen rect IS flagged.
        svg = _svg(body=f'<g transform="rotate(45)">{_offscreen_rect()}</g>')
        finding = detect_svg(svg)
        assert finding is not None
        assert finding["offscreen"]["count"] >= 1


# ---------------------------------------------------------------------------
# detect_svg -- data-geometry bounds (rect / line / circle)
# ---------------------------------------------------------------------------

class TestDetectSvgGeometry:
    def test_offscreen_rect_flagged(self):
        finding = detect_svg(_svg(body=_offscreen_rect(y=-893.0, height=10.0)))
        assert finding is not None
        samples = finding["offscreen"]["samples"]
        assert any(s["el"] == "rect" and s["y"] == -893.0 for s in samples)

    def test_offscreen_line_flagged(self):
        body = '<line x1="0" y1="-893" x2="10" y2="-800"/>'
        finding = detect_svg(_svg(body=body))
        assert finding is not None
        assert any(s["el"] == "line" for s in finding["offscreen"]["samples"])

    def test_offscreen_circle_flagged(self):
        body = '<circle cx="5" cy="-893" r="2"/>'
        finding = detect_svg(_svg(body=body))
        assert finding is not None
        assert any(s["el"] == "circle" and s["y"] == -893.0 for s in finding["offscreen"]["samples"])

    def test_line_within_bounds_not_flagged(self):
        assert detect_svg(_svg(body='<line x1="0" y1="50" x2="10" y2="60"/>')) is None

    def test_circle_within_bounds_not_flagged(self):
        assert detect_svg(_svg(body='<circle cx="5" cy="50" r="2"/>')) is None


# ---------------------------------------------------------------------------
# detect_svg -- 15% margin + shape of the finding dict
# ---------------------------------------------------------------------------

class TestDetectSvgMarginAndShape:
    def test_just_within_margin_not_flagged(self):
        # viewBox 0..100 -> lo=-15. y=-14 stays inside the 15% tolerance.
        assert detect_svg(_svg(body=_offscreen_rect(y=-14.0))) is None

    def test_just_past_margin_flagged(self):
        # y=-16 crosses the -15 bound (strict inequality).
        finding = detect_svg(_svg(body=_offscreen_rect(y=-16.0)))
        assert finding is not None

    def test_finding_shape(self):
        finding = detect_svg(_svg(body=_offscreen_rect()))
        assert finding is not None
        assert finding["viewBox_min_y"] == 0.0
        assert finding["viewBox_height"] == 100.0
        assert finding["bounds"] == [-15.0, 115.0]  # round(lo,1), round(hi,1)
        assert "count" in finding["offscreen"]
        assert "samples" in finding["offscreen"]

    def test_text_excluded_from_geometry_check(self):
        # <text> labels may legitimately fringe the border; not data geometry.
        body = '<text x="0" y="-893">rotated label</text>'
        assert detect_svg(_svg(body=body)) is None

    def test_samples_capped_at_five(self):
        # 7 offscreen rects -> count=7, samples truncated to 5.
        body = "".join(_offscreen_rect(y=-100.0 - i * 10) for i in range(7))
        finding = detect_svg(_svg(body=body))
        assert finding is not None
        assert finding["offscreen"]["count"] == 7
        assert len(finding["offscreen"]["samples"]) == 5


# ---------------------------------------------------------------------------
# detect_cell -- MIME routing + aggregation
# ---------------------------------------------------------------------------

class TestDetectCell:
    def test_flags_svg_xml_mime(self):
        cell = _code_cell([_svg_output(_svg(body=_offscreen_rect()))])
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["output_index"] == 0
        assert findings[0]["mime"] == "image/svg+xml"
        assert findings[0]["svg_chars"] > 0

    def test_flags_text_html_mime(self):
        cell = _code_cell([_svg_output(_svg(body=_offscreen_rect()), mime="text/html")])
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["mime"] == "text/html"

    def test_ignores_non_svg_mime(self):
        cell = _code_cell([{"data": {"text/plain": "no chart here"}, "output_type": "display_data"}])
        assert detect_cell(cell) == []

    def test_clean_svg_not_flagged(self):
        cell = _code_cell([_svg_output(_svg(body='<rect x="0" y="50" width="10" height="10"/>'))])
        assert detect_cell(cell) == []

    def test_multiple_outputs_indexed(self):
        # output[0] clean, output[1] offscreen -> finding carries output_index 1.
        cell = _code_cell([
            _svg_output(_svg(body='<rect x="0" y="50" width="10" height="10"/>')),
            _svg_output(_svg(body=_offscreen_rect())),
        ])
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["output_index"] == 1

    def test_markdown_cell_no_outputs(self):
        assert detect_cell({"cell_type": "markdown", "source": ["# hi"], "outputs": []}) == []


# ---------------------------------------------------------------------------
# scan_notebook (filesystem)
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_clean_notebook_no_hits(self, tmp_path):
        p = _write_nb(tmp_path / "clean.ipynb",
                      [_code_cell([_svg_output(_svg(body='<rect x="0" y="50" width="10" height="10"/>'))])])
        result = scan_notebook(p)
        assert result["error"] is None
        assert result["hits"] == []
        assert result["kernel"] == ".net-csharp"

    def test_offscreen_notebook_hit_indexed_by_cell(self, tmp_path):
        cells = [
            {"cell_type": "markdown", "source": ["# title"], "outputs": []},
            _code_cell([_svg_output(_svg(body=_offscreen_rect()))]),
        ]
        p = _write_nb(tmp_path / "broken.ipynb", cells)
        result = scan_notebook(p)
        assert result["error"] is None
        assert len(result["hits"]) == 1
        assert result["hits"][0]["cell_index"] == 1  # markdown cell skipped

    def test_unreadable_notebook_error(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("{ not json", encoding="utf-8")
        result = scan_notebook(p)
        assert result["error"] is not None
        assert result["hits"] == []


# ---------------------------------------------------------------------------
# _should_skip
# ---------------------------------------------------------------------------

class TestShouldSkip:
    def test_skips_output_notebook_suffix(self):
        assert _should_skip(Path("Sudoku", "foo_output.ipynb")) is True

    def test_skips_known_dir(self):
        assert _should_skip(Path(".lake", "packages", "x.ipynb")) is True
        assert _should_skip(Path("foundry-lib", "lib", "y.ipynb")) is True

    def test_passes_normal_notebook(self):
        assert _should_skip(Path("Sudoku", "SW-2-CSharp.ipynb")) is False


# ---------------------------------------------------------------------------
# main() exit codes
# ---------------------------------------------------------------------------

class TestMainExitCodes:
    def test_check_clean_exit_0(self, tmp_path):
        p = _write_nb(tmp_path / "clean.ipynb",
                      [_code_cell([_svg_output(_svg(body='<rect x="0" y="50" width="10" height="10"/>'))])])
        assert main([str(p), "--check"]) == 0

    def test_check_broken_exit_1(self, tmp_path):
        p = _write_nb(tmp_path / "broken.ipynb",
                      [_code_cell([_svg_output(_svg(body=_offscreen_rect()))])])
        assert main([str(p), "--check"]) == 1

    def test_broken_without_check_exit_0(self, tmp_path):
        # Without --check, exit 0 even when defects are present (report-only).
        p = _write_nb(tmp_path / "broken.ipynb",
                      [_code_cell([_svg_output(_svg(body=_offscreen_rect()))])])
        assert main([str(p)]) == 0

    def test_missing_notebook_exit_2(self, tmp_path):
        assert main([str(tmp_path / "nope.ipynb")]) == 2

    def test_json_mode(self, tmp_path, capsys):
        p = _write_nb(tmp_path / "broken.ipynb",
                      [_code_cell([_svg_output(_svg(body=_offscreen_rect()))])])
        rc = main([str(p), "--json"])
        payload = json.loads(capsys.readouterr().out)
        assert payload["total_hits"] == 1
        assert payload["notebooks_scanned"] == 1
        assert rc == 0  # without --check, exit 0

    def test_family_not_found_exit_2(self, tmp_path):
        assert main(["--family", "NonexistentFamilyXYZ", "--root", str(tmp_path)]) == 2
