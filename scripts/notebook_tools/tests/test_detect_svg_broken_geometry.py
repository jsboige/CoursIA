"""Tests for scripts/notebook_tools/detect_svg_broken_geometry.py -- SVG element
with a NEGATIVE width/height (invisible element, broken render) detector.

Tests focus on the pure helpers (_extract_svgs, _negative_dims), the core
detect_svg contract (negative-dimension detection, sample cap, finding shape),
detect_cell MIME routing, scan_notebook filesystem + error handling,
_should_skip filtering, and the main() exit codes. Uses synthetic SVG
fragments and tmp_path for isolation.

See #7008 (gate MERGED, detector live), EPIC #3801 (SOTA axe-2), See #6927.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_svg_broken_geometry import (  # noqa: E402
    _extract_svgs,
    _negative_dims,
    _should_skip,
    detect_cell,
    detect_svg,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _svg(body: str = "") -> str:
    return f"<svg>{body}</svg>"


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
        out = _extract_svgs("<svg><rect/></svg>text<svg></svg>")
        assert len(out) == 2

    def test_list_payload_is_joined(self):
        out = _extract_svgs(["<svg>", "<rect/></svg>"])
        assert len(out) == 1

    def test_non_string_payload_returns_empty(self):
        assert _extract_svgs(None) == []
        assert _extract_svgs(42) == []


# ---------------------------------------------------------------------------
# _negative_dims (the regex)
# ---------------------------------------------------------------------------

class TestNegativeDims:
    def test_negative_width_flagged(self):
        dims = _negative_dims('<rect width="-893" height="10"/>')
        assert dims == [{"attr": "width", "value": "-893"}]

    def test_negative_height_flagged(self):
        dims = _negative_dims('<rect width="10" height="-66"/>')
        assert dims == [{"attr": "height", "value": "-66"}]

    def test_single_quote_form(self):
        # The regex accepts single quotes (backreference closes the same quote).
        dims = _negative_dims("<rect width='-893'/>")
        assert dims == [{"attr": "width", "value": "-893"}]

    def test_positive_dimensions_not_flagged(self):
        # width/height >= 0 are legitimate (0 is not negative).
        assert _negative_dims('<rect width="100" height="0"/>') == []

    def test_negative_zero_flagged(self):
        # "-0" still matches the -[\d.]+ pattern -> recorded (edge of the regex).
        dims = _negative_dims('<rect width="-0"/>')
        assert dims == [{"attr": "width", "value": "-0"}]

    def test_decimal_negative_flagged(self):
        dims = _negative_dims('<rect width="-1.5"/>')
        assert dims == [{"attr": "width", "value": "-1.5"}]

    def test_multiple_dims_collected(self):
        svg = '<rect width="-893"/><rect height="-66"/><image width="-10"/>'
        dims = _negative_dims(svg)
        assert len(dims) == 3
        assert {d["attr"] for d in dims} == {"width", "height"}

    def test_coordinates_not_confused_with_dimensions(self):
        # x/y/cx/cy negative are NOT flagged here (only width/height).
        assert _negative_dims('<rect x="-100" y="-200" width="10" height="10"/>') == []


# ---------------------------------------------------------------------------
# detect_svg -- finding shape + sample cap
# ---------------------------------------------------------------------------

class TestDetectSvg:
    def test_none_for_clean_svg(self):
        assert detect_svg(_svg('<rect width="100" height="50"/>')) is None

    def test_none_for_empty_svg(self):
        assert detect_svg("<svg></svg>") is None

    def test_finding_shape(self):
        finding = detect_svg(_svg('<rect width="-893"/>'))
        assert finding is not None
        assert finding["negative_dims"]["count"] == 1
        assert finding["negative_dims"]["samples"][0] == {"attr": "width", "value": "-893"}

    def test_samples_capped_at_five(self):
        # 7 negative-dim elements -> count=7, samples truncated to 5.
        body = "".join(f'<rect width="-{i}"/>' for i in range(10, 80, 10))  # 7 rects
        finding = detect_svg(_svg(body))
        assert finding is not None
        assert finding["negative_dims"]["count"] == 7
        assert len(finding["negative_dims"]["samples"]) == 5


# ---------------------------------------------------------------------------
# detect_cell -- MIME routing + aggregation
# ---------------------------------------------------------------------------

class TestDetectCell:
    def test_flags_svg_xml_mime(self):
        cell = _code_cell([_svg_output(_svg('<rect width="-893"/>'))])
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["output_index"] == 0
        assert findings[0]["mime"] == "image/svg+xml"
        assert findings[0]["svg_chars"] > 0

    def test_flags_text_html_mime(self):
        cell = _code_cell([_svg_output(_svg('<rect width="-893"/>'), mime="text/html")])
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["mime"] == "text/html"

    def test_ignores_non_svg_mime(self):
        cell = _code_cell([{"data": {"text/plain": "no chart"}, "output_type": "display_data"}])
        assert detect_cell(cell) == []

    def test_clean_svg_not_flagged(self):
        cell = _code_cell([_svg_output(_svg('<rect width="100" height="50"/>'))])
        assert detect_cell(cell) == []

    def test_multiple_outputs_indexed(self):
        cell = _code_cell([
            _svg_output(_svg('<rect width="100"/>')),
            _svg_output(_svg('<rect width="-893"/>')),
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
                      [_code_cell([_svg_output(_svg('<rect width="100" height="50"/>'))])])
        result = scan_notebook(p)
        assert result["error"] is None
        assert result["hits"] == []
        assert result["kernel"] == ".net-csharp"

    def test_broken_notebook_hit_indexed_by_cell(self, tmp_path):
        cells = [
            {"cell_type": "markdown", "source": ["# title"], "outputs": []},
            _code_cell([_svg_output(_svg('<rect width="-893"/>'))]),
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
                      [_code_cell([_svg_output(_svg('<rect width="100" height="50"/>'))])])
        assert main([str(p), "--check"]) == 0

    def test_check_broken_exit_1(self, tmp_path):
        p = _write_nb(tmp_path / "broken.ipynb",
                      [_code_cell([_svg_output(_svg('<rect width="-893"/>'))])])
        assert main([str(p), "--check"]) == 1

    def test_broken_without_check_exit_0(self, tmp_path):
        p = _write_nb(tmp_path / "broken.ipynb",
                      [_code_cell([_svg_output(_svg('<rect width="-893"/>'))])])
        assert main([str(p)]) == 0

    def test_missing_notebook_exit_2(self, tmp_path):
        assert main([str(tmp_path / "nope.ipynb")]) == 2

    def test_json_mode(self, tmp_path, capsys):
        p = _write_nb(tmp_path / "broken.ipynb",
                      [_code_cell([_svg_output(_svg('<rect width="-893"/>'))])])
        rc = main([str(p), "--json"])
        payload = json.loads(capsys.readouterr().out)
        assert payload["total_hits"] == 1
        assert payload["notebooks_scanned"] == 1
        assert rc == 0

    def test_family_not_found_exit_2(self, tmp_path):
        assert main(["--family", "NonexistentFamilyXYZ", "--root", str(tmp_path)]) == 2
