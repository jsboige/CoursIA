"""Tests for check_figure_rendering.py — figure outputs the reader will
never see (#26690, demand 2; founding case PR #26613).

Pins the three-finding contract and its deliberate silences: a healthy SVG
served as text/html is invisible on the GitHub renderer (SVG_IN_HTML), a
drawing-less or unclosed SVG renders blank (BROKEN_SVG), a PNG decoding
under the floor is mechanically empty (TINY_PNG) -- while a healthy SVG
under its own mime, a substantial PNG, a rich HTML table carrying a small
decorative SVG icon, and text-only outputs all stay silent. Diff bounding:
only cells added, source-changed or output-changed since base are judged.
No network, no kernel.
"""
import base64
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_figure_rendering import (analyze, analyze_diff, run,
                                    DOMINANCE_FRACTION)

HEALTHY_SVG = (
    "<svg xmlns='http://www.w3.org/2000/svg' width='10' height='10'>"
    "<rect width='10' height='10' fill='white'/>"
    "<path d='M 0 0 L 10 10' stroke='black'/></svg>"
)
EMPTY_SVG = (
    "<svg xmlns='http://www.w3.org/2000/svg' width='10' height='10'>"
    "</svg>"
)


def out(data):
    return {"output_type": "display_data", "data": data}


def code_cell(outputs):
    return {"cell_type": "code", "source": ["x=1"], "outputs": outputs}


def nb(cells):
    return {"cells": list(cells)}


def kinds(findings):
    return sorted(f["kind"] for f in findings)


def test_founding_case_svg_in_html():
    # The .NET SvgMarkup formatter registers "text/html": renders locally,
    # sanitised away by the GitHub notebook renderer.
    got = analyze(nb([code_cell([out({"text/html": [HEALTHY_SVG]})])]))
    assert kinds(got) == ["SVG_IN_HTML"]


def test_svg_own_mime_is_silent():
    got = analyze(nb([code_cell([out({"image/svg+xml": [HEALTHY_SVG]})])]))
    assert got == []


def test_svg_without_drawing_element_is_broken():
    got = analyze(nb([code_cell([out({"image/svg+xml": [EMPTY_SVG]})])]))
    assert kinds(got) == ["BROKEN_SVG"]


def test_unclosed_svg_in_html_is_broken():
    got = analyze(nb([code_cell([out({"text/html": HEALTHY_SVG[:30]})])]))
    assert kinds(got) == ["BROKEN_SVG"]


def test_decoration_in_rich_html_is_not_dominant():
    html = ("<table><tr><td>mesured results table</td></tr></table>"
            + HEALTHY_SVG)
    got = analyze(nb([code_cell([out({"text/html": html})])]))
    assert got == []


def test_substantial_png_is_silent():
    b64 = base64.b64encode(b"x" * 5000).decode()
    got = analyze(nb([code_cell([out({"image/png": b64})])]))
    assert got == []


def test_tiny_png_is_flagged():
    b64 = base64.b64encode(b"\x89PNG\r\n\x1a\n" + b"x" * 40).decode()
    got = analyze(nb([code_cell([out({"image/png": b64})])]))
    assert kinds(got) == ["TINY_PNG"]


def test_stream_output_is_silent():
    got = analyze(nb([code_cell([{"output_type": "stream",
                                  "name": "stdout", "text": ["ok"]}])]))
    assert got == []


def test_diff_bounding_skips_unchanged_and_judges_added():
    base = nb([code_cell([out({"text/html": [HEALTHY_SVG]})]),
               code_cell([out({"image/png": base64.b64encode(b"y" * 5000).decode()})])])
    same = nb([code_cell([out({"text/html": [HEALTHY_SVG]})]),
               code_cell([out({"image/png": base64.b64encode(b"y" * 5000).decode()})])])
    assert analyze_diff(base, same) == []
    grown = nb([code_cell([out({"text/html": [HEALTHY_SVG]})]),
                code_cell([out({"text/html": [HEALTHY_SVG]})])])
    got = analyze_diff(base, grown)
    assert [(f["cell"], f["kind"]) for f in got] == [(1, "SVG_IN_HTML")]


def test_run_census_counts_by_kind(tmp_path):
    p = tmp_path / "n.ipynb"
    p.write_text(__import__("json").dumps(
        nb([code_cell([out({"text/html": [HEALTHY_SVG]})]),
            code_cell([out({"image/svg+xml": [EMPTY_SVG]})])])), encoding="utf-8")
    report = run([p.name], cwd=tmp_path)
    assert report["counts"] == {"BROKEN_SVG": 1, "SVG_IN_HTML": 1}
    assert report["total"] == 2
    assert report["base"] is None


def test_dominance_fraction_is_strict_minority():
    # The threshold itself must stay well under a half: a figure sharing its
    # output with substantial HTML is not "a figure hidden in HTML".
    assert DOMINANCE_FRACTION <= 0.25
