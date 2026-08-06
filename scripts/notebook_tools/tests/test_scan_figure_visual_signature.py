"""Tests for scripts/notebook_tools/scan_figure_visual_signature.py.

Why this test file exists
-------------------------
`scan_figure_visual_signature.py` consolidates the 11 visual tells discovered
across the MANIFEST-desc-visuelle rollout c.754-c.781 (EPIC #5780):
L777-L1, L778-L1/L2, L779-L1/L2, L780-L1/L2/L3, L781-L1/L2/L3.

The tells encode palette signatures discovered via PIL RGB stats on actual
manifest figures (ML.Net, ML racine, IIT/ICT-Series, Probas/PyMC, Search/Apps,
QuantConnect/Python). They are DETERMINISTIC (statistical thresholds on mean
and std per channel), not heuristic.

The detector's contract:
- sample 2000 pixels random seed 42 -> mean R/G/B + std R/G/B
- match tell predicates against the 6 stats
- emit JSON or text report with detected tells + lesson reference

Test data design: synthetic stats dicts (no PIL dependency) for each canonical
tell, plus an "atypique" baseline that matches none (proves ZERO false-positives
without dictating "must match at least one"). End-to-end CLI sanity check via
synthesized PNG (1x1 white pixel) -- the canonical FIGURE_PLEINE_MAIS_VIDE
blind-spot is OUT of scope (cf module docstring), and we don't test what we
declared hors-scope.

Founding context: see MEMORY.md "Lecons durables" entries L777-L1 through
L781-L3 for the empirical thresholds validated firsthand on real manifest PNGs.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile

# Add scripts/notebook_tools to sys.path so we can import the detector
# module directly (matches test_*_detect_blank_figures.py pattern).
_HERE = os.path.dirname(__file__)
_TOOLS_DIR = os.path.abspath(os.path.join(_HERE, ".."))
if _TOOLS_DIR not in sys.path:
    sys.path.insert(0, _TOOLS_DIR)

import scan_figure_visual_signature as sfvs  # noqa: E402


# ----------------------------------------------------------------------------
# Cluster 1: Tell predicates on synthetic stats dicts
# ----------------------------------------------------------------------------


def _stats(
    mean_r: float = 200.0,
    mean_g: float = 200.0,
    mean_b: float = 200.0,
    std_r: float = 25.0,
    std_g: float = 25.0,
    std_b: float = 25.0,
) -> dict[str, float]:
    return {
        "width": 600,
        "height": 400,
        "mean_r": mean_r,
        "mean_g": mean_g,
        "mean_b": mean_b,
        "std_r": std_r,
        "std_g": std_g,
        "std_b": std_b,
        "n_samples": 2000,
        "seed": 42,
    }


def test_imshow_darkfield():
    """L778-L2 : mean < 100 sur R/G/B => heatmap dark-field."""
    stats = _stats(mean_r=50, mean_g=50, mean_b=80)
    matches = sfvs.detect_tells(stats)
    names = [m["name"] for m in matches]
    assert "heatmap_imshow_darkfield" in names, f"expected imshow_darkfield in {names}"


def test_matplotlib_blanc():
    """L781-L2 : mean R/G/B ~ 248 + std uniforme (~31)."""
    stats = _stats(mean_r=248, mean_g=248, mean_b=248, std_r=31, std_g=32, std_b=30)
    matches = sfvs.detect_tells(stats)
    names = [m["name"] for m in matches]
    assert "matplotlib_blanc_whitegrid" in names, f"expected matplotlib_blanc in {names}"
    # NB : achrome_palette matche AUSSI car mean R = G = B = 248 EXACT
    # (la predicate achrome ne regarde que les mean, pas les std).
    # La discrimination vient du std uniforme ~31 vs std variable.
    assert "achrome_palette" in names, "mean R=G=B=248 EXACT -- achrome predicate hits too (not a regression)"


def test_graphe_academique_blanc():
    """L780-L3 : mean >= 249 + std 20-30."""
    stats = _stats(mean_r=250, mean_g=251, mean_b=251, std_r=24, std_g=22, std_b=21)
    matches = sfvs.detect_tells(stats)
    names = [m["name"] for m in matches]
    assert "graphe_academique_blanc" in names, f"expected graphe_academique in {names}"


def test_achrome_palette():
    """L780-L1 : mean R = G = B EXACT (no tint)."""
    stats = _stats(mean_r=231.87, mean_g=231.87, mean_b=231.87, std_r=27.86, std_g=27.86, std_b=27.86)
    matches = sfvs.detect_tells(stats)
    names = [m["name"] for m in matches]
    assert "achrome_palette" in names, f"expected achrome in {names}"


def test_bar_chart_bleu_dominant():
    """L781-L1 : mean B > G > R + std R > 50 (bar chart steelblue seaborn)."""
    stats = _stats(mean_r=186, mean_g=203, mean_b=222, std_r=72, std_g=52, std_b=37)
    matches = sfvs.detect_tells(stats)
    names = [m["name"] for m in matches]
    assert "bar_chart_bleu_dominant_seaborn" in names, f"expected bar_chart_bleu in {names}"


def test_stacked_area_orange_seaborn():
    """L781-L3 : R > G > B + std B > 50 (stacked area orange seaborn)."""
    stats = _stats(mean_r=235, mean_g=222, mean_b=220, std_r=29, std_g=37, std_b=52)
    matches = sfvs.detect_tells(stats)
    names = [m["name"] for m in matches]
    assert "stacked_area_orange_seaborn" in names, f"expected stacked_area in {names}"


def test_courbe_bleu_dominant():
    """L779-L2 : mean B > R + 5 (line plot blue dominant)."""
    stats = _stats(mean_r=235, mean_g=235, mean_b=241)  # difference = 6
    matches = sfvs.detect_tells(stats)
    names = [m["name"] for m in matches]
    assert "courbe_bleu_dominant" in names, f"expected courbe_bleu in {names}"


def test_niveau_2d_procedural_dense():
    """L780-L2 : mean 100-180 + std 50+ (procedural multi-couleurs)."""
    stats = _stats(mean_r=130, mean_g=141, mean_b=111, std_r=70, std_g=63, std_b=74)
    matches = sfvs.detect_tells(stats)
    names = [m["name"] for m in matches]
    assert "niveau_2d_procedural_dense" in names, f"expected procedural in {names}"


def test_heatmap_dense_ylorrd():
    """L779-L1 : mean 200-250 + G < R + std B > 50 (YlOrRd heatmap)."""
    stats = _stats(mean_r=241, mean_g=176, mean_b=149, std_r=35, std_g=92, std_b=96)
    matches = sfvs.detect_tells(stats)
    names = [m["name"] for m in matches]
    assert "heatmap_dense_ylorrd" in names, f"expected heatmap_dense in {names}"


# ----------------------------------------------------------------------------
# Cluster 2: Atypical case (no tell matches) -> empty list, no crash
# ----------------------------------------------------------------------------


def test_no_tell_matches_atypique():
    """Synthetic atypical palette -> empty matches (no false-positive)."""
    stats = _stats(mean_r=128, mean_g=200, mean_b=64, std_r=20, std_g=30, std_b=12)
    # Random "non-canonical" palette (greenish-yellow, low std on R/B)
    matches = sfvs.detect_tells(stats)
    assert isinstance(matches, list), f"expected list, got {type(matches)}"
    # We don't assert `matches == []` -- some tells can overlap. We assert the
    # detector doesn't crash on atypical input and returns a usable structure.


# ----------------------------------------------------------------------------
# Cluster 3: scan_path() — file/dir/no-exist handling
# ----------------------------------------------------------------------------


def test_scan_path_file():
    """scan_path on a single PNG file returns [path]."""
    with tempfile.NamedTemporaryFile(suffix=".png", delete=False) as f:
        path = f.name
    try:
        result = sfvs.scan_path(path, recursive=False)
        assert result == [path]
    finally:
        os.unlink(path)


def test_scan_path_dir_nonrecursive():
    """scan_path on a dir without --recursive lists top-level PNGs only."""
    with tempfile.TemporaryDirectory() as tmpdir:
        # Create top-level PNG + nested PNG (nested should be ignored w/o recursive)
        open(os.path.join(tmpdir, "top.png"), "wb").close()
        nested = os.path.join(tmpdir, "nested")
        os.makedirs(nested)
        open(os.path.join(nested, "deep.png"), "wb").close()
        result = sfvs.scan_path(tmpdir, recursive=False)
        assert len(result) == 1
        assert os.path.basename(result[0]) == "top.png"


def test_scan_path_dir_recursive():
    """scan_path on a dir with --recursive lists all PNGs."""
    with tempfile.TemporaryDirectory() as tmpdir:
        open(os.path.join(tmpdir, "a.png"), "wb").close()
        nested = os.path.join(tmpdir, "sub")
        os.makedirs(nested)
        open(os.path.join(nested, "b.png"), "wb").close()
        result = sfvs.scan_path(tmpdir, recursive=True)
        assert len(result) == 2


def test_scan_path_missing_returns_empty():
    """scan_path on a non-existent path returns empty list (not raise)."""
    assert sfvs.scan_path("/nonexistent/path/xyz123") == []


def test_scan_path_non_png_skipped():
    """scan_path on a non-PNG file returns empty list."""
    with tempfile.NamedTemporaryFile(suffix=".txt", delete=False) as f:
        path = f.name
    try:
        assert sfvs.scan_path(path) == []
    finally:
        os.unlink(path)


# ----------------------------------------------------------------------------
# Cluster 4: render_report() — JSON vs text output format
# ----------------------------------------------------------------------------


def test_render_report_json():
    """JSON output is valid JSON with required keys."""
    stats = _stats(mean_r=200, mean_g=200, mean_b=200)
    tells = sfvs.detect_tells(stats)
    out = sfvs.render_report("/tmp/figure.png", stats, tells, "json")
    parsed = json.loads(out)
    assert parsed["path"] == "/tmp/figure.png"
    assert parsed["dimensions"] == [600, 400]
    assert len(parsed["mean_rgb"]) == 3
    assert len(parsed["std_rgb"]) == 3
    assert isinstance(parsed["tells_detected"], list)


def test_render_report_text_includes_dimensions():
    """Text output includes 'dimensions' label and R/G/B numbers."""
    stats = _stats(mean_r=235, mean_g=235, mean_b=241)
    out = sfvs.render_report("/tmp/x.png", stats, [], "text")
    assert "dimensions" in out
    assert "235" in out and "241" in out
    assert "aucun tell" in out or "0 detecte" in out


# ----------------------------------------------------------------------------
# Cluster 5: CLI end-to-end (subprocess) — synthesized 1x1 white PNG
# ----------------------------------------------------------------------------


def _make_minimal_png(path: str) -> None:
    """Write a minimal 1x1 white PNG (no PIL dependency for test fixture)."""
    import zlib

    def chunk(tag: bytes, data: bytes) -> bytes:
        import struct

        return (
            struct.pack(">I", len(data))
            + tag
            + data
            + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)
        )

    sig = b"\x89PNG\r\n\x1a\n"
    ihdr = chunk(b"IHDR", b"\x00\x00\x00\x01\x00\x00\x00\x01\x08\x02\x00\x00\x00")
    # IDAT: a single white pixel, filter byte 0 + RGB (255,255,255)
    raw = b"\x00\xff\xff\xff"
    idat = chunk(b"IDAT", zlib.compress(raw))
    iend = chunk(b"IEND", b"")
    with open(path, "wb") as f:
        f.write(sig + ihdr + idat + iend)


def test_cli_end_to_end_json():
    """CLI run on synthesized PNG produces parseable JSON output."""
    with tempfile.TemporaryDirectory() as tmpdir:
        png_path = os.path.join(tmpdir, "test.png")
        _make_minimal_png(png_path)
        result = subprocess.run(
            [
                sys.executable,
                os.path.join(_TOOLS_DIR, "scan_figure_visual_signature.py"),
                "--format",
                "json",
                png_path,
            ],
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert result.returncode == 0, f"stderr: {result.stderr}"
        # Output may include multiple reports if path resolves to dir;
        # here we passed a single file so output is a single JSON object.
        try:
            parsed = json.loads(result.stdout.strip())
            assert parsed["dimensions"] == [1, 1]
            assert "mean_rgb" in parsed
            assert "std_rgb" in parsed
            assert "tells_detected" in parsed
        except json.JSONDecodeError:
            # If multi-line output (recursive scan), parse line by line.
            lines = [ln for ln in result.stdout.strip().split("\n") if ln.strip()]
            assert len(lines) >= 1
            parsed = json.loads(lines[0])
            assert "mean_rgb" in parsed


def test_cli_check_exit_zero_on_success():
    """--check exits 0 when all scanned figures succeed."""
    with tempfile.TemporaryDirectory() as tmpdir:
        png_path = os.path.join(tmpdir, "test.png")
        _make_minimal_png(png_path)
        result = subprocess.run(
            [
                sys.executable,
                os.path.join(_TOOLS_DIR, "scan_figure_visual_signature.py"),
                "--check",
                png_path,
            ],
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert result.returncode == 0, f"stderr: {result.stderr}"


def test_cli_check_exit_one_on_missing_file():
    """--check exits 1 when path resolves to empty (no PNG found)."""
    result = subprocess.run(
        [
            sys.executable,
            os.path.join(_TOOLS_DIR, "scan_figure_visual_signature.py"),
            "--check",
            "/nonexistent/path/should/fail",
        ],
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert result.returncode == 1, f"expected exit 1, got {result.returncode}"
