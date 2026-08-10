"""Tests for scripts/notebook_tools/detect_blank_figures.py — degenerate PNG figure detector.

Why this test file exists
-------------------------
`detect_blank_figures.py` (registre #3801, Prong-A sweep, axe-2 SOTA) is the
canonical DETECTOR for fabricated PNG figures in pedagogical notebooks -- the
"matplotlib emitted an empty figure and we shipped it as if it were a real plot"
class. The detector is deterministic on dimensions + decoded payload size, NOT
heuristic (the gap between 70-byte 1x1 PNGs and 41-236 KB real matplotlib plots
is several orders of magnitude).

Founding incident #6891 (8 quantbook.ipynb files, each carrying a single 70-byte
1x1 PNG instead of a real figure) makes this a high-ROI gate. The sibling
detector `detect_ascii_workaround.py` covers the ASCII half of the Prong-A
sweep; this file covers the IMAGE half.

Seven clusters mirroring the detector's documented decision logic:

  1. TestConstants            -- MIN_DIM, MIN_BYTES, _PNG_SIGNATURE, _IMAGE_MIMES defaults
  2. TestDecodeImage          -- base64 payload decoding (str/list/None/invalid)
  3. TestPngDimensions        -- IHDR parsing (signature check, length check, success)
  4. TestClassifyImage        -- degenerate detection (dim too small / bytes too small / both)
  5. TestDetectCell           -- code-cell iteration over image mimes, output_index
  6. TestScanNotebook         -- end-to-end dict contract, kernel extraction, error handling
  7. TestMainExitCodes        -- CLI: --check / --json / missing-notebook / family-not-found

Test data design: every PNG sample below is a synthesized minimal PNG (using
`zlib` + `struct`) -- the canonical 1x1, the 8x8 boundary case, the 100x100
legitimate case. Each test isolates one conjunct of the decision so a regression
in any conjunct surfaces as a single failure.
"""
import base64
import json
import struct
import sys
import zlib
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_blank_figures import (  # noqa: E402
    MIN_BYTES,
    MIN_DIM,
    MIN_DISTINCT_COLORS,
    SKIP_DIRS,
    _OUTPUT_SUFFIX,
    _PNG_SIGNATURE,
    _classify_image,
    _decode_image,
    _flattened_pixels,
    _has_real_content,
    detect_cell,
    _human_report,
    _iter_notebooks,
    _kernel,
    _png_dimensions,
    _should_skip,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers — synthesized PNG samples (the canonical fixture class)
# ---------------------------------------------------------------------------

def _make_png(width: int, height: int, pixel: bytes = b"\xff\x00\x00") -> bytes:
    """Synthesize a minimal valid PNG of given dimensions.

    Produces a non-transparent, fully-colored image (default pixel = opaque red)
    so the dimensions IHDR + decoded size match what the detector reads.
    """
    def chunk(chunk_type: bytes, data: bytes) -> bytes:
        return (
            struct.pack(">I", len(data))
            + chunk_type
            + data
            + struct.pack(">I", zlib.crc32(chunk_type + data) & 0xFFFFFFFF)
        )

    sig = b"\x89PNG\r\n\x1a\n"
    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)  # 8-bit RGB
    raw = b"".join(b"\x00" + pixel * width for _ in range(height))
    idat = zlib.compress(raw, level=9)
    return sig + chunk(b"IHDR", ihdr) + chunk(b"IDAT", idat) + chunk(b"IEND", b"")


def _b64_png(width: int, height: int, pixel: bytes = b"\xff\x00\x00") -> str:
    return base64.b64encode(_make_png(width, height, pixel)).decode("ascii")


# Canonical fixtures (sizes chosen so the detector classifies them as expected):
PNG_1x1_B64 = _b64_png(1, 1)            # 69 bytes, (1,1) -> DEGENERATE
PNG_8x8_B64 = _b64_png(8, 8)            # ~75 bytes, (8,8) -> DEGENERATE (8 <= 8)
PNG_100x100_B64 = _b64_png(100, 100)    # ~334 bytes, (100,100) -> still tiny (< 1024)


def _make_noisy_png(width: int, height: int) -> bytes:
    """Make a PNG with HIGH entropy so zlib compression cannot collapse it.

    Real matplotlib figures have noisy gradients/text/axes that resist compression;
    a uniformly-colored PNG compresses to ~1/3 the size. We need at least 1024
    bytes of decoded output to satisfy MIN_BYTES for a "legitimate" fixture.
    """
    import hashlib
    raw = b""
    for row in range(height):
        # Pseudo-random noise per row (deterministic but incompressible)
        row_seed = hashlib.sha256(f"{row}".encode()).digest()
        line = b"\x00" + (row_seed * ((width * 3) // len(row_seed) + 1))[: width * 3]
        raw += line

    def chunk(chunk_type: bytes, data: bytes) -> bytes:
        return (
            struct.pack(">I", len(data))
            + chunk_type
            + data
            + struct.pack(">I", zlib.crc32(chunk_type + data) & 0xFFFFFFFF)
        )

    sig = b"\x89PNG\r\n\x1a\n"
    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)
    idat = zlib.compress(raw, level=1)  # low compression = preserves size
    return sig + chunk(b"IHDR", ihdr) + chunk(b"IDAT", idat) + chunk(b"IEND", b"")


# A 50x50 noisy PNG: ~7.5 KB decoded > MIN_BYTES=1024, dim > MIN_DIM=8 -> CLEAN
PNG_LARGE_B64 = base64.b64encode(_make_noisy_png(50, 50)).decode("ascii")


def _make_multicolor_png(width: int, height: int, palette: list[bytes]) -> bytes:
    """Synthesize a small PNG with several DISTINCT colors (pixel-art / grid).

    Used to exercise the content-gate escape hatch (#8634): such an image is
    small in bytes but carries real content, so it must NOT be flagged. Rows are
    painted round-robin from `palette` (>= MIN_DISTINCT_COLORS colors) so the
    decoded image is genuinely multicolor.
    """
    assert len(palette) >= MIN_DISTINCT_COLORS, "palette must carry real content"

    def chunk(chunk_type: bytes, data: bytes) -> bytes:
        return (
            struct.pack(">I", len(data))
            + chunk_type
            + data
            + struct.pack(">I", zlib.crc32(chunk_type + data) & 0xFFFFFFFF)
        )

    sig = b"\x89PNG\r\n\x1a\n"
    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)  # 8-bit RGB
    rows = []
    for row in range(height):
        pixel = palette[row % len(palette)]
        rows.append(b"\x00" + pixel * width)
    raw = b"".join(rows)
    idat = zlib.compress(raw, level=9)
    return sig + chunk(b"IHDR", ihdr) + chunk(b"IDAT", idat) + chunk(b"IEND", b"")


# A 24x16 pixel-art grid with 6 distinct colors (the 04-4 cross-stitch shape,
# #8632/#8634): small canvas, real content -> CLEAN via the content gate.
_PALETTE_6 = [bytes(c) for c in [(51, 131, 98), (153, 207, 217), (253, 215, 85),
                                  (44, 106, 69), (200, 50, 30), (120, 80, 160)]]
PNG_PIXELART_B64 = base64.b64encode(_make_multicolor_png(24, 16, _PALETTE_6)).decode("ascii")


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": source}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": source}


def _nb(cells: list[dict]) -> dict:
    """Minimal nbformat-4 notebook."""
    return {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "python3", "display_name": "Python 3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _code_cell_with_png(b64_png: str, mime: str = "image/png") -> dict:
    """Build a code cell with an image/png output."""
    return {
        "cell_type": "code",
        "source": "# some code that emitted an image",
        "metadata": {},
        "outputs": [
            {
                "output_type": "display_data",
                "data": {mime: b64_png},
                "metadata": {},
            }
        ],
        "execution_count": 1,
    }


def _write_nb(path: Path, cells: list[dict], kernel: str = "python3") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel, "display_name": kernel}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# 1. Constants — the documented defaults (calibrated on QC #6891)
# ---------------------------------------------------------------------------

class TestConstants:
    def test_min_dim_is_8_px(self):
        # 8 px is the documented threshold (cf #6891: 1x1 matplotlib empty)
        assert MIN_DIM == 8

    def test_min_bytes_is_1_kb(self):
        # 1024 bytes separates 70-byte empty PNGs from legitimate 41-236 KB plots
        assert MIN_BYTES == 1024

    def test_png_signature_is_canonical(self):
        # 8-byte magic number per the PNG spec
        assert _PNG_SIGNATURE == b"\x89PNG\r\n\x1a\n"

    def test_image_mimes_include_png_and_jpeg(self):
        from detect_blank_figures import _IMAGE_MIMES
        assert "image/png" in _IMAGE_MIMES
        assert "image/jpeg" in _IMAGE_MIMES

    def test_output_suffix_for_papermill_artifacts(self):
        # _output.ipynb is the papermill re-execution artifact; we skip it
        assert _OUTPUT_SUFFIX == "_output.ipynb"

    def test_skip_dirs_includes_vendored_and_caches(self):
        # SKIP_DIRS covers vendored libs (.lake, foundry-lib) and cache dirs
        for d in (".lake", ".git", "__pycache__", "_archives", ".pytest_cache", "foundry-lib"):
            assert d in SKIP_DIRS, f"missing skip-dir: {d}"


# ---------------------------------------------------------------------------
# 2. _decode_image — base64 payload decoding
# ---------------------------------------------------------------------------

class TestDecodeImage:
    def test_decode_string_payload(self):
        raw = _make_png(1, 1)
        b64 = base64.b64encode(raw).decode("ascii")
        decoded = _decode_image(b64)
        assert decoded == raw

    def test_decode_list_of_string_chunks(self):
        # nbformat source-as-list pattern: image payloads may be list[str] (joined)
        raw = _make_png(1, 1)
        b64_full = base64.b64encode(raw).decode("ascii")
        # Split into 4 chunks of roughly equal length
        n = len(b64_full) // 4
        chunks = [b64_full[:n], b64_full[n:2*n], b64_full[2*n:3*n], b64_full[3*n:]]
        decoded = _decode_image(chunks)
        assert decoded == raw

    def test_invalid_base64_returns_none(self):
        assert _decode_image("not_valid_base64@@@") is None

    def test_non_string_non_list_returns_none(self):
        assert _decode_image(42) is None
        assert _decode_image({"data": "abc"}) is None
        assert _decode_image(None) is None

    def test_empty_string_returns_empty_bytes(self):
        # Empty b64 decodes to empty bytes (which is then tiny_payload)
        assert _decode_image("") == b""


# ---------------------------------------------------------------------------
# 3. _png_dimensions — IHDR parsing
# ---------------------------------------------------------------------------

class TestPngDimensions:
    def test_canonical_1x1(self):
        raw = _make_png(1, 1)
        assert _png_dimensions(raw) == (1, 1)

    def test_canonical_100x50(self):
        raw = _make_png(100, 50)
        assert _png_dimensions(raw) == (100, 50)

    def test_invalid_signature_returns_none(self):
        # Strip the PNG signature
        raw = _make_png(10, 10)[8:]
        assert _png_dimensions(raw) is None

    def test_truncated_too_short_returns_none(self):
        # Must be at least 24 bytes (signature + IHDR chunk header + width + height)
        raw = _make_png(10, 10)[:16]
        assert _png_dimensions(raw) is None

    def test_missing_ihdr_returns_none(self):
        # Valid signature but IHDR replaced by another chunk type
        raw = bytearray(_make_png(10, 10))
        raw[12:16] = b"XXXX"
        assert _png_dimensions(bytes(raw)) is None

    def test_non_png_data_returns_none(self):
        # Pure JPEG / random bytes don't parse as PNG
        assert _png_dimensions(b"\xff\xd8\xff\xe0" + b"\x00" * 50) is None


# ---------------------------------------------------------------------------
# 4. _classify_image — degenerate detection (the core decision)
# ---------------------------------------------------------------------------

class TestClassifyImage:
    def test_1x1_png_degenerate(self):
        # The founding case: 1x1 PNG = both signals (dim + tiny_payload)
        raw = _make_png(1, 1)
        result = _classify_image("image/png", raw, MIN_DIM, MIN_BYTES)
        assert result is not None
        assert result["mime"] == "image/png"
        assert result["dimensions"] == [1, 1]
        assert "degenerate_dimensions(1x1)" in result["reasons"]
        assert any("tiny_payload" in r for r in result["reasons"])

    def test_8x8_png_at_boundary(self):
        # 8x8 = MIN_DIM boundary: w <= 8 is degenerate (inclusive)
        raw = _make_png(8, 8)
        result = _classify_image("image/png", raw, MIN_DIM, MIN_BYTES)
        assert result is not None
        assert "degenerate_dimensions(8x8)" in result["reasons"]

    def test_9x9_png_no_dim_degeneration(self):
        # 9x9 > MIN_DIM: dimension signal clear, but bytes may still be tiny
        raw = _make_png(9, 9)
        result = _classify_image("image/png", raw, MIN_DIM, MIN_BYTES)
        # 9x9 OK on dims (no degenerate_dimensions), but still tiny bytes
        if result is not None:
            assert "degenerate_dimensions" not in " ".join(result["reasons"])

    def test_tiny_payload_no_dim_degeneration(self):
        # An image where dimensions are OK but bytes are below threshold
        # (e.g. a near-empty JPEG with valid dimensions that we can't parse)
        result = _classify_image("image/jpeg", b"\xff\xd8" + b"\x00" * 50, MIN_DIM, MIN_BYTES)
        # JPEG: dims=None, but bytes (52) < 1024 -> tiny_payload reason
        assert result is not None
        assert "tiny_payload" in result["reasons"][0]
        assert result["dimensions"] is None

    def test_legitimate_large_png_clean(self):
        # 50x50 noisy PNG = ~7.5 KB > MIN_BYTES and > MIN_DIM -> CLEAN
        raw = _make_noisy_png(50, 50)
        # Sanity: dimensions 50x50, bytes >= 1024
        assert len(raw) >= MIN_BYTES
        result = _classify_image("image/png", raw, MIN_DIM, MIN_BYTES)
        assert result is None  # legitimate: no finding

    def test_custom_min_dim_threshold(self):
        # A 12x12 PNG with min_dim=20 = degenerate by custom threshold
        raw = _make_png(12, 12)
        result = _classify_image("image/png", raw, min_dim=20, min_bytes=MIN_BYTES)
        assert result is not None
        assert any("degenerate_dimensions(12x12)" in r for r in result["reasons"])

    def test_custom_min_bytes_threshold(self):
        # 200x200 PNG with min_bytes=2000 = below custom threshold = degenerate
        raw = _make_png(200, 200, pixel=b"\x80\x80\x80")
        result = _classify_image("image/png", raw, min_dim=MIN_DIM, min_bytes=2000)
        if result is not None:
            assert any("tiny_payload" in r for r in result["reasons"])

    def test_classify_returns_dict_with_consistent_keys(self):
        # All findings have the same shape (for json/dashboard consumers)
        raw = _make_png(1, 1)
        result = _classify_image("image/png", raw, MIN_DIM, MIN_BYTES)
        assert result is not None
        for key in ("mime", "bytes", "dimensions", "reasons"):
            assert key in result
        assert isinstance(result["reasons"], list)


# ---------------------------------------------------------------------------
# 5. detect_cell — code-cell iteration, output_index preservation
# ---------------------------------------------------------------------------

class TestDetectCell:
    def test_code_cell_with_degenerate_png_returns_finding(self):
        cell = _code_cell_with_png(PNG_1x1_B64)
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["output_index"] == 0
        assert findings[0]["mime"] == "image/png"

    def test_code_cell_with_legitimate_png_no_findings(self):
        cell = _code_cell_with_png(PNG_LARGE_B64)
        findings = detect_cell(cell)
        assert findings == []

    def test_code_cell_with_no_outputs_no_findings(self):
        cell = {"cell_type": "code", "source": "x = 1", "outputs": [], "execution_count": 1}
        assert detect_cell(cell) == []

    def test_code_cell_with_none_outputs_no_findings(self):
        # Defensive: outputs may be None
        cell = {"cell_type": "code", "source": "x = 1", "outputs": None}
        assert detect_cell(cell) == []

    def test_code_cell_with_multiple_outputs_indexed(self):
        # Two PNG outputs in one cell: one degenerate, one legitimate
        cell = {
            "cell_type": "code",
            "source": "plt.show()",
            "outputs": [
                {"output_type": "display_data", "data": {"image/png": PNG_1x1_B64}, "metadata": {}},
                {"output_type": "display_data", "data": {"image/png": PNG_LARGE_B64}, "metadata": {}},
            ],
            "execution_count": 1,
        }
        findings = detect_cell(cell)
        assert len(findings) == 1
        assert findings[0]["output_index"] == 0  # only the degenerate one

    def test_code_cell_with_jpeg(self):
        # JPEG: pass a valid base64 string of a small JPEG payload
        jpeg_bytes = b"\xff\xd8\xff\xe0" + b"\x00" * 50
        jpeg_b64 = base64.b64encode(jpeg_bytes).decode("ascii")
        cell = _code_cell_with_png(jpeg_b64, mime="image/jpeg")
        findings = detect_cell(cell)
        # JPEG: dims=None, but tiny bytes (54) -> degenerate on tiny_payload only
        assert len(findings) == 1
        assert findings[0]["mime"] == "image/jpeg"
        assert findings[0]["dimensions"] is None
        assert "tiny_payload" in findings[0]["reasons"][0]

    def test_code_cell_with_non_image_mime_ignored(self):
        # A text/html output should NOT be scanned as an image
        cell = {
            "cell_type": "code",
            "source": "print('hi')",
            "outputs": [
                {"output_type": "display_data", "data": {"text/html": "<div>hello</div>"}, "metadata": {}},
            ],
            "execution_count": 1,
        }
        assert detect_cell(cell) == []

    def test_custom_thresholds_passed_through(self):
        # Custom min_dim=4 should catch a 5x5 PNG that defaults miss
        cell = _code_cell_with_png(_b64_png(5, 5))
        # Default: 5 > 8? No, 5 <= 8 -> caught at default
        findings_default = detect_cell(cell)
        assert len(findings_default) == 1
        # With min_dim=20: still caught (5 < 20)
        findings_custom = detect_cell(cell, min_dim=20)
        assert len(findings_custom) == 1


# ---------------------------------------------------------------------------
# 6. scan_notebook — end-to-end dict contract
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_clean_notebook_returns_empty_hits(self, tmp_path):
        nb_path = _write_nb(tmp_path / "clean.ipynb", [_code("x = 1")])
        result = scan_notebook(nb_path)
        assert result["hits"] == []
        assert result["error"] is None
        assert "path" in result

    def test_notebook_with_degenerate_cell_returns_hit(self, tmp_path):
        nb_path = _write_nb(
            tmp_path / "degenerate.ipynb",
            [_code("import matplotlib"), _code_cell_with_png(PNG_1x1_B64)],
        )
        result = scan_notebook(nb_path)
        assert len(result["hits"]) == 1
        assert result["hits"][0]["cell_index"] == 1  # second cell
        assert result["hits"][0]["mime"] == "image/png"

    def test_kernel_extracted_from_metadata(self, tmp_path):
        nb_path = _write_nb(tmp_path / "kernel.ipynb", [_code("x")], kernel=".net-csharp")
        result = scan_notebook(nb_path)
        assert result["kernel"] == ".net-csharp"

    def test_unknown_kernel_defaults_to_question_mark(self, tmp_path):
        nb_path = tmp_path / "no-kernel.ipynb"
        # Build a notebook without kernelspec metadata
        nb = {"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        result = scan_notebook(nb_path)
        assert result["kernel"] == "?"

    def test_unreadable_file_returns_error_in_result(self, tmp_path):
        # Path that doesn't exist
        result = scan_notebook(tmp_path / "does_not_exist.ipynb")
        assert result["error"] is not None
        assert result["hits"] == []

    def test_malformed_json_returns_error_in_result(self, tmp_path):
        nb_path = tmp_path / "broken.ipynb"
        nb_path.write_text("{this is not valid json", encoding="utf-8")
        result = scan_notebook(nb_path)
        assert result["error"] is not None
        assert result["hits"] == []

    def test_markdown_cells_skipped(self, tmp_path):
        # Even with degenerate content, markdown cells are NOT scanned
        cells = [_md("# Title\n" + PNG_1x1_B64)]
        nb_path = _write_nb(tmp_path / "md.ipynb", cells)
        result = scan_notebook(nb_path)
        assert result["hits"] == []

    def test_multiple_degenerate_cells_collected(self, tmp_path):
        # Three code cells with degenerate figures, two with legitimate ones
        # PNG_LARGE_B64 is the noisy 50x50 PNG (~7.5 KB > MIN_BYTES)
        cells = [
            _code_cell_with_png(PNG_1x1_B64),       # degenerate (1x1 + tiny)
            _code_cell_with_png(PNG_LARGE_B64),     # legitimate (50x50 noisy)
            _code_cell_with_png(PNG_8x8_B64),       # degenerate (8x8 at boundary)
            _code_cell_with_png(PNG_LARGE_B64),     # legitimate
            _code_cell_with_png(PNG_1x1_B64),       # degenerate (1x1)
        ]
        nb_path = _write_nb(tmp_path / "multi.ipynb", cells)
        result = scan_notebook(nb_path)
        assert len(result["hits"]) == 3
        assert {h["cell_index"] for h in result["hits"]} == {0, 2, 4}

    def test_default_thresholds_apply(self, tmp_path):
        # 100x100 PNG is below MIN_BYTES (1024) even though dims are > MIN_DIM
        # -> degenerate on tiny_payload only
        nb_path = _write_nb(tmp_path / "100.ipynb", [_code_cell_with_png(PNG_100x100_B64)])
        result = scan_notebook(nb_path)
        assert len(result["hits"]) == 1
        assert "degenerate_dimensions" not in " ".join(result["hits"][0]["reasons"])
        assert any("tiny_payload" in r for r in result["hits"][0]["reasons"])


# ---------------------------------------------------------------------------
# 7. _kernel and _should_skip — internal helpers
# ---------------------------------------------------------------------------

class TestHelpers:
    def test_kernel_extracts_name(self):
        nb = {"metadata": {"kernelspec": {"name": "python3"}}}
        assert _kernel(nb) == "python3"

    def test_kernel_missing_metadata_returns_question_mark(self):
        assert _kernel({}) == "?"
        assert _kernel({"metadata": {}}) == "?"

    def test_should_skip_vendored_dirs(self):
        # SKIP_DIRS members anywhere in the path = skip
        for d in SKIP_DIRS:
            rel = Path(f"MyIA.AI.Notebooks/foo/{d}/bar.ipynb")
            assert _should_skip(rel), f"should skip {rel}"

    def test_should_skip_output_artifact(self):
        # _output.ipynb is the papermill re-execution artifact (not the source)
        rel = Path("MyIA.AI.Notebooks/QuantConnect/some_output.ipynb")
        assert _should_skip(rel)

    def test_should_keep_regular_notebook(self):
        rel = Path("MyIA.AI.Notebooks/QuantConnect/research.ipynb")
        assert not _should_skip(rel)


# ---------------------------------------------------------------------------
# 8. _iter_notebooks and _human_report — scan orchestration + reporting
# ---------------------------------------------------------------------------

class TestIterNotebooks:
    def test_iter_with_family(self, tmp_path):
        # Build a fake MyIA.AI.Notebooks/QuantConnect tree
        root = tmp_path
        qc = root / "MyIA.AI.Notebooks" / "QuantConnect"
        qc.mkdir(parents=True)
        (qc / "alpha.ipynb").write_text("{}", encoding="utf-8")
        (qc / "beta.ipynb").write_text("{}", encoding="utf-8")

        notebooks = list(_iter_notebooks(root, family="QuantConnect"))
        assert len(notebooks) == 2
        names = {nb.name for nb in notebooks}
        assert names == {"alpha.ipynb", "beta.ipynb"}

    def test_iter_skips_output_artifact(self, tmp_path):
        root = tmp_path
        qc = root / "MyIA.AI.Notebooks" / "QuantConnect"
        qc.mkdir(parents=True)
        (qc / "alpha.ipynb").write_text("{}", encoding="utf-8")
        (qc / "alpha_output.ipynb").write_text("{}", encoding="utf-8")

        notebooks = list(_iter_notebooks(root, family="QuantConnect"))
        assert len(notebooks) == 1
        assert notebooks[0].name == "alpha.ipynb"

    def test_iter_skips_vendored_dirs(self, tmp_path):
        root = tmp_path
        qc = root / "MyIA.AI.Notebooks" / "QuantConnect"
        qc.mkdir(parents=True)
        (qc / ".lake").mkdir()
        (qc / ".lake" / "cached.ipynb").write_text("{}", encoding="utf-8")
        (qc / "real.ipynb").write_text("{}", encoding="utf-8")

        notebooks = list(_iter_notebooks(root, family="QuantConnect"))
        names = {nb.name for nb in notebooks}
        assert "real.ipynb" in names
        assert "cached.ipynb" not in names


class TestHumanReport:
    def test_empty_results_reports_no_degenerates(self):
        report = _human_report([])
        assert "Degenerate figures : 0" in report
        assert "No degenerate figures detected" in report

    def test_results_with_hits_report_each_finding(self, tmp_path):
        nb_path = _write_nb(
            tmp_path / "sample.ipynb",
            [_code_cell_with_png(PNG_1x1_B64)],
            kernel="python3",
        )
        result = scan_notebook(nb_path)
        report = _human_report([result])
        assert "Degenerate figures : 1" in report
        assert "Affected notebooks : 1" in report
        assert "sample.ipynb" in report
        assert "python3" in report
        # #10319: the prescription prefix is now ``FIX (degenerate):`` -- it
        # distinguishes the blocking degenerate-FIX from the non-blocking
        # sparse-grid advisory section added by the per-tile detector.
        assert "FIX (degenerate):" in report  # the Stop&Repair prescription

    def test_errored_results_included(self, tmp_path):
        # Build a malformed notebook
        nb_path = tmp_path / "bad.ipynb"
        nb_path.write_text("{invalid", encoding="utf-8")
        result = scan_notebook(nb_path)
        report = _human_report([result])
        assert "0" in report  # no hits
        assert "unreadable" in report.lower()


# ---------------------------------------------------------------------------
# 9. main() — CLI exit codes
# ---------------------------------------------------------------------------

class TestMainExitCodes:
    def test_missing_notebook_exits_2(self, tmp_path, capsys):
        nb_path = tmp_path / "missing.ipynb"
        rc = main([str(nb_path)])
        assert rc == 2
        captured = capsys.readouterr()
        assert "not found" in captured.err.lower()

    def test_check_mode_exits_1_on_degenerate(self, tmp_path, capsys):
        nb_path = _write_nb(tmp_path / "bad.ipynb", [_code_cell_with_png(PNG_1x1_B64)])
        rc = main([str(nb_path), "--check"])
        assert rc == 1

    def test_no_check_mode_exits_0_even_with_degenerate(self, tmp_path, capsys):
        nb_path = _write_nb(tmp_path / "bad.ipynb", [_code_cell_with_png(PNG_1x1_B64)])
        rc = main([str(nb_path)])  # no --check
        assert rc == 0  # by design: only --check exits 1

    def test_clean_run_exits_0(self, tmp_path, capsys):
        nb_path = _write_nb(tmp_path / "clean.ipynb", [_code_cell_with_png(PNG_LARGE_B64)])
        rc = main([str(nb_path), "--check"])
        assert rc == 0

    def test_json_output_is_valid_json(self, tmp_path, capsys):
        nb_path = _write_nb(tmp_path / "test.ipynb", [_code_cell_with_png(PNG_1x1_B64)])
        rc = main([str(nb_path), "--json"])
        assert rc == 0
        captured = capsys.readouterr()
        parsed = json.loads(captured.out)
        assert "notebooks_scanned" in parsed
        assert "total_hits" in parsed
        assert parsed["total_hits"] == 1

    def test_custom_thresholds_passed_through(self, tmp_path, capsys):
        # Post-content-gate (#8634): a noisy/rich PNG is no longer flagged on
        # size alone (it carries real content). To still demonstrate that
        # --min-bytes propagates, use a MONOCHROME PNG (1 color, so
        # _has_real_content=False -> not exempt) whose only signal is tiny_payload.
        # Threshold below its byte count -> clean; above -> degenerate.
        raw = _make_png(100, 100, pixel=b"\x80\x80\x80")  # ~334 B, monochrome, 100x100 (dim OK)
        size = len(raw)
        mono_b64 = base64.b64encode(raw).decode("ascii")
        nb_path = _write_nb(tmp_path / "test.ipynb", [_code_cell_with_png(mono_b64)])
        assert main([str(nb_path), "--check", "--min-bytes", str(size - 1)]) == 0
        assert main([str(nb_path), "--check", "--min-bytes", str(size + 1)]) == 1

    def test_invalid_family_exits_2(self, tmp_path, capsys):
        rc = main(["--family", "NonExistentFamily", "--root", str(tmp_path)])
        assert rc == 2
        captured = capsys.readouterr()
        assert "family not found" in captured.err.lower()


# ---------------------------------------------------------------------------
# 10. Content gate (#8634) -- escape hatch for small but rich images
# ---------------------------------------------------------------------------
# The founding #6891 incident was about EMPTY figures (1x1, 70 B). The size
# threshold (MIN_BYTES) caught them. But size measures RESOLUTION, not CONTENT:
# pixel-art, cross-stitch grids, sprites, mini heatmaps are small in bytes yet
# carry real visual content. The content gate adds a content-based escape: a
# small image is exempted from tiny_payload iff it decodes and carries >=
# MIN_DISTINCT_COLORS distinct colors. Indecodable images (PIL absent / corrupt)
# fall back to the size signal -- no coverage regression.

class TestContentGate:
    def test_min_distinct_colors_is_4(self):
        # Calibrated so a 1-color canvas is caught but a 4-color pixel-art is freed
        assert MIN_DISTINCT_COLORS == 4

    def test_has_real_content_true_for_multicolor(self):
        # A 24x16 grid with 6 colors carries real content
        assert _has_real_content(_make_multicolor_png(24, 16, _PALETTE_6)) is True

    def test_has_real_content_false_for_monochrome(self):
        # A single-color image (canvas blanc) carries no real content
        assert _has_real_content(_make_png(50, 50, pixel=b"\xff\xff\xff")) is False

    def test_has_real_content_none_for_non_image_bytes(self):
        # Random/corrupt bytes cannot be decoded -> None (fall back to size)
        assert _has_real_content(b"\x00" * 50) is None
        assert _has_real_content(b"") is None

    def test_has_real_content_respects_custom_threshold(self):
        # With min_colors higher than the palette size, a 6-color image is "poor"
        assert _has_real_content(_make_multicolor_png(24, 16, _PALETTE_6), min_colors=10) is False

    def test_pixelart_not_flagged_on_tiny_payload(self):
        # THE #8634 case: a small (24x16, <1024 B) but rich image is CLEAN
        raw = _make_multicolor_png(24, 16, _PALETTE_6)
        assert len(raw) < MIN_BYTES  # sanity: it IS under the size threshold
        assert _classify_image("image/png", raw, MIN_DIM, MIN_BYTES) is None

    def test_monochrome_small_still_flagged(self):
        # #6891 must NOT regress: a small monochrome (canvas blanc) stays flagged
        raw = _make_png(50, 50, pixel=b"\xff\xff\xff")  # 50x50 white, ~150 B, 1 color
        assert len(raw) < MIN_BYTES
        result = _classify_image("image/png", raw, MIN_DIM, MIN_BYTES)
        assert result is not None
        assert any("tiny_payload" in r for r in result["reasons"])

    def test_1x1_still_flagged_via_min_dim(self):
        # The true 1x1 placeholder is caught by degenerate_dimensions regardless
        raw = _make_png(1, 1)
        result = _classify_image("image/png", raw, MIN_DIM, MIN_BYTES)
        assert result is not None
        assert "degenerate_dimensions(1x1)" in result["reasons"]

    def test_indecodable_small_falls_back_to_size(self):
        # A corrupt "JPEG" under MIN_BYTES: _has_real_content=None -> size signal
        result = _classify_image("image/jpeg", b"\xff\xd8" + b"\x00" * 50, MIN_DIM, MIN_BYTES)
        assert result is not None
        assert any("tiny_payload" in r for r in result["reasons"])

    def test_scan_notebook_frees_pixelart(self, tmp_path):
        # End-to-end: a notebook whose only figure is rich pixel-art scans clean
        nb_path = _write_nb(tmp_path / "pixelart.ipynb", [_code_cell_with_png(PNG_PIXELART_B64)])
        result = scan_notebook(nb_path)
        assert result["hits"] == []

    def test_scan_notebook_still_catches_monochrome(self, tmp_path):
        # End-to-end: a monochrome small figure is still caught (#6891 preserved)
        mono_b64 = base64.b64encode(_make_png(50, 50, pixel=b"\xff\xff\xff")).decode("ascii")
        nb_path = _write_nb(tmp_path / "mono.ipynb", [_code_cell_with_png(mono_b64)])
        result = scan_notebook(nb_path)
        assert len(result["hits"]) == 1


class TestContentGateSurvivesDeprecation:
    """The content gate must not revert to size-only because of a Pillow warning.

    `_has_real_content` swallows every exception into `None`, and `None` means
    "fall back to the size rule" -- the very rule #8634 was filed against. So any
    call that can *raise* on the nominal path silently undoes #8637. Pillow 12
    deprecated `Image.getdata()` and removes it in Pillow 14 (2027-10-15): under
    a warnings-as-errors run the deprecation raises, is swallowed, and the
    pixel-art of #8634 is flagged again -- with no error and no failing test.

    These tests pin the nominal path as warning-free, so the regression surfaces
    here rather than in a scan verdict two years from now.
    """

    def test_content_gate_is_warning_free(self):
        # The happy path must not emit ANY warning: one turned into an error by
        # `-W error` would be swallowed into None and silently disable the gate.
        import warnings

        raw = base64.b64decode(PNG_PIXELART_B64)
        with warnings.catch_warnings():
            warnings.simplefilter("error")
            assert _has_real_content(raw) is True

    def test_pixelart_stays_free_under_warnings_as_errors(self):
        # End-to-end guard: this is what regresses on Pillow 14 if the deprecated
        # API is called -- the pixel-art gets flagged tiny_payload again.
        import warnings

        raw = base64.b64decode(PNG_PIXELART_B64)
        with warnings.catch_warnings():
            warnings.simplefilter("error")
            assert _classify_image("image/png", raw, MIN_DIM, MIN_BYTES) is None

    def test_uses_supported_pillow_api_when_available(self):
        # Prefer get_flattened_data(); fall back to getdata() on older Pillow.
        pytest.importorskip("PIL")
        from PIL import Image

        im = Image.new("RGB", (2, 2))
        im.putdata([(0, 0, 0), (1, 1, 1), (2, 2, 2), (3, 3, 3)])
        if hasattr(im, "get_flattened_data"):
            assert list(_flattened_pixels(im)) == list(im.get_flattened_data())
        else:  # Pillow < 12: the legacy name is the only one available
            assert len(list(_flattened_pixels(im))) == 4


# ---------------------------------------------------------------------------
# 11. Gate workflow contract (#8884) -- the environment the detector RUNS in
# ---------------------------------------------------------------------------
# Every test above exercises the detector as a library, in THIS job's
# environment -- where Pillow is present transitively (scripts-tests.yml installs
# matplotlib, which depends on Pillow). The GATE runs in a different job with its
# own environment, and that is the gap #8884 fell through: the unit tests stayed
# green while `degenerate-figure-gate.yml` had no `pip install` at all, so PIL was
# missing, `_has_real_content` returned None, the #8634 content escape hatch was
# inoperative, and the 24x16 cross-stitch grid was flagged again -- in CI only,
# invisible from here.
#
# These two assertions are the ratchet. They are deliberately assertions about
# the WORKFLOW FILE, not about the detector: a unit test cannot observe another
# job's interpreter. Dropping the Pillow install, or reverting the loop to the
# errexit-unsafe form, turns this file red instead of silently disarming the gate.

_GATE_WORKFLOW = (
    Path(__file__).resolve().parents[3] / ".github" / "workflows" / "degenerate-figure-gate.yml"
)


class TestGateWorkflowContract:
    def test_gate_workflow_exists(self):
        assert _GATE_WORKFLOW.is_file(), f"gate workflow missing: {_GATE_WORKFLOW}"

    def test_gate_installs_pillow_explicitly(self):
        # PIL is REQUIRED for the #8634 content gate, not optional. Relying on a
        # transitive matplotlib dependency (as scripts-tests.yml does) is exactly
        # the asymmetry that hid #8884.
        text = _GATE_WORKFLOW.read_text(encoding="utf-8")
        assert "pip install" in text and "Pillow" in text, (
            "degenerate-figure-gate.yml must install Pillow explicitly; without it "
            "_has_real_content() degrades to None and the #8634 escape hatch is dead"
        )

    def test_detector_invocation_is_errexit_safe(self):
        # The step runs under `bash -e`: a bare `out=$(cmd)` that exits non-zero
        # aborts before `rc=$?` is read, making the rc=1/rc=2 branches dead code
        # and the failure anonymous. `&& rc=0 || rc=$?` preserves the real code.
        text = _GATE_WORKFLOW.read_text(encoding="utf-8")
        invocation = [
            ln for ln in text.splitlines()
            if "detect_blank_figures.py" in ln and "out=$(" in ln
        ]
        assert invocation, "expected an `out=$(... detect_blank_figures.py ...)` invocation"
        line = invocation[0]
        assert "&& rc=0 || rc=$?" in line, (
            f"errexit-unsafe detector invocation: {line.strip()!r} -- use "
            "`out=$(...) && rc=0 || rc=$?` so rc survives `bash -e`"
        )
        # `|| true` would make $? read 0 from `true` itself: rc always 0, so the
        # gate could never fire at all -- strictly worse than the original bug.
        assert "|| true" not in line, (
            "`|| true` makes rc always 0 and permanently disarms the gate; "
            "use `&& rc=0 || rc=$?`"
        )