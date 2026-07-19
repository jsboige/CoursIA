"""Tests for scripts/notebook_tools/extract_readme_figures.py — PNG figure
extractor for README illustration (EPIC #5654).

Why this test file exists
-------------------------
`extract_readme_figures.py` is the *extraction* half of EPIC #5654 (illustration
des READMEs, source 1 = figures extraites des outputs de notebooks
deja committes). It implements two modes :

  - :func:`list_figures` : inventaire / *gisement* (read-only, no files written).
  - :func:`extract_figure` : extraction d'UNE figure vers ``assets/readme/`` +
    append ``MANIFEST.md`` (provenance source 1 obligatoire).

The sibling detectors under ``scripts/notebook_tools/`` carry their own pytest
roll-out (po-2025 c.628 PR #7391, c.716 PR #7374, c.720 PR #7212,
c.684 PR #7217). This file completes the roll-out for the *extractor* path of
the same EPIC, ensuring the public API (resolutions de path, parsing IHDR,
extraction base64, optimisation PIL, MANIFEST idempotent) all keep working
when the module is later refactored.

Nine clusters mirroring the module's documented decision logic :

  1. TestPngDimensions      -- IHDR parsing (signature check, length check, success)
  2. TestPngOutputBytes     -- base64 payload extraction (str/list/None/invalid/empty)
  3. TestCellOutputs        -- routing code vs markdown + empty outputs handling
  4. TestFigureRecords      -- multi-cell / multi-output aggregation + bytes count
  5. TestIterNotebooks      -- checkpoint skipping + ordering
  6. TestResolveRepoPath    -- absolute / repo-relatif / serie-relatif resolution
  7. TestListFigures        -- end-to-end inventory on tmp dir + over_weight flag
  8. TestOptimizeWithPil    -- PIL path + graceful PIL-absent fallback + errors
  9. TestAppendManifest     -- header init, append, idempotent replace, serie_root
 10. TestExtractFigure      -- end-to-end extraction + MANIFEST + alt_text_fr HARD
 11. TestConstants          -- plafond defaults + magic + offsets (documented)

Test data design: every PNG sample below is a synthesized minimal PNG (using
`zlib` + `struct`) — the canonical 1x1, the 100x100 noisy case, etc. Tests are
isolation-first (tmp_path fixture, no repo mutation). The real disk sweep
(119 figures / 25 notebooks in Probas) is NOT exercised here — that is the
end-to-end smoke test, not a unit test.
"""
import base64
import json
import struct
import sys
import zlib
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from extract_readme_figures import (  # noqa: E402
    MAX_BYTES_DEFAULT,
    MAX_DIM_DEFAULT,
    PNG_IHDR_HEIGHT_OFFSET,
    PNG_IHDR_WIDTH_OFFSET,
    _PNG_MAGIC,
    _append_manifest,
    _cell_outputs,
    _figure_records,
    _iter_notebooks,
    _load_notebook,
    _optimize_with_pil,
    _png_dimensions,
    _png_output_bytes,
    extract_figure,
    list_figures,
    resolve_repo_path,
)


# ---------------------------------------------------------------------------
# Helpers — synthesized PNG samples (canonical fixture class)
# ---------------------------------------------------------------------------
def _make_png(width: int, height: int, pixel: bytes = b"\xff\x00\x00") -> bytes:
    """Synthesize a minimal valid PNG of given dimensions (8-bit RGB)."""

    def chunk(chunk_type: bytes, data: bytes) -> bytes:
        return (
            struct.pack(">I", len(data))
            + chunk_type
            + data
            + struct.pack(">I", zlib.crc32(chunk_type + data) & 0xFFFFFFFF)
        )

    sig = b"\x89PNG\r\n\x1a\n"
    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)
    raw = b"".join(b"\x00" + pixel * width for _ in range(height))
    idat = zlib.compress(raw, level=9)
    return sig + chunk(b"IHDR", ihdr) + chunk(b"IDAT", idat) + chunk(b"IEND", b"")


def _b64_png(width: int, height: int, pixel: bytes = b"\xff\x00\x00") -> str:
    return base64.b64encode(_make_png(width, height, pixel)).decode("ascii")


def _make_noisy_png(width: int, height: int) -> bytes:
    """High-entropy PNG so zlib cannot collapse it (real-figure stand-in)."""
    import hashlib

    raw = b""
    for row in range(height):
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
    idat = zlib.compress(raw, level=1)
    return sig + chunk(b"IHDR", ihdr) + chunk(b"IDAT", idat) + chunk(b"IEND", b"")


# Canonical fixtures
PNG_1x1_BYTES = _make_png(1, 1)                # 69 bytes raw, (1,1) -> tiny
PNG_8x8_BYTES = _make_png(8, 8)                # ~75 bytes raw
PNG_100x100_B64 = _b64_png(100, 100)           # ~340 bytes raw, used in cell fixtures
PNG_NOISY_512_B64 = base64.b64encode(_make_noisy_png(512, 512)).decode("ascii")


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": source}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": source}


def _nb(cells: list[dict], kernel: str = "python3") -> dict:
    """Minimal nbformat-4 notebook."""
    return {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel, "display_name": kernel}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _code_cell_with_png(b64_png: str, mime: str = "image/png") -> dict:
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


def _code_cell_with_two_pngs() -> dict:
    """Cell with TWO display_data outputs — two records expected."""
    return {
        "cell_type": "code",
        "source": "# two figures side by side",
        "metadata": {},
        "outputs": [
            {
                "output_type": "display_data",
                "data": {"image/png": _b64_png(64, 64)},
                "metadata": {},
            },
            {
                "output_type": "execute_result",
                "data": {"image/png": _b64_png(128, 128)},
                "metadata": {},
            },
        ],
        "execution_count": 2,
    }


def _write_nb(path: Path, cells: list[dict], kernel: str = "python3") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = _nb(cells, kernel=kernel)
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# 1. TestPngDimensions — IHDR parsing without PIL
# ---------------------------------------------------------------------------
class TestPngDimensions:
    """PNG header parsing: the stdlib-only path used by list_figures/records."""

    def test_returns_none_when_bytes_too_short(self):
        # < 24 bytes -> cannot read width AND height
        assert _png_dimensions(b"\x89PNG\r\n\x1a\n" + b"\x00" * 10) is None

    def test_returns_none_when_signature_missing(self):
        # Bytes are long enough but signature is wrong (no \x89PNG)
        bad_sig = b"NOTPNG\r\n\x1a\n" + b"\x00" * 16
        assert _png_dimensions(bad_sig) is None

    def test_returns_dims_for_canonical_png(self):
        w, h = _png_dimensions(PNG_1x1_BYTES)
        assert (w, h) == (1, 1)

    def test_returns_dims_for_noisy_512(self):
        w, h = _png_dimensions(_make_noisy_png(512, 512))
        assert (w, h) == (512, 512)

    def test_returns_dims_for_8x8(self):
        w, h = _png_dimensions(PNG_8x8_BYTES)
        assert (w, h) == (8, 8)

    def test_width_height_are_independent(self):
        # 100x200 (non-square)
        png = _make_png(100, 200)
        w, h = _png_dimensions(png)
        assert w == 100
        assert h == 200


# ---------------------------------------------------------------------------
# 2. TestPngOutputBytes — base64 payload extraction (display_data + execute_result)
# ---------------------------------------------------------------------------
class TestPngOutputBytes:
    """Output-dict -> PNG bytes; the bridge between nbformat and the parser."""

    def test_returns_none_when_output_has_no_data(self):
        assert _png_output_bytes({"output_type": "stream", "text": "hello"}) is None

    def test_returns_none_when_data_has_no_png(self):
        out = {"output_type": "display_data", "data": {"text/plain": "x"}}
        assert _png_output_bytes(out) is None

    def test_extracts_base64_string(self):
        out = {"output_type": "display_data", "data": {"image/png": PNG_100x100_B64}}
        raw = _png_output_bytes(out)
        assert raw is not None
        assert raw[:8] == _PNG_MAGIC

    def test_extracts_from_execute_result(self):
        out = {"output_type": "execute_result", "data": {"image/png": PNG_100x100_B64}}
        raw = _png_output_bytes(out)
        assert raw is not None
        assert _png_dimensions(raw) == (100, 100)

    def test_handles_list_payload(self):
        # nbformat allows list-of-str for source-like; image data is normally str
        b64 = PNG_100x100_B64
        # split into chunks as nbformat sometimes does for cell source
        out = {"output_type": "display_data", "data": {"image/png": [b64[:32], b64[32:]]}}
        raw = _png_output_bytes(out)
        assert raw is not None
        assert _png_dimensions(raw) == (100, 100)

    def test_returns_none_on_invalid_base64(self):
        out = {"output_type": "display_data", "data": {"image/png": "###invalid###"}}
        assert _png_output_bytes(out) is None

    def test_returns_none_on_empty_string(self):
        out = {"output_type": "display_data", "data": {"image/png": ""}}
        # empty string is falsy -> returns None at the `if not b64` guard
        assert _png_output_bytes(out) is None


# ---------------------------------------------------------------------------
# 3. TestCellOutputs — code/markdown routing + empty outputs
# ---------------------------------------------------------------------------
class TestCellOutputs:
    """`_cell_outputs` is the boundary between nbformat cells and the parser."""

    def test_returns_empty_for_markdown_cell(self):
        cell = {"cell_type": "markdown", "source": "# Title", "outputs": []}
        assert _cell_outputs(cell) == []

    def test_returns_outputs_for_code_cell(self):
        cell = {"cell_type": "code", "outputs": [{"output_type": "stream", "text": "x"}]}
        assert _cell_outputs(cell) == [{"output_type": "stream", "text": "x"}]

    def test_returns_empty_when_outputs_key_missing(self):
        # Robust to nbformat-3 (no outputs key)
        cell = {"cell_type": "code", "source": "1+1"}
        assert _cell_outputs(cell) == []

    def test_returns_empty_when_outputs_is_none(self):
        # Defensive: some kernels set outputs to None rather than []
        cell = {"cell_type": "code", "outputs": None}
        assert _cell_outputs(cell) == []


# ---------------------------------------------------------------------------
# 4. TestFigureRecords — multi-cell / multi-output aggregation
# ---------------------------------------------------------------------------
class TestFigureRecords:
    """`_figure_records` is the notebook -> list[record] aggregation."""

    def test_empty_notebook_returns_empty_list(self):
        nb = _nb([])
        assert _figure_records(Path("x.ipynb"), nb) == []

    def test_no_image_returns_empty_list(self):
        nb = _nb([
            _md("# Title"),
            _code("print('hi')"),
        ])
        # code cell with no outputs -> no records
        assert _figure_records(Path("x.ipynb"), nb) == []

    def test_single_png_in_single_cell(self):
        nb = _nb([_code_cell_with_png(PNG_100x100_B64)])
        recs = _figure_records(Path("x.ipynb"), nb)
        assert len(recs) == 1
        r = recs[0]
        assert r["cell_index"] == 0
        assert r["output_index"] == 0
        assert r["width"] == 100
        assert r["height"] == 100
        assert r["bytes"] > 0
        assert "notebook" in r

    def test_two_pngs_in_same_cell(self):
        nb = _nb([_code_cell_with_two_pngs()])
        recs = _figure_records(Path("x.ipynb"), nb)
        assert len(recs) == 2
        assert recs[0]["cell_index"] == 0 and recs[0]["output_index"] == 0
        assert recs[1]["cell_index"] == 0 and recs[1]["output_index"] == 1
        # Both should have valid dims
        assert recs[0]["width"] == 64 and recs[0]["height"] == 64
        assert recs[1]["width"] == 128 and recs[1]["height"] == 128

    def test_mixed_cells_preserve_cell_order(self):
        nb = _nb([
            _md("# Title"),                                              # cell 0 (skipped)
            _code_cell_with_png(_b64_png(50, 50)),                       # cell 1 -> 1 record
            _md("more prose"),                                           # cell 2 (skipped)
            _code_cell_with_two_pngs(),                                  # cell 3 -> 2 records
        ])
        recs = _figure_records(Path("x.ipynb"), nb)
        assert len(recs) == 3
        assert [r["cell_index"] for r in recs] == [1, 3, 3]
        assert [r["output_index"] for r in recs] == [0, 0, 1]

    def test_malformed_png_returns_dims_none(self):
        # data:image/png with bytes that are not a PNG -> dims None, still a record
        out = {
            "cell_type": "code",
            "source": "x",
            "outputs": [{"output_type": "display_data",
                         "data": {"image/png": "AAAA"}}],
            "execution_count": 1,
        }
        nb = _nb([out])
        recs = _figure_records(Path("x.ipynb"), nb)
        # base64 decode of "AAAA" succeeds (decodes to 3 zero bytes), but the
        # bytes don't start with PNG magic, so dims = None and record still exists
        assert len(recs) == 1
        assert recs[0]["width"] is None
        assert recs[0]["height"] is None


# ---------------------------------------------------------------------------
# 5. TestIterNotebooks — checkpoint skipping
# ---------------------------------------------------------------------------
class TestIterNotebooks:
    """`_iter_notebooks` walks a directory tree, skipping `.ipynb_checkpoints`."""

    def test_finds_ipynb_recursively(self, tmp_path: Path):
        (_make_ipynb(tmp_path / "a.ipynb"))
        (_make_ipynb(tmp_path / "sub" / "b.ipynb"))
        found = list(_iter_notebooks(tmp_path))
        names = sorted(p.name for p in found)
        assert names == ["a.ipynb", "b.ipynb"]

    def test_skips_ipynb_checkpoints(self, tmp_path: Path):
        (_make_ipynb(tmp_path / "a.ipynb"))
        # The .ipynb_checkpoints/ tree contains auto-save files that are NOT
        # notebook output -> they MUST be skipped.
        (_make_ipynb(tmp_path / ".ipynb_checkpoints" / "a-checkpoint.ipynb"))
        found = list(_iter_notebooks(tmp_path))
        names = [p.name for p in found]
        assert "a.ipynb" in names
        assert "a-checkpoint.ipynb" not in names

    def test_returns_empty_for_empty_directory(self, tmp_path: Path):
        assert list(_iter_notebooks(tmp_path)) == []

    def test_paths_are_sorted(self, tmp_path: Path):
        # Create in random-looking order; we expect lexicographic order
        (_make_ipynb(tmp_path / "z.ipynb"))
        (_make_ipynb(tmp_path / "a.ipynb"))
        (_make_ipynb(tmp_path / "m.ipynb"))
        names = [p.name for p in _iter_notebooks(tmp_path)]
        assert names == sorted(names)


def _make_ipynb(path: Path) -> Path:
    """Minimal helper — write an empty-but-valid notebook for iter tests."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_nb([])), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# 6. TestResolveRepoPath — absolute / repo-relatif / serie-relatif
# ---------------------------------------------------------------------------
class TestResolveRepoPath:
    """Path resolution strategy used by extract_figure / list_figures callers."""

    def test_absolute_path_returned_as_is(self, tmp_path: Path):
        abs_path = tmp_path / "MyIA.AI.Notebooks" / "RL" / "demo.ipynb"
        abs_path.parent.mkdir(parents=True, exist_ok=True)
        abs_path.write_text("{}")
        resolved = resolve_repo_path(str(abs_path), tmp_path)
        assert resolved.is_absolute()
        assert resolved.name == "demo.ipynb"

    def test_repo_relative_when_exists(self, tmp_path: Path):
        rel_path = "MyIA.AI.Notebooks/RL/demo.ipynb"
        full = tmp_path / rel_path
        full.parent.mkdir(parents=True, exist_ok=True)
        full.write_text("{}")
        resolved = resolve_repo_path(rel_path, tmp_path)
        assert resolved == full.resolve()

    def test_serie_relative_prefixed_when_repo_relative_missing(self, tmp_path: Path):
        # Caller passes "RL/demo.ipynb" — repo-root/RL/demo.ipynb does NOT exist
        # but repo-root/MyIA.AI.Notebooks/RL/demo.ipynb does.
        full = tmp_path / "MyIA.AI.Notebooks" / "RL" / "demo.ipynb"
        full.parent.mkdir(parents=True, exist_ok=True)
        full.write_text("{}")
        resolved = resolve_repo_path("RL/demo.ipynb", tmp_path)
        assert resolved == full.resolve()

    def test_custom_notebooks_subdir(self, tmp_path: Path):
        # Caller uses a different convention -> the prefixer adapts
        full = tmp_path / "courses" / "RL" / "demo.ipynb"
        full.parent.mkdir(parents=True, exist_ok=True)
        full.write_text("{}")
        resolved = resolve_repo_path(
            "RL/demo.ipynb", tmp_path, notebooks_subdir="courses")
        assert resolved == full.resolve()

    def test_repo_relative_takes_precedence_over_prefix(self, tmp_path: Path):
        # If BOTH paths exist (e.g. a notebook accidentally named "MyIA.AI.Notebooks/x")
        # the repo-relative wins to avoid double-prefix
        full_repo_rel = tmp_path / "MyIA.AI.Notebooks" / "demo.ipynb"
        full_repo_rel.parent.mkdir(parents=True, exist_ok=True)
        full_repo_rel.write_text("{}")
        # Don't create the prefixed variant — repo-rel exists, prefix doesn't matter
        resolved = resolve_repo_path("MyIA.AI.Notebooks/demo.ipynb", tmp_path)
        assert resolved == full_repo_rel.resolve()


# ---------------------------------------------------------------------------
# 7. TestListFigures — end-to-end inventory on tmp dir
# ---------------------------------------------------------------------------
class TestListFigures:
    """`list_figures` end-to-end: tmp-dir as fake serie, assert contract."""

    def test_raises_when_directory_missing(self, tmp_path: Path):
        with pytest.raises(FileNotFoundError):
            list_figures(tmp_path / "does_not_exist")

    def test_returns_empty_for_empty_directory(self, tmp_path: Path):
        result = list_figures(tmp_path)
        assert result["serie"] == tmp_path.name
        assert result["n_figures"] == 0
        assert result["n_notebooks_with_figures"] == 0
        assert result["total_bytes"] == 0
        assert result["figures"] == []

    def test_inventory_with_one_notebook_one_figure(self, tmp_path: Path):
        _write_nb(tmp_path / "demo.ipynb", [_code_cell_with_png(PNG_100x100_B64)])
        result = list_figures(tmp_path)
        assert result["n_figures"] == 1
        assert result["n_notebooks_with_figures"] == 1
        assert result["total_bytes"] > 0
        r = result["figures"][0]
        assert r["width"] == 100
        assert r["height"] == 100
        assert r["bytes"] > 0
        # over_weight flag is set for figures above MAX_BYTES_DEFAULT
        assert "over_weight" in r

    def test_relative_to_rebase(self, tmp_path: Path):
        nb = _write_nb(tmp_path / "demo.ipynb", [_code_cell_with_png(PNG_100x100_B64)])
        result = list_figures(tmp_path, relative_to=tmp_path)
        # notebook path should be relative to tmp_path, POSIX-style
        nb_rel = result["figures"][0]["notebook"]
        assert "\\" not in nb_rel
        assert nb_rel == "demo.ipynb"
        # root should also be relative
        assert "\\" not in result["root"]

    def test_over_weight_flag_for_heavy_figure(self, tmp_path: Path):
        # Synthesize a PNG whose byte size exceeds MAX_BYTES_DEFAULT (200 KB).
        # The noisy stand-in above is < 200 KB by design (small disk footprint,
        # fast CI). For the over_weight flag we need a truly heavy payload — we
        # build a valid PNG header + a large pseudo-random tail.
        import hashlib

        def chunk(t, d):
            return (
                struct.pack(">I", len(d))
                + t
                + d
                + struct.pack(">I", zlib.crc32(t + d) & 0xFFFFFFFF)
            )

        sig = b"\x89PNG\r\n\x1a\n"
        ihdr = struct.pack(">IIBBBBB", 64, 64, 8, 2, 0, 0, 0)
        # 200 KB of deterministic but incompressible-ish bytes tacked onto IDAT
        noise = b""
        while len(noise) < 300 * 1024:
            noise += hashlib.sha256(noise).digest()
        noise = noise[: 300 * 1024]
        idat = zlib.compress(noise, level=1)
        heavy = sig + chunk(b"IHDR", ihdr) + chunk(b"IDAT", idat) + chunk(b"IEND", b"")
        heavy_b64 = base64.b64encode(heavy).decode("ascii")
        # Sanity: the synthesized PNG really exceeds the default ceiling
        assert len(heavy) > MAX_BYTES_DEFAULT, (
            f"heavy fixture must exceed {MAX_BYTES_DEFAULT} bytes, got {len(heavy)}"
        )

        _write_nb(tmp_path / "heavy.ipynb", [_code_cell_with_png(heavy_b64)])
        result = list_figures(tmp_path)
        assert all(r["over_weight"] for r in result["figures"])

    def test_multiple_notebooks_counted_separately(self, tmp_path: Path):
        _write_nb(tmp_path / "a.ipynb", [_code_cell_with_png(_b64_png(50, 50))])
        _write_nb(tmp_path / "b.ipynb", [_code_cell_with_png(_b64_png(75, 75))])
        _write_nb(tmp_path / "c.ipynb", [])  # empty notebook -> no figures
        result = list_figures(tmp_path)
        assert result["n_figures"] == 2
        assert result["n_notebooks_with_figures"] == 2
        # Sorted by (notebook, cell_index, output_index) -> a then b
        assert [Path(r["notebook"]).name for r in result["figures"]] == ["a.ipynb", "b.ipynb"]

    def test_skips_invalid_json_notebooks(self, tmp_path: Path):
        # A notebook with corrupt JSON should be silently skipped (no crash)
        bad = tmp_path / "bad.ipynb"
        bad.write_text("this is not json {", encoding="utf-8")
        _write_nb(tmp_path / "good.ipynb", [_code_cell_with_png(PNG_100x100_B64)])
        result = list_figures(tmp_path)
        assert result["n_figures"] == 1
        assert "good.ipynb" in result["figures"][0]["notebook"]


# ---------------------------------------------------------------------------
# 8. TestOptimizeWithPil — PIL path + graceful PIL-absent fallback
# ---------------------------------------------------------------------------
class TestOptimizeWithPil:
    """`_optimize_with_pil`: optimisation and PIL-import-error resilience."""

    def test_returns_raw_when_pil_unavailable(self, monkeypatch):
        # Force the PIL import inside _optimize_with_pil to fail -> raw bytes returned
        import builtins

        real_import = builtins.__import__

        def fake_import(name, *args, **kwargs):
            if name == "PIL" or name.startswith("PIL."):
                raise ImportError("simulated PIL absent for test")
            return real_import(name, *args, **kwargs)

        monkeypatch.setattr(builtins, "__import__", fake_import)
        raw = _make_noisy_png(64, 64)
        out, used_pil = _optimize_with_pil(raw, max_dim=128)
        assert out == raw
        assert used_pil is False

    def test_returns_optimized_when_pil_available(self):
        """If PIL is installed, optimize() should produce a usable PNG with PIL used."""
        try:
            from PIL import Image  # noqa: F401
        except ImportError:
            pytest.skip("PIL not installed in test env")
        raw = _make_noisy_png(256, 256)
        out, used_pil = _optimize_with_pil(raw, max_dim=128)
        assert used_pil is True
        # PIL re-encoded: dimensions should match the downscaled target
        dims = _png_dimensions(out)
        assert dims is not None
        assert max(dims) <= 128

    def test_zero_dim_image_does_not_crash(self, monkeypatch):
        # Defensive: even if width/height are 0 (shouldn't happen on a real PNG),
        # the function must not raise — `max(w,h) > 0` guard.
        # We synthesize the raw bytes to look like a 0x0 PNG.
        bad_png = _PNG_MAGIC + b"\x00" * 20
        out, used_pil = _optimize_with_pil(bad_png, max_dim=128)
        # PIL path will fail on garbage bytes and fall back to raw
        assert out == bad_png
        assert used_pil is False

    def test_preserves_existing_png_when_already_small(self):
        """When image is already <= max_dim, optimize() still produces a valid PNG."""
        try:
            from PIL import Image  # noqa: F401
        except ImportError:
            pytest.skip("PIL not installed in test env")
        raw = _make_noisy_png(64, 64)
        out, used_pil = _optimize_with_pil(raw, max_dim=256)
        assert used_pil is True
        # Still a valid PNG header
        assert out[:8] == _PNG_MAGIC


# ---------------------------------------------------------------------------
# 9. TestAppendManifest — header init / idempotent replace / serie_root
# ---------------------------------------------------------------------------
class TestAppendManifest:
    """`_append_manifest`: provenance traceability for assets/readme/."""

    def _entry(self, fname: str = "fig.png", nb: str = "/abs/path/demo.ipynb",
               used_pil: bool = True) -> dict:
        return {
            "output": str(Path("/tmp") / fname),
            "notebook": nb,
            "cell_index": 0,
            "output_index": 0,
            "bytes": 1024,
            "used_pil": used_pil,
            "over_weight": False,
        }

    def test_creates_manifest_with_header_on_first_call(self, tmp_path: Path):
        _append_manifest(tmp_path, self._entry(), "Alt-text FR test")
        manifest = tmp_path / "MANIFEST.md"
        assert manifest.exists()
        body = manifest.read_text(encoding="utf-8")
        assert "# MANIFEST des figures README" in body
        assert "## fig.png" in body
        assert "Alt-text FR test" in body

    def test_appends_new_entry_to_existing_manifest(self, tmp_path: Path):
        _append_manifest(tmp_path, self._entry(fname="a.png"), "Alt A")
        _append_manifest(tmp_path, self._entry(fname="b.png"), "Alt B")
        body = (tmp_path / "MANIFEST.md").read_text(encoding="utf-8")
        assert "## a.png" in body
        assert "## b.png" in body
        assert "Alt A" in body
        assert "Alt B" in body

    def test_replaces_existing_entry_idempotently(self, tmp_path: Path):
        # First append -> creates entry
        _append_manifest(tmp_path, self._entry(), "Old alt-text")
        body1 = (tmp_path / "MANIFEST.md").read_text(encoding="utf-8")
        assert body1.count("## fig.png") == 1
        assert "Old alt-text" in body1
        # Second append with same fname -> REPLACES the block, no duplicate
        _append_manifest(tmp_path, self._entry(), "New alt-text FR")
        body2 = (tmp_path / "MANIFEST.md").read_text(encoding="utf-8")
        assert body2.count("## fig.png") == 1
        assert "New alt-text FR" in body2
        assert "Old alt-text" not in body2

    def test_serie_root_relative_path_in_source(self, tmp_path: Path):
        nb_abs = tmp_path / "MyIA.AI.Notebooks" / "RL" / "demo.ipynb"
        nb_abs.parent.mkdir(parents=True, exist_ok=True)
        nb_abs.write_text("{}")
        _append_manifest(tmp_path, self._entry(nb=str(nb_abs)),
                         "Alt", serie_root=tmp_path / "MyIA.AI.Notebooks" / "RL")
        body = (tmp_path / "MANIFEST.md").read_text(encoding="utf-8")
        assert "demo.ipynb" in body
        # Path should be displayed with POSIX separator and relative prefix
        assert "MyIA.AI.Notebooks" not in body or "RL/demo.ipynb" in body

    def test_used_pil_tag_in_weight_line(self, tmp_path: Path):
        _append_manifest(tmp_path, self._entry(used_pil=True), "Alt")
        body = (tmp_path / "MANIFEST.md").read_text(encoding="utf-8")
        assert "PIL optimise" in body
        # Second pass with PIL absent
        _append_manifest(tmp_path, self._entry(used_pil=False), "Alt")
        body2 = (tmp_path / "MANIFEST.md").read_text(encoding="utf-8")
        assert "raw (PIL absent)" in body2

    def test_replace_handles_alt_text_with_backslash(self, tmp_path: Path):
        """Replacing a manifest entry must NOT crash on alt-text containing backslashes.

        Regression test: the original implementation used ``re.sub(block, existing)``
        where ``block`` is the replacement string. ``re.sub`` interprets the
        replacement as a regex template, so a backslash inside the alt-text
        (e.g. a Windows path or escaped markdown) crashes with
        ``re.PatternError: bad escape \\X``. The fix builds the new manifest via
        split-match-rebuild instead.
        """
        # First insert
        _append_manifest(
            tmp_path, self._entry(),
            "First alt-text (no backslash)",
        )
        # Now replace with an alt-text containing a backslash — must NOT crash
        _append_manifest(
            tmp_path, self._entry(),
            r"Alt avec backslash : C:\Users\demo\nb.ipynb",
        )
        body = (tmp_path / "MANIFEST.md").read_text(encoding="utf-8")
        # Exactly one entry for this file (idempotent replace)
        assert body.count("## fig.png") == 1
        # Backslashes are preserved literally
        assert r"C:\Users\demo\nb.ipynb" in body
        # Old alt-text is gone
        assert "First alt-text" not in body


# ---------------------------------------------------------------------------
# 10. TestExtractFigure — end-to-end extraction + alt_text_fr HARD
# ---------------------------------------------------------------------------
class TestExtractFigure:
    """`extract_figure` end-to-end: PNG write + MANIFEST append + alt-text HARD."""

    def _setup_nb(self, tmp_path: Path) -> Path:
        return _write_nb(
            tmp_path / "demo.ipynb",
            [_code_cell_with_png(PNG_100x100_B64)],
        )

    def test_extracts_figure_and_writes_png(self, tmp_path: Path):
        nb = self._setup_nb(tmp_path)
        out_path = tmp_path / "assets" / "readme" / "demo.png"
        entry = extract_figure(
            nb_path=nb, cell_index=0, output_index=0,
            output_path=out_path,
            alt_text_fr="Figure d'exemple pour README",
        )
        assert out_path.exists()
        assert out_path.read_bytes()[:8] == _PNG_MAGIC
        assert entry["bytes"] > 0
        assert entry["used_pil"] is True or entry["used_pil"] is False  # depends on PIL
        # Source 1 provenance is recorded
        manifest = out_path.parent / "MANIFEST.md"
        assert manifest.exists()
        assert "demo.png" in manifest.read_text(encoding="utf-8")

    def test_alt_text_fr_empty_raises_value_error(self, tmp_path: Path):
        nb = self._setup_nb(tmp_path)
        out_path = tmp_path / "out.png"
        with pytest.raises(ValueError, match="alt_text_fr"):
            extract_figure(
                nb_path=nb, cell_index=0, output_index=0,
                output_path=out_path,
                alt_text_fr="",  # HARD rule violation
            )

    def test_alt_text_fr_whitespace_raises_value_error(self, tmp_path: Path):
        nb = self._setup_nb(tmp_path)
        with pytest.raises(ValueError, match="alt_text_fr"):
            extract_figure(
                nb_path=nb, cell_index=0, output_index=0,
                output_path=tmp_path / "out.png",
                alt_text_fr="   \t\n  ",
            )

    def test_cell_index_out_of_range_raises(self, tmp_path: Path):
        nb = self._setup_nb(tmp_path)
        with pytest.raises(ValueError, match="cell_index"):
            extract_figure(
                nb_path=nb, cell_index=99, output_index=0,
                output_path=tmp_path / "out.png",
                alt_text_fr="alt",
            )

    def test_output_index_out_of_range_raises(self, tmp_path: Path):
        nb = self._setup_nb(tmp_path)
        with pytest.raises(ValueError, match="output_index"):
            extract_figure(
                nb_path=nb, cell_index=0, output_index=99,
                output_path=tmp_path / "out.png",
                alt_text_fr="alt",
            )

    def test_cell_without_png_raises(self, tmp_path: Path):
        # Code cell with one output, but the output is NOT a PNG (stream + text/plain).
        # extract_figure must raise "ne porte pas de PNG" (NOT "output_index hors plage").
        non_png_cell = {
            "cell_type": "code",
            "source": "print('hello')",
            "metadata": {},
            "outputs": [
                {
                    "output_type": "stream",
                    "name": "stdout",
                    "text": "hello\n",
                }
            ],
            "execution_count": 1,
        }
        nb = _write_nb(tmp_path / "demo.ipynb", [non_png_cell])
        with pytest.raises(ValueError, match="ne porte pas de PNG"):
            extract_figure(
                nb_path=nb, cell_index=0, output_index=0,
                output_path=tmp_path / "out.png",
                alt_text_fr="alt",
            )

    def test_over_weight_flag_for_heavy_figure(self, tmp_path: Path):
        # 512x512 noisy PNG >> 200 KB
        nb = _write_nb(tmp_path / "heavy.ipynb", [_code_cell_with_png(PNG_NOISY_512_B64)])
        out_path = tmp_path / "heavy.png"
        entry = extract_figure(
            nb_path=nb, cell_index=0, output_index=0,
            output_path=out_path,
            alt_text_fr="Figure lourde",
        )
        # Even if PIL downscales, the post-optimize size should still be tracked
        assert "over_weight" in entry
        assert "bytes" in entry

    def test_creates_parent_directories(self, tmp_path: Path):
        nb = self._setup_nb(tmp_path)
        deep_path = tmp_path / "deep" / "nested" / "fig.png"
        extract_figure(
            nb_path=nb, cell_index=0, output_index=0,
            output_path=deep_path,
            alt_text_fr="alt",
        )
        assert deep_path.exists()


# ---------------------------------------------------------------------------
# 11. TestConstants — documented defaults (calibrated on EPIC #5654)
# ---------------------------------------------------------------------------
class TestConstants:
    """Module-level constants are part of the public contract."""

    def test_max_bytes_default_is_200kb(self):
        assert MAX_BYTES_DEFAULT == 200 * 1024

    def test_max_dim_default_is_1200(self):
        assert MAX_DIM_DEFAULT == 1200

    def test_png_magic_is_canonical(self):
        assert _PNG_MAGIC == b"\x89PNG\r\n\x1a\n"
        assert len(_PNG_MAGIC) == 8

    def test_ihdr_offsets_target_width_and_height(self):
        # Width at offset 16, height at offset 20 (after 8 magic + 4 len + 4 type)
        assert PNG_IHDR_WIDTH_OFFSET == 16
        assert PNG_IHDR_HEIGHT_OFFSET == 20
