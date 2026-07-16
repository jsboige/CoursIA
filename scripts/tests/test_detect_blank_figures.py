"""Tests for scripts/notebook_tools/detect_blank_figures.py — Prong-A blank-figure detector.

Validates the deterministic dimension/size degeneracy check against the #6891
baseline (70-byte 1x1 PNG = fabrication) vs real matplotlib figures (KB-sized,
hundreds of px). Because detection is deterministic (parse PNG IHDR + byte size),
there is no heuristic false-positive risk on real plots — the tests lock the
clean separation in.
"""

import base64
import json
import sys
from pathlib import Path

import pytest

# Convention siblings (test_detect_ascii_workaround.py) : inserer
# scripts/notebook_tools/ et importer le module directement (evite d'enregistrer
# le repertoire comme namespace package masquant notebook_tools.py).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

from detect_blank_figures import (  # noqa: E402
    MIN_BYTES,
    MIN_DIM,
    SKIP_DIRS,
    _classify_image,
    _decode_image,
    _png_dimensions,
    _should_skip,
    detect_cell,
    main,
    scan_notebook,
)

_PNG_SIG = b"\x89PNG\r\n\x1a\n"


def make_png(width: int, height: int, total_bytes: int) -> bytes:
    """Construct a minimal PNG whose IHDR carries `width`x`height`, padded to `total_bytes`."""
    ihdr = (
        _PNG_SIG
        + b"\x00\x00\x00\x0d"          # IHDR length = 13
        + b"IHDR"
        + width.to_bytes(4, "big")
        + height.to_bytes(4, "big")
        + b"\x08\x02\x00\x00\x00"      # bit depth / color type / compression / filter / interlace
    )
    pad = b"\x00" * max(0, total_bytes - len(ihdr))
    return ihdr + pad


def b64(raw: bytes) -> str:
    return base64.b64encode(raw).decode("ascii")


def code_cell_with_png(raw: bytes, execution_count: int = 1) -> dict:
    return {
        "cell_type": "code",
        "execution_count": execution_count,
        "source": ["import matplotlib.pyplot as plt\n", "plt.plot([1,2,3])\n", "plt.show()\n"],
        "outputs": [
            {"output_type": "display_data", "data": {"image/png": b64(raw)}, "metadata": {}}
        ],
    }


# The canonical #6891 fabrication: the exact 70-byte 1x1 PNG matplotlib emits for
# an empty figure. Reconstructed to match (real bytes = 70).
BLANK_1x1 = make_png(1, 1, 70)
REAL_PLOT = make_png(690, 590, 41223)   # research.ipynb AllWeather cell — real matplotlib figure


class TestPngDimensions:
    def test_parses_real_dimensions(self):
        assert _png_dimensions(make_png(690, 590, 41223)) == (690, 590)

    def test_parses_1x1(self):
        assert _png_dimensions(BLANK_1x1) == (1, 1)

    def test_none_on_non_png(self):
        assert _png_dimensions(b"not a png at all, just bytes here padding") is None

    def test_none_on_too_short(self):
        assert _png_dimensions(_PNG_SIG + b"\x00\x00") is None


class TestClassifyImage:
    def test_1x1_flagged_both_reasons(self):
        """70-byte 1x1 = the #6891 case: BOTH degenerate dimensions AND tiny payload."""
        f = _classify_image("image/png", BLANK_1x1, MIN_DIM, MIN_BYTES)
        assert f is not None
        reasons = " ".join(f["reasons"])
        assert "degenerate_dimensions(1x1)" in reasons
        assert "tiny_payload(70B)" in reasons
        assert f["dimensions"] == [1, 1]
        assert f["bytes"] == 70

    def test_real_plot_not_flagged(self):
        """690x590 @ 41KB = a real figure: neither degenerate nor tiny -> None."""
        assert _classify_image("image/png", REAL_PLOT, MIN_DIM, MIN_BYTES) is None

    def test_small_dimension_full_bytes_flagged_on_dims_only(self):
        """A 4px-tall but heavy image is flagged on dimensions, not on size."""
        img = make_png(600, 4, 5000)
        f = _classify_image("image/png", img, MIN_DIM, MIN_BYTES)
        assert f is not None
        assert any("degenerate_dimensions" in r for r in f["reasons"])
        assert not any("tiny_payload" in r for r in f["reasons"])

    def test_full_dimension_tiny_bytes_flagged_on_size_only(self):
        """A full-size-declared PNG that is nonetheless < MIN_BYTES is flagged on size."""
        img = make_png(690, 590, 200)  # dims fine, but only 200 bytes
        f = _classify_image("image/png", img, MIN_DIM, MIN_BYTES)
        assert f is not None
        assert any("tiny_payload" in r for r in f["reasons"])
        assert not any("degenerate_dimensions" in r for r in f["reasons"])

    def test_jpeg_flagged_on_size_only(self):
        """JPEG dimensions are not parsed (PNG-only); a tiny JPEG is caught on size."""
        f = _classify_image("image/jpeg", b"\xff\xd8\xff" + b"\x00" * 50, MIN_DIM, MIN_BYTES)
        assert f is not None
        assert f["dimensions"] is None
        assert any("tiny_payload" in r for r in f["reasons"])


class TestDetectCell:
    def test_blank_cell_one_finding(self):
        findings = detect_cell(code_cell_with_png(BLANK_1x1))
        assert len(findings) == 1
        assert findings[0]["output_index"] == 0

    def test_real_cell_no_finding(self):
        assert detect_cell(code_cell_with_png(REAL_PLOT)) == []

    def test_cell_without_image_output_no_finding(self):
        cell = {
            "cell_type": "code",
            "execution_count": 1,
            "source": ["print('hello')\n"],
            "outputs": [{"output_type": "stream", "name": "stdout", "text": ["hello\n"]}],
        }
        assert detect_cell(cell) == []

    def test_malformed_payload_does_not_crash(self):
        cell = {
            "cell_type": "code",
            "outputs": [{"output_type": "display_data", "data": {"image/png": 12345}, "metadata": {}}],
        }
        # non-str payload decodes to None -> skipped, no exception
        assert detect_cell(cell) == []


class TestDecodeImage:
    def test_list_payload_joined(self):
        raw = _decode_image([b64(BLANK_1x1)[:10], b64(BLANK_1x1)[10:]])
        assert raw == BLANK_1x1

    def test_non_str_returns_none(self):
        assert _decode_image(999) is None


class TestScanNotebook:
    def _write_nb(self, tmp_path: Path, cells: list[dict]) -> Path:
        nb = {"cells": cells, "metadata": {"kernelspec": {"name": "python3"}}, "nbformat": 4}
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        return p

    def test_flags_only_degenerate(self, tmp_path):
        p = self._write_nb(tmp_path, [
            code_cell_with_png(BLANK_1x1, 1),   # fabrication
            code_cell_with_png(REAL_PLOT, 2),   # real
            {"cell_type": "markdown", "source": ["# title"]},
        ])
        res = scan_notebook(p)
        assert res["error"] is None
        assert len(res["hits"]) == 1
        assert res["hits"][0]["cell_index"] == 0
        assert res["kernel"] == "python3"

    def test_clean_notebook_no_hits(self, tmp_path):
        p = self._write_nb(tmp_path, [code_cell_with_png(REAL_PLOT, 1)])
        assert scan_notebook(p)["hits"] == []

    def test_unreadable_notebook_reports_error(self, tmp_path):
        p = tmp_path / "broken.ipynb"
        p.write_text("{not json", encoding="utf-8")
        res = scan_notebook(p)
        assert res["error"] is not None
        assert res["hits"] == []


class TestSkipDirs:
    def test_should_skip_output_suffix(self):
        assert _should_skip(Path("QuantConnect/projects/AllWeather/quantbook_output.ipynb")) is True

    def test_should_not_skip_canonical(self):
        assert _should_skip(Path("QuantConnect/projects/AllWeather/quantbook.ipynb")) is False

    def test_should_skip_lake_dir(self):
        assert _should_skip(Path("SomeFam/.lake/build/nb.ipynb")) is True

    def test_skip_dirs_has_expected_entries(self):
        assert ".lake" in SKIP_DIRS and "worktrees" in SKIP_DIRS


class TestMainCli:
    def _write_nb(self, tmp_path: Path, cells: list[dict], name="nb.ipynb") -> Path:
        nb = {"cells": cells, "metadata": {"kernelspec": {"name": "python3"}}, "nbformat": 4}
        p = tmp_path / name
        p.write_text(json.dumps(nb), encoding="utf-8")
        return p

    def test_check_returns_1_on_degenerate(self, tmp_path, capsys):
        p = self._write_nb(tmp_path, [code_cell_with_png(BLANK_1x1)])
        rc = main([str(p), "--check"])
        assert rc == 1

    def test_check_returns_0_on_clean(self, tmp_path):
        p = self._write_nb(tmp_path, [code_cell_with_png(REAL_PLOT)])
        assert main([str(p), "--check"]) == 0

    def test_missing_file_returns_2(self, tmp_path):
        assert main([str(tmp_path / "nope.ipynb"), "--check"]) == 2

    def test_json_output_shape(self, tmp_path, capsys):
        p = self._write_nb(tmp_path, [code_cell_with_png(BLANK_1x1)])
        main([str(p), "--json"])
        payload = json.loads(capsys.readouterr().out)
        assert payload["total_hits"] == 1
        assert payload["notebooks_scanned"] == 1

    def test_min_dim_threshold_honored(self, tmp_path):
        """A 690x10 image passes at default min-dim=8 but fails at min-dim=16."""
        p = self._write_nb(tmp_path, [code_cell_with_png(make_png(690, 10, 5000))])
        assert main([str(p), "--check"]) == 0                       # 10 > 8 default
        assert main([str(p), "--check", "--min-dim", "16"]) == 1    # 10 <= 16
