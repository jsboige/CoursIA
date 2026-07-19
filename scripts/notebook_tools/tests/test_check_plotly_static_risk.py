"""Tests for scripts/notebook_tools/check_plotly_static_risk.py — Plotly-CDN static-render risk detector.

Why this test file exists
-------------------------
`check_plotly_static_risk.py` (canon C548-L2 / #6927) is the canonical DETECTOR
for notebook cells that emit `<script src="https://cdn.plot.ly/...">` HTML, which
renders correctly in a live .NET Interactive kernel (VS Code / Jupyter Lab with
Internet) BUT goes BLANK on GitHub sandbox / nbviewer / CSP-strict CI artifacts
(no `<script>` execution, no CDN load). The fix path is per-cell replacement with
a static `image/png` raster fallback (cf canon C548-L2 + PR #6931).

The detector's decision logic is structurally simple but must be pinned:

  - cell_is_risky(outputs) -> True iff (cdn.plot.ly in output blob) AND (no
    static-fallback MIME image/png | image/jpeg | image/svg+xml | image/webp |
    image/gif in same outputs).
  - iter_notebooks(root) skips vendored/archived dirs (`.git`, `_output`,
    `_archives`, `.ipynb_checkpoints`, `.lake`, `.claude`, `node_modules`) AND
    `_output.ipynb` duplicates (same outputs as primary).
  - scan_notebook(path) -> list of risky cell indexes (only code cells count).
  - main() is CLI-driven (--root, --json, --exit-risky-nb, --fix-plan-out); the
    fixture must exercise each branch.

Six clusters mirroring the detector's documented decision logic:

  1. TestConstants           -- CDN_PATTERN, IMAGE_MIMES, SKIP_DIRS defaults
  2. TestIterNotebooks       -- vendored/archived skip, _output.ipynb skip, end-to-end
  3. TestCellIsRisky         -- the 6 conjuncts of the decision (cdn yes/no, image yes/no)
  4. TestScanNotebook        -- end-to-end dict contract, cell_type filter, error tolerance
  5. TestMainExitCodes       -- CLI: --json / --fix-plan-out / --exit-risky-nb gate / missing-root
  6. TestFixPlanOutput       -- Markdown fix-plan table generation (R6 anti-monotonie advice pinned)

Test data design: synthetic notebook dicts (matching the real nbformat) constructed
inline. The detector is pure-stdlib + json + regex, hermetic on dict inputs.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

import pytest

# Import path setup: this file is co-located under scripts/notebook_tools/tests/
# alongside the module under test (one directory up).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_plotly_static_risk as cpr  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers — synthetic notebook fixtures
# ---------------------------------------------------------------------------

def _mk_cell(cell_type: str, outputs: list | None = None) -> dict:
    """Build a minimal nbformat cell dict."""
    cell = {"cell_type": cell_type, "metadata": {}, "source": []}
    if cell_type == "code":
        cell["execution_count"] = 1
        cell["outputs"] = outputs if outputs is not None else []
    return cell


def _mk_output_html(html: str) -> dict:
    """Build an HTML display_data output (the CDN-Plotly rendering shape)."""
    return {"output_type": "display_data", "data": {"text/html": html}, "metadata": {}}


def _mk_output_image(mime: str, b64: str = "iVBORw0KGgo=") -> dict:
    """Build a base64 image display_data output (the static-fallback shape)."""
    return {"output_type": "display_data", "data": {mime: b64}, "metadata": {}}


# Common CDN HTML payloads used in the .NET Interactive PlotlyHtml+Formatter.Register pattern
PLOTLY_CDN_HTML = '<script src="https://cdn.plot.ly/plotly-2.27.0.min.js"></script><div>...</div>'
PLOTLY_CDN_HTML_ALT = '<script src="https://cdn.plotly.com/plotly-2.27.0.min.js"></script>'  # alt TLD
PLOTLY_OFFLINE_HTML = '<div class="plotly-graph-div"></div>'  # no CDN reference


def _mk_notebook(cells: list[dict]) -> dict:
    """Build a minimal nbformat notebook dict."""
    return {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "csharp", "language": "C#"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_nb(path: Path, nb: dict) -> None:
    """Write a synthetic notebook to disk as valid JSON."""
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")


# ===========================================================================
# 1. TestConstants
# ===========================================================================

class TestConstants:
    """Pinned invariants: CDN_PATTERN regex, IMAGE_MIMES, SKIP_DIRS defaults."""

    def test_cdn_pattern_is_case_insensitive(self):
        # The detector matches both `cdn.plot.ly` and `cdn.plotly.com`
        # (both spellings appear in the wild across Plotly.js versions).
        assert cpr.CDN_PATTERN.search("CDN.PLOT.LY") is not None
        assert cpr.CDN_PATTERN.search("Cdn.Plot.Ly") is not None
        assert cpr.CDN_PATTERN.search("cdn.plot.ly") is not None

    def test_cdn_pattern_matches_plotly_com_alt(self):
        # Some Plotly.js CDN URLs use plotly.com instead of plot.ly
        assert cpr.CDN_PATTERN.search("cdn.plotly.com") is not None

    def test_cdn_pattern_does_not_match_unrelated_hosts(self):
        # Must NOT match unrelated CDN-like strings (anchor regression test)
        assert cpr.CDN_PATTERN.search("cdn.jsdelivr.net") is None
        assert cpr.CDN_PATTERN.search("cdn.skypack.dev") is None
        assert cpr.CDN_PATTERN.search("plotly-min.js") is None  # without `cdn.`
        assert cpr.CDN_PATTERN.search("https://example.com/foo") is None

    def test_image_mimes_covers_all_static_fallbacks(self):
        # The 5 canonical image MIMEs that GitHub/nbviewer can render inline
        expected = {"image/png", "image/jpeg", "image/svg+xml", "image/webp", "image/gif"}
        assert set(cpr.IMAGE_MIMES) == expected

    def test_skip_dirs_includes_all_vendored_paths(self):
        # Pinned: skipping is critical to avoid scanning Lean vendored / archives / node_modules
        expected = {
            ".git",
            "_output",
            "_archives",
            ".ipynb_checkpoints",
            ".lake",
            ".claude",
            "node_modules",
        }
        assert cpr.SKIP_DIRS == expected


# ===========================================================================
# 2. TestIterNotebooks
# ===========================================================================

class TestIterNotebooks:
    """iter_notebooks(root) yields .ipynb paths excluding vendored/archived/_output."""

    def test_iter_yields_root_ipynb(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code")])
        _write_nb(tmp_path / "test.ipynb", nb)
        results = list(cpr.iter_notebooks(tmp_path))
        assert len(results) == 1
        assert results[0].name == "test.ipynb"

    def test_iter_recurses_into_subdirs(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code")])
        sub = tmp_path / "sub" / "deep"
        sub.mkdir(parents=True)
        _write_nb(sub / "leaf.ipynb", nb)
        results = list(cpr.iter_notebooks(tmp_path))
        assert len(results) == 1
        assert results[0].name == "leaf.ipynb"

    def test_iter_skips_git_dir(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code")])
        (tmp_path / ".git").mkdir()
        _write_nb(tmp_path / ".git" / "do_not_scan.ipynb", nb)
        _write_nb(tmp_path / "ok.ipynb", nb)
        results = list(cpr.iter_notebooks(tmp_path))
        names = [p.name for p in results]
        assert "ok.ipynb" in names
        assert "do_not_scan.ipynb" not in names

    def test_iter_skips_all_vendored_dirs(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code")])
        for skip in cpr.SKIP_DIRS:
            (tmp_path / skip).mkdir()
            _write_nb(tmp_path / skip / "x.ipynb", nb)
        _write_nb(tmp_path / "keep.ipynb", nb)
        results = list(cpr.iter_notebooks(tmp_path))
        names = [p.name for p in results]
        assert names == ["keep.ipynb"]

    def test_iter_skips_output_ipynb_duplicates(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code")])
        _write_nb(tmp_path / "primary.ipynb", nb)
        _write_nb(tmp_path / "primary_output.ipynb", nb)
        results = list(cpr.iter_notebooks(tmp_path))
        names = sorted(p.name for p in results)
        assert names == ["primary.ipynb"]

    def test_iter_skips_lake_vendored_lean(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code")])
        (tmp_path / ".lake" / "packages" / "Mathlib").mkdir(parents=True)
        _write_nb(tmp_path / ".lake" / "packages" / "Mathlib" / "theorem.ipynb", nb)
        _write_nb(tmp_path / "user.ipynb", nb)
        results = list(cpr.iter_notebooks(tmp_path))
        names = [p.name for p in results]
        assert names == ["user.ipynb"]


# ===========================================================================
# 3. TestCellIsRisky
# ===========================================================================

class TestCellIsRisky:
    """The 6 conjuncts of the cell_is_risky decision matrix."""

    def test_no_outputs_not_risky(self):
        # Un-executed cell: nothing to render in static mode either, not flagged.
        cell = _mk_cell("code", outputs=[])
        assert cpr.cell_is_risky(cell) is False

    def test_no_cdn_not_risky(self):
        # Pure matplotlib image output: no CDN, no risk.
        cell = _mk_cell("code", outputs=[_mk_output_image("image/png")])
        assert cpr.cell_is_risky(cell) is False

    def test_cdn_only_risky(self):
        # The canonical risky pattern: CDN Plotly, no static fallback.
        cell = _mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)])
        assert cpr.cell_is_risky(cell) is True

    def test_cdn_with_png_fallback_not_risky(self):
        # The "fixed" pattern: same cell also emits a PNG, so GitHub can fall back.
        cell = _mk_cell("code", outputs=[
            _mk_output_html(PLOTLY_CDN_HTML),
            _mk_output_image("image/png"),
        ])
        assert cpr.cell_is_risky(cell) is False

    def test_cdn_with_svg_fallback_not_risky(self):
        # SVG fallback is the canonical .NET Plotly static-render fix (cf C548-L2).
        cell = _mk_cell("code", outputs=[
            _mk_output_html(PLOTLY_CDN_HTML),
            _mk_output_image("image/svg+xml"),
        ])
        assert cpr.cell_is_risky(cell) is False

    @pytest.mark.parametrize("mime", ["image/png", "image/jpeg", "image/svg+xml", "image/webp", "image/gif"])
    def test_cdn_with_each_image_mime_not_risky(self, mime: str):
        """All 5 static-fallback MIMEs must be detected as a fallback."""
        cell = _mk_cell("code", outputs=[
            _mk_output_html(PLOTLY_CDN_HTML),
            _mk_output_image(mime),
        ])
        assert cpr.cell_is_risky(cell) is False

    def test_offline_plotly_html_not_risky(self):
        # Plotly offline-rendered (no CDN reference in script src): no risk.
        cell = _mk_cell("code", outputs=[_mk_output_html(PLOTLY_OFFLINE_HTML)])
        assert cpr.cell_is_risky(cell) is False

    def test_cdn_alternate_tld_risky(self):
        # plotly.com alt TLD must also be flagged.
        cell = _mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML_ALT)])
        assert cpr.cell_is_risky(cell) is True

    def test_non_serializable_outputs_not_risky(self):
        # Defensive: outputs with non-serializable objects fall through as non-risky.
        # Simulate with a dict that json.dumps cannot handle.
        cell = _mk_cell("code", outputs=[{"data": {"text/html": set()}}])  # set is not JSON-serializable
        assert cpr.cell_is_risky(cell) is False

    def test_output_without_data_dict_not_risky(self):
        # stream output without `data` field — no MIME to inspect.
        cell = _mk_cell("code", outputs=[{"output_type": "stream", "name": "stdout", "text": "hello"}])
        assert cpr.cell_is_risky(cell) is False


# ===========================================================================
# 4. TestScanNotebook
# ===========================================================================

class TestScanNotebook:
    """scan_notebook(path) returns list of cell indexes that are risky."""

    def test_scan_returns_empty_when_no_risk(self, tmp_path: Path):
        nb = _mk_notebook([
            _mk_cell("markdown"),
            _mk_cell("code", outputs=[_mk_output_image("image/png")]),
            _mk_cell("code", outputs=[_mk_output_html(PLOTLY_OFFLINE_HTML)]),
        ])
        p = tmp_path / "safe.ipynb"
        _write_nb(p, nb)
        assert cpr.scan_notebook(p) == []

    def test_scan_returns_cell_indexes_of_risky_cells(self, tmp_path: Path):
        nb = _mk_notebook([
            _mk_cell("markdown"),  # idx 0: skip (not code)
            _mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)]),  # idx 1: risky
            _mk_cell("code", outputs=[_mk_output_image("image/png")]),  # idx 2: safe
            _mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)]),  # idx 3: risky
        ])
        p = tmp_path / "mixed.ipynb"
        _write_nb(p, nb)
        assert cpr.scan_notebook(p) == [1, 3]

    def test_scan_skips_markdown_cells(self, tmp_path: Path):
        # Even if markdown contains cdn.plot.ly in raw text, it's not rendered
        # as cell output, so should not be flagged.
        nb = _mk_notebook([
            _mk_cell("markdown"),
        ])
        # Markdown cells have no outputs by default
        p = tmp_path / "md_only.ipynb"
        _write_nb(p, nb)
        assert cpr.scan_notebook(p) == []

    def test_scan_handles_malformed_json(self, tmp_path: Path, capsys):
        p = tmp_path / "broken.ipynb"
        p.write_text("{not valid json", encoding="utf-8")
        assert cpr.scan_notebook(p) == []
        err = capsys.readouterr().err
        assert "WARN" in err
        assert "broken.ipynb" in err

    def test_scan_handles_missing_file(self, tmp_path: Path, capsys):
        p = tmp_path / "missing.ipynb"
        assert cpr.scan_notebook(p) == []
        err = capsys.readouterr().err
        assert "WARN" in err


# ===========================================================================
# 5. TestMainExitCodes
# ===========================================================================

class TestMainExitCodes:
    """CLI: --json / --fix-plan-out / --exit-risky-nb gate / missing-root."""

    def _run_cli(self, *args: str, cwd: Path | None = None) -> subprocess.CompletedProcess:
        """Invoke the module's main() as a subprocess (hermetic)."""
        cmd = [sys.executable, "-m", "scripts.notebook_tools.check_plotly_static_risk", *args]
        return subprocess.run(
            cmd,
            cwd=str(cwd) if cwd else None,
            capture_output=True,
            text=True,
            timeout=60,
        )

    def test_json_emits_valid_json_structure(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)])])
        sub = tmp_path / "Probas" / "Infer"
        sub.mkdir(parents=True)
        _write_nb(sub / "risk.ipynb", nb)
        result = self._run_cli("--root", str(tmp_path), "--json")
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert "summary" in data
        assert data["summary"]["risky_notebooks"] == 1
        assert data["summary"]["risky_cells_total"] == 1
        assert data["risky_cells"][0]["family"] == "Probas/Infer"
        assert data["risky_cells"][0]["cell_idx"] == 0

    def test_human_readable_output_contains_summary(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)])])
        _write_nb(tmp_path / "r.ipynb", nb)
        result = self._run_cli("--root", str(tmp_path))
        assert result.returncode == 0
        out = result.stdout
        assert "Plotly-CDN static-render risk scan" in out
        assert "Risky cells" in out
        assert "1 nb, 1 cells" in out or "1 nb" in out  # by-family line

    def test_missing_root_returns_exit_code_2(self, tmp_path: Path):
        result = self._run_cli("--root", str(tmp_path / "does_not_exist"))
        assert result.returncode == 2
        assert "root not found" in result.stderr

    def test_exit_risky_nb_below_threshold_returns_0(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)])])
        _write_nb(tmp_path / "r.ipynb", nb)
        result = self._run_cli("--root", str(tmp_path), "--exit-risky-nb", "5")
        assert result.returncode == 0

    def test_exit_risky_nb_above_threshold_returns_1(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)])])
        _write_nb(tmp_path / "r.ipynb", nb)
        result = self._run_cli("--root", str(tmp_path), "--exit-risky-nb", "0")
        assert result.returncode == 1
        assert "FAIL" in result.stderr


# ===========================================================================
# 6. TestFixPlanOutput
# ===========================================================================

class TestFixPlanOutput:
    """Markdown fix-plan table generation -- R6 anti-monotonie advice pinned."""

    def _run_cli(self, *args: str) -> subprocess.CompletedProcess:
        cmd = [sys.executable, "-m", "scripts.notebook_tools.check_plotly_static_risk", *args]
        return subprocess.run(cmd, capture_output=True, text=True, timeout=60)

    def test_fix_plan_writes_markdown_with_summary(self, tmp_path: Path):
        nb = _mk_notebook([_mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)])])
        sub = tmp_path / "Probas" / "Infer"
        sub.mkdir(parents=True)
        _write_nb(sub / "risk.ipynb", nb)
        out_path = tmp_path / "fix_plan.md"
        result = self._run_cli("--root", str(tmp_path), "--fix-plan-out", str(out_path))
        assert result.returncode == 0
        assert out_path.exists()
        content = out_path.read_text(encoding="utf-8")
        assert "# Fix plan — Plotly-CDN static-rendering risk (#6927)" in content
        assert "1 notebooks scanned" in content
        assert "1 notebooks risky" in content
        assert "1 cells risky total" in content

    def test_fix_plan_pins_r6_anti_monotonie_advice(self, tmp_path: Path):
        # The fix-plan file embeds documented per-PR R3 atomique + R6 anti-monotonie
        # guidance. Pin it: future refactors that drop the guidance are caught.
        nb = _mk_notebook([_mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)])])
        _write_nb(tmp_path / "r.ipynb", nb)
        out_path = tmp_path / "fix_plan.md"
        result = self._run_cli("--root", str(tmp_path), "--fix-plan-out", str(out_path))
        assert result.returncode == 0
        content = out_path.read_text(encoding="utf-8")
        assert "R6 anti-monotonie" in content
        assert "R3 atomique" in content
        assert "Pick ONE notebook per PR" in content

    def test_fix_plan_includes_risky_cells_table(self, tmp_path: Path):
        nb = _mk_notebook([
            _mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML)]),
            _mk_cell("code", outputs=[_mk_output_image("image/png")]),
            _mk_cell("code", outputs=[_mk_output_html(PLOTLY_CDN_HTML_ALT)]),
        ])
        _write_nb(tmp_path / "multi.ipynb", nb)
        out_path = tmp_path / "fix_plan.md"
        result = self._run_cli("--root", str(tmp_path), "--fix-plan-out", str(out_path))
        assert result.returncode == 0
        content = out_path.read_text(encoding="utf-8")
        # 2 risky cells (idx 0 and idx 2)
        assert "2 cells risky total" in content
        # Risky cells table present
        assert "## Risky cells" in content
        assert "| # | Notebook | cell idx | Family |" in content
