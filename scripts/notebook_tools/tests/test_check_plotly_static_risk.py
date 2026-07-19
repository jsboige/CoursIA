"""Tests for scripts/notebook_tools/check_plotly_static_risk.py — Plotly-CDN
static-rendering risk detector (EPIC #6927, canon C548-L2).

Why this test file exists
-------------------------
``check_plotly_static_risk.py`` flags notebooks whose code-cell outputs
contain a Plotly-CDN script reference (``cdn.plot.ly``/``cdn.plotly``) with
**no** static ``image/*`` fallback. Such cells render correctly in a live
.NET Interactive kernel (Internet access) but render as a blank div on
GitHub / nbviewer / CSP-strict CI artifacts. This detector is the
**barometer + fix-plan source** feeding the R3-atomic PR cycle that
replaces the CDN script with a static PNG/SVG (1 notebook per PR).

The sibling detectors under ``scripts/notebook_tools/`` carry their own
pytest roll-out (po-2025 c.628 PR #7391, po-2024 c.722 PR #7402,
po-2024 c.723 PR #7406, c.716 PR #7374, c.720 PR #7212). This file
completes the roll-out for the Plotly-CDN risk detector — gap identified
during the c.728 pool audit (no test file present despite detector
shipping in #6931).

Eight clusters mirroring the module's documented decision logic :

  1. TestCdnPattern         -- CDN_PATTERN regex (cdn.plot.ly, cdn.plotly, mixed case)
  2. TestImageMimes         -- IMAGE_MIMES set (5 entries)
  3. TestSkipDirs           -- SKIP_DIRS set (8 entries incl. Lean vendored)
  4. TestIterNotebooks      -- vendored/archived skip + _output.ipynb skip
  5. TestCellIsRisky        -- 8 branches: no-outputs, non-code, Plotly-no-fallback,
                              Plotly-with-PNG, Plotly-with-SVG, Plotly-with-non-image,
                              malformed-outputs, multi-output mixed
  6. TestScanNotebook       -- per-cell aggregation + malformed JSON graceful
  7. TestMainCli            -- argparse --json/--exit-risky-nb/--fix-plan-out + stdout format
  8. TestEndToEnd           -- tmp tree with risky + safe notebooks + full scan

Test data design: notebooks are synthesized as JSON via the standard nbformat
shape (cells: list of {cell_type, outputs}). No real .ipynb is mutated. The
end-to-end smoke scan uses an in-tmp ``MyIA.AI.Notebooks/`` tree.
"""
import json
import subprocess
import sys
from pathlib import Path
from typing import Iterable

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from check_plotly_static_risk import (  # noqa: E402
    CDN_PATTERN,
    IMAGE_MIMES,
    SKIP_DIRS,
    cell_is_risky,
    iter_notebooks,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers — notebook cell construction
# ---------------------------------------------------------------------------
def _code_cell(outputs: list | None) -> dict:
    """Build a minimal .NET-Interactive-style code cell."""
    return {
        "cell_type": "code",
        "execution_count": 1,
        "metadata": {},
        "outputs": outputs or [],
        "source": ["print('hello')"],
    }


def _markdown_cell(text: str = "# Heading") -> dict:
    return {
        "cell_type": "markdown",
        "metadata": {},
        "source": [text],
    }


def _plotly_cdn_output() -> dict:
    """An output of type display_data with text/html containing cdn.plot.ly."""
    return {
        "output_type": "display_data",
        "data": {
            "text/html": [
                '<div><script src="https://cdn.plot.ly/plotly-2.27.0.min.js"></script></div>'
            ],
            "text/plain": ["<plotly>"],
        },
        "metadata": {},
    }


def _png_output() -> dict:
    return {
        "output_type": "display_data",
        "data": {"image/png": "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mNkYAAAAAYAAjCB0C8AAAAASUVORK5CYII="},
        "metadata": {},
    }


def _svg_output() -> dict:
    return {
        "output_type": "display_data",
        "data": {"image/svg+xml": "<svg xmlns='http://www.w3.org/2000/svg' width='10' height='10'/>"},
        "metadata": {},
    }


def _plain_output() -> dict:
    return {
        "output_type": "display_data",
        "data": {"text/plain": ["42"]},
        "metadata": {},
    }


def _notebook_with_cells(cells: Iterable[dict]) -> dict:
    return {
        "cells": list(cells),
        "metadata": {"kernelspec": {"name": "csharp"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_notebook(tmp_path: Path, rel: str, nb: dict) -> Path:
    p = tmp_path / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return p


# ===========================================================================
# 1. CDN_PATTERN — regex sanity
# ===========================================================================
class TestCdnPattern:
    """Plotly CDN reference must be detected across case + variation."""

    def test_matches_lowercase_cdn_plotly(self):
        assert CDN_PATTERN.search("https://cdn.plot.ly/plotly-2.27.0.min.js")

    def test_no_match_compact_cdnplotly(self):
        # The regex requires a dot between plot and ly: cdn.plot.ly OR cdn.plotly
        # (the latter = cdn.plot + ly with NO dot). cdnplotly.com (compact form,
        # no separator at all) is NOT matched by this regex. Documented gap:
        # the detector scopes to the canonical CDN host patterns.
        assert not CDN_PATTERN.search('<script src="https://cdnplotly.com/foo.js">')

    def test_matches_mixed_case(self):
        assert CDN_PATTERN.search("<SCRIPT SRC='HTTPS://CDN.PLOT.LY/foo.js'>")

    def test_no_match_plain_text(self):
        assert not CDN_PATTERN.search("just some text without plotly")

    def test_no_match_unrelated_cdn(self):
        # cdnjs.cloudflare.com is a different CDN — must NOT match.
        assert not CDN_PATTERN.search("https://cdnjs.cloudflare.com/jquery.js")

    def test_no_match_empty(self):
        assert not CDN_PATTERN.search("")


# ===========================================================================
# 2. IMAGE_MIMES — fallback set
# ===========================================================================
class TestImageMimes:
    """The fallback set must cover the canonical raster MIME types."""

    def test_includes_png(self):
        assert "image/png" in IMAGE_MIMES

    def test_includes_jpeg(self):
        assert "image/jpeg" in IMAGE_MIMES

    def test_includes_svg(self):
        assert "image/svg+xml" in IMAGE_MIMES

    def test_includes_webp(self):
        assert "image/webp" in IMAGE_MIMES

    def test_includes_gif(self):
        assert "image/gif" in IMAGE_MIMES

    def test_excludes_text_html(self):
        assert "text/html" not in IMAGE_MIMES

    def test_excludes_application_json(self):
        assert "application/json" not in IMAGE_MIMES

    def test_size_matches_docstring(self):
        # 5 rasters, as documented in the script header.
        assert len(IMAGE_MIMES) == 5


# ===========================================================================
# 3. SKIP_DIRS — vendored/archived exclusions
# ===========================================================================
class TestSkipDirs:
    """The skip-set must exclude vendored/archived/output paths."""

    def test_includes_git(self):
        assert ".git" in SKIP_DIRS

    def test_includes_lake_lean_vendored(self):
        assert ".lake" in SKIP_DIRS

    def test_includes_claude(self):
        assert ".claude" in SKIP_DIRS

    def test_includes_ipynb_checkpoints(self):
        assert ".ipynb_checkpoints" in SKIP_DIRS

    def test_includes_output(self):
        assert "_output" in SKIP_DIRS

    def test_includes_archives(self):
        assert "_archives" in SKIP_DIRS

    def test_includes_node_modules(self):
        assert "node_modules" in SKIP_DIRS

    def test_size_at_least_seven(self):
        # Documented size: 7 entries (.git, _output, _archives,
        # .ipynb_checkpoints, .lake, .claude, node_modules).
        assert len(SKIP_DIRS) >= 7


# ===========================================================================
# 4. iter_notebooks — vendored skip + _output.ipynb skip
# ===========================================================================
class TestIterNotebooks:
    """The iterator must skip vendored/archived dirs and _output.ipynb duplicates."""

    def test_yields_root_notebook(self, tmp_path):
        nb = _notebook_with_cells([_code_cell([])])
        _write_notebook(tmp_path, "family/nb.ipynb", nb)
        paths = list(iter_notebooks(tmp_path))
        assert len(paths) == 1
        assert paths[0].name == "nb.ipynb"

    def test_skips_dot_git(self, tmp_path):
        nb = _notebook_with_cells([_code_cell([])])
        _write_notebook(tmp_path, ".git/nb.ipynb", nb)
        _write_notebook(tmp_path, "nb.ipynb", nb)
        paths = list(iter_notebooks(tmp_path))
        names = {p.name for p in paths}
        assert names == {"nb.ipynb"}

    def test_skips_dot_lake(self, tmp_path):
        nb = _notebook_with_cells([_code_cell([])])
        _write_notebook(tmp_path, ".lake/packages/nb.ipynb", nb)
        _write_notebook(tmp_path, "nb.ipynb", nb)
        paths = list(iter_notebooks(tmp_path))
        names = {p.name for p in paths}
        assert names == {"nb.ipynb"}

    def test_skips_output_ipynb(self, tmp_path):
        nb = _notebook_with_cells([_code_cell([])])
        _write_notebook(tmp_path, "primary.ipynb", nb)
        _write_notebook(tmp_path, "primary_output.ipynb", nb)
        paths = list(iter_notebooks(tmp_path))
        names = {p.name for p in paths}
        assert "primary_output.ipynb" not in names
        assert "primary.ipynb" in names

    def test_skips_underscore_archives(self, tmp_path):
        nb = _notebook_with_cells([_code_cell([])])
        _write_notebook(tmp_path, "_archives/nb.ipynb", nb)
        _write_notebook(tmp_path, "nb.ipynb", nb)
        paths = list(iter_notebooks(tmp_path))
        names = {p.name for p in paths}
        assert names == {"nb.ipynb"}

    def test_skips_checkpoints(self, tmp_path):
        nb = _notebook_with_cells([_code_cell([])])
        _write_notebook(tmp_path, ".ipynb_checkpoints/nb.ipynb", nb)
        _write_notebook(tmp_path, "nb.ipynb", nb)
        paths = list(iter_notebooks(tmp_path))
        names = {p.name for p in paths}
        assert names == {"nb.ipynb"}

    def test_skips_claude_dir(self, tmp_path):
        nb = _notebook_with_cells([_code_cell([])])
        _write_notebook(tmp_path, ".claude/nb.ipynb", nb)
        _write_notebook(tmp_path, "nb.ipynb", nb)
        paths = list(iter_notebooks(tmp_path))
        names = {p.name for p in paths}
        assert names == {"nb.ipynb"}


# ===========================================================================
# 5. cell_is_risky — 8 branches
# ===========================================================================
class TestCellIsRisky:
    """Risk = cdn.plot.ly output AND no image/* fallback."""

    def test_no_outputs_returns_false(self):
        # Un-executed cell: not "risky" (the detection can't apply, no fail).
        cell = _code_cell([])
        assert cell_is_risky(cell) is False

    def test_plotly_only_returns_true(self):
        # The canonical C548-L2 risky pattern: HTML with cdn.plot.ly, no fallback.
        cell = _code_cell([_plotly_cdn_output()])
        assert cell_is_risky(cell) is True

    def test_plotly_with_png_returns_false(self):
        # Static PNG emitted alongside the Plotly HTML — has fallback.
        cell = _code_cell([_plotly_cdn_output(), _png_output()])
        assert cell_is_risky(cell) is False

    def test_plotly_with_svg_returns_false(self):
        cell = _code_cell([_plotly_cdn_output(), _svg_output()])
        assert cell_is_risky(cell) is False

    def test_plotly_with_only_text_plain_returns_true(self):
        # Plotly + plain text only — no image, still risky.
        cell = _code_cell([_plotly_cdn_output(), _plain_output()])
        assert cell_is_risky(cell) is True

    def test_png_without_plotly_returns_false(self):
        # No cdn → nothing to be risky about.
        cell = _code_cell([_png_output()])
        assert cell_is_risky(cell) is False

    def test_plain_output_returns_false(self):
        cell = _code_cell([_plain_output()])
        assert cell_is_risky(cell) is False

    def test_plotly_case_insensitive(self):
        # CDN_PATTERN is re.IGNORECASE — uppercase CDN.PLOT.LY must trigger.
        out = {
            "output_type": "display_data",
            "data": {
                "text/html": ['<SCRIPT SRC="HTTPS://CDN.PLOT.LY/foo.js"></script>'],
            },
            "metadata": {},
        }
        cell = _code_cell([out])
        assert cell_is_risky(cell) is True

    def test_plotly_compact_cdnplotly_returns_false(self):
        # cdnplotly.com (compact, no dot between cdn+plotly) is NOT caught by the
        # current regex. Documented gap: the detector scopes to the canonical
        # CDN host patterns (cdn.plot.ly, cdn.plotly).
        out = {
            "output_type": "display_data",
            "data": {
                "text/html": ['<script src="https://cdnplotly.com/foo.js"></script>'],
            },
            "metadata": {},
        }
        cell = _code_cell([out])
        assert cell_is_risky(cell) is False

    def test_malformed_outputs_returns_false(self):
        # Non-serializable outputs (e.g. unusual types) → graceful False.
        cell = _code_cell([{"unserializable": object()}])
        assert cell_is_risky(cell) is False

    def test_output_data_not_dict_returns_risky(self):
        # data field is not a dict → MIME check is skipped → if has CDN, risky.
        out = {
            "output_type": "display_data",
            "data": "not a dict but contains cdn.plot.ly",
            "metadata": {},
        }
        cell = _code_cell([out])
        assert cell_is_risky(cell) is True


# ===========================================================================
# 6. scan_notebook — per-notebook aggregation + malformed JSON
# ===========================================================================
class TestScanNotebook:
    """scan_notebook must aggregate risky cell indexes + skip malformed JSON."""

    def test_returns_empty_when_no_risky(self, tmp_path):
        nb = _notebook_with_cells([_code_cell([_png_output()])])
        p = _write_notebook(tmp_path, "safe.ipynb", nb)
        assert scan_notebook(p) == []

    def test_returns_index_of_risky_cell(self, tmp_path):
        nb = _notebook_with_cells([
            _code_cell([_png_output()]),
            _code_cell([_plotly_cdn_output()]),
            _code_cell([_png_output()]),
        ])
        p = _write_notebook(tmp_path, "mixed.ipynb", nb)
        assert scan_notebook(p) == [1]

    def test_skips_markdown_cells(self, tmp_path):
        nb = _notebook_with_cells([
            _markdown_cell("cdn.plot.ly should not flag here"),
            _code_cell([_plotly_cdn_output()]),
        ])
        p = _write_notebook(tmp_path, "mixed.ipynb", nb)
        # Markdown cell content is NOT in `outputs`, but the markdown source can
        # contain the string — verify the detector only looks at outputs (i.e.
        # the markdown cell does not produce a false positive via outputs).
        # Cell 0 is markdown (no `outputs` key), cell 1 is risky code.
        assert scan_notebook(p) == [1]

    def test_malformed_json_returns_empty(self, tmp_path, capsys):
        p = tmp_path / "broken.ipynb"
        p.write_text("{not json}", encoding="utf-8")
        assert scan_notebook(p) == []
        captured = capsys.readouterr()
        assert "WARN" in captured.err

    def test_missing_cells_key_returns_empty(self, tmp_path):
        p = tmp_path / "no_cells.ipynb"
        p.write_text(json.dumps({"metadata": {}, "nbformat": 4}), encoding="utf-8")
        assert scan_notebook(p) == []

    def test_multiple_risky_cells_indexes(self, tmp_path):
        nb = _notebook_with_cells([
            _code_cell([_plotly_cdn_output()]),
            _code_cell([_png_output()]),
            _code_cell([_plotly_cdn_output()]),
        ])
        p = _write_notebook(tmp_path, "two_risky.ipynb", nb)
        assert scan_notebook(p) == [0, 2]


# ===========================================================================
# 7. main() — argparse + output modes + CI gate
# ===========================================================================
class TestMainCli:
    """main() drives the CLI; we patch sys.argv so argparse reads our flags."""

    def _run_main(self, argv, capsys):
        """Helper: monkey-patch sys.argv, call main(), return (rc, stdout, stderr)."""
        import sys as _sys
        old_argv = _sys.argv
        try:
            _sys.argv = ["check_plotly_static_risk.py"] + argv
            rc = main()
        finally:
            _sys.argv = old_argv
        captured = capsys.readouterr()
        return rc, captured.out, captured.err

    def test_main_returns_2_when_root_missing(self, tmp_path, capsys):
        rc, out, err = self._run_main(["--root", str(tmp_path / "no-such-dir")], capsys)
        assert rc == 2
        assert "root not found" in err

    def test_main_json_empty_scan(self, tmp_path, capsys):
        empty_root = tmp_path / "empty"
        empty_root.mkdir()
        rc, out, err = self._run_main(["--root", str(empty_root), "--json"], capsys)
        assert rc == 0
        payload = json.loads(out)
        assert payload["summary"]["total_notebooks_scanned"] == 0
        assert payload["summary"]["risky_notebooks"] == 0
        assert payload["risky_cells"] == []

    def test_main_json_with_risky_cells(self, tmp_path, capsys):
        root = tmp_path / "MyIA.AI.Notebooks"
        nb = _notebook_with_cells([
            _code_cell([_plotly_cdn_output()]),
            _code_cell([_png_output()]),
        ])
        _write_notebook(root, "Infer/nb1.ipynb", nb)
        rc, out, err = self._run_main(["--root", str(root), "--json"], capsys)
        assert rc == 0
        payload = json.loads(out)
        assert payload["summary"]["total_notebooks_scanned"] == 1
        assert payload["summary"]["risky_notebooks"] == 1
        assert payload["summary"]["risky_cells_total"] == 1
        assert payload["risky_cells"][0]["cell_idx"] == 0
        assert "Infer" in payload["risky_cells"][0]["family"]

    def test_main_human_output_contains_summary(self, tmp_path, capsys):
        root = tmp_path / "MyIA.AI.Notebooks"
        nb = _notebook_with_cells([_code_cell([_plotly_cdn_output()])])
        _write_notebook(root, "Search/nb.ipynb", nb)
        rc, out, err = self._run_main(["--root", str(root)], capsys)
        assert rc == 0
        assert "# Plotly-CDN static-render risk scan" in out
        assert "Notebooks scanned: 1" in out
        assert "Notebooks risky (>=1 cell): 1" in out
        assert "Search/" in out

    def test_main_exit_risky_nb_under_threshold(self, tmp_path, capsys):
        root = tmp_path / "MyIA.AI.Notebooks"
        nb = _notebook_with_cells([_code_cell([_plotly_cdn_output()])])
        _write_notebook(root, "Infer/nb.ipynb", nb)
        rc, out, err = self._run_main(
            ["--root", str(root), "--exit-risky-nb", "5", "--json"], capsys
        )
        # 1 risky nb, threshold 5 → not exceeded, exit 0.
        assert rc == 0

    def test_main_exit_risky_nb_over_threshold(self, tmp_path, capsys):
        root = tmp_path / "MyIA.AI.Notebooks"
        nb = _notebook_with_cells([_code_cell([_plotly_cdn_output()])])
        _write_notebook(root, "Infer/nb1.ipynb", nb)
        _write_notebook(root, "Infer/nb2.ipynb", nb)
        rc, out, err = self._run_main(
            ["--root", str(root), "--exit-risky-nb", "1", "--json"], capsys
        )
        # 2 risky nb, threshold 1 → exceeded, exit 1.
        assert rc == 1
        assert "FAIL" in err

    def test_main_fix_plan_out_writes_markdown(self, tmp_path, capsys):
        root = tmp_path / "MyIA.AI.Notebooks"
        nb = _notebook_with_cells([_code_cell([_plotly_cdn_output()])])
        _write_notebook(root, "Infer/nb1.ipynb", nb)
        plan = tmp_path / "plan.md"
        rc, out, err = self._run_main(
            ["--root", str(root), "--fix-plan-out", str(plan), "--json"], capsys
        )
        assert rc == 0
        assert plan.exists()
        text = plan.read_text(encoding="utf-8")
        assert "# Fix plan — Plotly-CDN static-rendering risk (#6927)" in text
        assert "Infer/" in text
        assert "R3 atomique" in text
        # Plan header notes 1 cell.
        assert "1 cells risky total" in text


# ===========================================================================
# 8. End-to-end — tmp tree smoke test
# ===========================================================================
class TestEndToEnd:
    """Synthesized mini-repo: risky + safe notebooks + verify scan output."""

    def test_mixed_tree_scan(self, tmp_path):
        root = tmp_path / "MyIA.AI.Notebooks"
        # Risky notebook — 2 risky cells, 1 safe.
        risky_nb = _notebook_with_cells([
            _code_cell([_plotly_cdn_output()]),
            _code_cell([_png_output()]),
            _code_cell([_plotly_cdn_output()]),
        ])
        # Safe notebook — all cells have static fallback.
        safe_nb = _notebook_with_cells([
            _code_cell([_png_output()]),
            _code_cell([_png_output()]),
        ])
        # Notebook without Plotly at all.
        plain_nb = _notebook_with_cells([
            _code_cell([_plain_output()]),
        ])
        _write_notebook(root, "Infer/risky.ipynb", risky_nb)
        _write_notebook(root, "Search/safe.ipynb", safe_nb)
        _write_notebook(root, "ML/plain.ipynb", plain_nb)
        # Vendored — must be skipped.
        _write_notebook(root, ".lake/packages/vendored.ipynb", risky_nb)

        # Subprocess invocation to exercise the __main__ guard path.
        repo_root = Path(__file__).resolve().parents[3]
        script = repo_root / "scripts" / "notebook_tools" / "check_plotly_static_risk.py"
        proc = subprocess.run(
            [sys.executable, str(script), "--root", str(root), "--json"],
            capture_output=True,
            text=True,
            check=False,
        )
        assert proc.returncode == 0
        payload = json.loads(proc.stdout)
        assert payload["summary"]["total_notebooks_scanned"] == 3
        assert payload["summary"]["risky_notebooks"] == 1
        assert payload["summary"]["risky_cells_total"] == 2
        families = {rc["family"] for rc in payload["risky_cells"]}
        assert families == {"Infer"}
