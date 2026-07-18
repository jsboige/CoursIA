r"""Tests for scripts/notebook_tools/detect_bare_cross_dir_load.py — #load cross-dir detector.

Why this test file exists
-------------------------
`detect_bare_cross_dir_load.py` (issue #7050, design-gate ai-01 2026-07-17) is the
canonical DETECTOR for bare `#load "X.cs"` directives whose source file does NOT
live in the notebook's own directory — the exact signature of a cross-family #load
that breaks silent headless re-exec (CS1504 -- source file not found). The gate
`bare-cross-dir-load-gate.yml` runs this detector per-PR; pinning its contract
here protects the zero-FP guarantee (docstring L26-L47).

Five clusters, mirroring the detector's documented decision logic:

  1. TestLoadRegex      -- _LOAD_RE captures #load "X" / #load @"X", ignores #r
  2. TestIsBare         -- separator detection (no / and no \)
  3. TestDetectCell     -- the 5-step decision (code / source-ext / bare / not-colocated)
  4. TestScanNotebook   -- end-to-end dict contract (path/kernel/hits/error)
  5. TestMainExitCodes  -- exit 0/1/2 contract (--check, missing file, family)

The decision to FLAG requires ALL of: code cell + `#load "X"` + X ends with
.cs/.csx/.fsx + X is bare (no separator) + X NOT co-located in the notebook dir.
Every negative case below breaks exactly one conjunct, exercising each documented
exclusion (explicit path, co-located file, non-source ext, #r reference, markdown).
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_bare_cross_dir_load import (  # noqa: E402
    _LOAD_RE,
    _colocated,
    _is_bare,
    detect_cell,
    main,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code(source) -> dict:
    """A code cell with given source (str OR list-of-str)."""
    return {"cell_type": "code", "source": source}


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": source}


def _write_nb(path: Path, cells: list[dict], kernel: str = ".net-csharp") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel, "display_name": kernel}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# _LOAD_RE -- directive capture
# ---------------------------------------------------------------------------

class TestLoadRegex:
    def test_captures_plain_load(self):
        m = _LOAD_RE.search('#load "SvgChartHelper.cs"')
        assert m is not None
        assert m.group(1) == "SvgChartHelper.cs"

    def test_captures_at_prefixed_load(self):
        # dotnet-interactive allows #load @"..." (verbatim). The @ prefix is optional.
        m = _LOAD_RE.search('#load @"SvgChartHelper.cs"')
        assert m is not None
        assert m.group(1) == "SvgChartHelper.cs"

    def test_does_not_match_reference_directive(self):
        # #r is a package/dll reference, never a #load of a source file.
        assert _LOAD_RE.search('#r "nuget:Microsoft.ML,1.0"') is None
        assert _LOAD_RE.search('#r "System.Numerics"') is None

    def test_does_not_match_unquoted_load(self):
        # #load X (no double quotes) is not the canonical dotnet-interactive form.
        assert _LOAD_RE.search("#load SvgChartHelper.cs") is None

    def test_captures_multiple_loads_in_cell(self):
        src = '#load "A.cs"\nvar x = 1;\n#load "B.cs"'
        targets = [m.group(1) for m in _LOAD_RE.finditer(src)]
        assert targets == ["A.cs", "B.cs"]


# ---------------------------------------------------------------------------
# _is_bare -- separator detection
# ---------------------------------------------------------------------------

class TestIsBare:
    def test_plain_filename_is_bare(self):
        assert _is_bare("SvgChartHelper.cs") is True
        assert _is_bare("Helper.fsx") is True

    def test_forward_slash_not_bare(self):
        assert _is_bare("helpers/Foo.cs") is False
        assert _is_bare("../Probas/Infer/SvgChartHelper.cs") is False

    def test_backslash_not_bare(self):
        # Windows separator also disqualifies bare status.
        assert _is_bare("helpers\\Foo.cs") is False

    def test_absolute_path_not_bare(self):
        assert _is_bare("/abs/path/Foo.cs") is False


# ---------------------------------------------------------------------------
# detect_cell -- the 5-step decision (all conjuncts must hold to flag)
# ---------------------------------------------------------------------------

class TestDetectCell:
    def test_bare_absent_file_flagged(self, tmp_path):
        # Canonical defect: bare #load of a .cs that is NOT in the notebook dir.
        cell = _code('#load "SvgChartHelper.cs"')
        hits = detect_cell(cell, tmp_path)  # tmp_path has no SvgChartHelper.cs
        assert len(hits) == 1
        assert hits[0]["target"] == "SvgChartHelper.cs"
        assert hits[0]["directive"] == '#load "SvgChartHelper.cs"'

    def test_at_prefixed_bare_flagged(self, tmp_path):
        cell = _code('#load @"SvgChartHelper.cs"')
        hits = detect_cell(cell, tmp_path)
        assert len(hits) == 1
        assert hits[0]["target"] == "SvgChartHelper.cs"

    def test_explicit_relative_path_not_flagged(self, tmp_path):
        # The canonical FIX (../Probas/Infer/...) carries a separator -> out of scope.
        cell = _code('#load "../Probas/Infer/SvgChartHelper.cs"')
        assert detect_cell(cell, tmp_path) == []

    def test_colocated_file_not_flagged(self, tmp_path):
        # A bare #load of a file that EXISTS in the notebook dir resolves -> legitimate.
        (tmp_path / "Helper.cs").write_text("// local helper", encoding="utf-8")
        cell = _code('#load "Helper.cs"')
        assert detect_cell(cell, tmp_path) == []

    def test_colocated_case_insensitive_not_flagged(self, tmp_path):
        # Windows FS is case-insensitive; a co-located file with a different case
        # still resolves -> must NOT be flagged (zero-FP guarantee, docstring L40-L42).
        (tmp_path / "svgcharthelper.cs").write_text("// local", encoding="utf-8")
        cell = _code('#load "SvgChartHelper.cs"')
        assert detect_cell(cell, tmp_path) == []

    def test_non_source_extension_not_flagged(self, tmp_path):
        # .dll is not a .NET source script -> out of scope.
        cell = _code('#load "Microsoft.ML.dll"')
        assert detect_cell(cell, tmp_path) == []

    def test_csx_extension_flagged(self, tmp_path):
        # .csx is a C# script source -> in scope.
        cell = _code('#load "script.csx"')
        assert len(detect_cell(cell, tmp_path)) == 1

    def test_fsx_extension_flagged(self, tmp_path):
        # .fsx is an F# script source -> in scope.
        cell = _code('#load "lib.fsx"')
        assert len(detect_cell(cell, tmp_path)) == 1

    def test_markdown_cell_not_scanned(self, tmp_path):
        # Only code cells are scanned.
        cell = _md('#load "SvgChartHelper.cs"')
        assert detect_cell(cell, tmp_path) == []

    def test_reference_directive_ignored(self, tmp_path):
        # #r is not a #load -> never flagged even if the package is absent.
        cell = _code('#r "nuget:Microsoft.ML"')
        assert detect_cell(cell, tmp_path) == []

    def test_multiple_bare_loads_in_one_cell(self, tmp_path):
        cell = _code('#load "A.cs"\n#load "B.cs"')
        hits = detect_cell(cell, tmp_path)
        assert {h["target"] for h in hits} == {"A.cs", "B.cs"}

    def test_mixed_bare_and_explicit(self, tmp_path):
        # Only the bare one is flagged; the explicit path is out of scope.
        cell = _code('#load "../lib/Ok.cs"\n#load "Broken.cs"')
        hits = detect_cell(cell, tmp_path)
        assert len(hits) == 1
        assert hits[0]["target"] == "Broken.cs"


# ---------------------------------------------------------------------------
# _colocated -- filesystem co-location (case-insensitive)
# ---------------------------------------------------------------------------

class TestColocated:
    def test_existing_file_colocated(self, tmp_path):
        (tmp_path / "Foo.cs").write_text("// x", encoding="utf-8")
        assert _colocated(tmp_path, "Foo.cs") is True

    def test_absent_file_not_colocated(self, tmp_path):
        assert _colocated(tmp_path, "Foo.cs") is False

    def test_case_insensitive_colocated(self, tmp_path):
        (tmp_path / "foo.cs").write_text("// x", encoding="utf-8")
        assert _colocated(tmp_path, "FOO.CS") is True
        assert _colocated(tmp_path, "Foo.cs") is True


# ---------------------------------------------------------------------------
# scan_notebook -- end-to-end dict contract
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_clean_notebook_no_hits(self, tmp_path):
        cells = [
            _code('#load "../Probas/Infer/SvgChartHelper.cs"'),  # explicit path
            _code('var x = 1;'),
        ]
        p = _write_nb(tmp_path / "clean.ipynb", cells)
        result = scan_notebook(p)
        assert result["error"] is None
        assert result["hits"] == []
        assert result["kernel"] == ".net-csharp"

    def test_bare_hit_with_cell_index(self, tmp_path):
        cells = [
            _code('var setup = 1;'),
            _code('#load "SvgChartHelper.cs"\nvar x = Helper.Draw();'),
        ]
        p = _write_nb(tmp_path / "broken.ipynb", cells)
        result = scan_notebook(p)
        assert result["error"] is None
        assert len(result["hits"]) == 1
        h = result["hits"][0]
        assert h["cell_index"] == 1
        assert h["target"] == "SvgChartHelper.cs"
        assert h["directive"] == '#load "SvgChartHelper.cs"'

    def test_colocated_notebook_no_hits(self, tmp_path):
        # The .cs exists next to the notebook -> legitimate, no hit.
        (tmp_path / "LocalHelper.cs").write_text("// local", encoding="utf-8")
        cells = [_code('#load "LocalHelper.cs"')]
        p = _write_nb(tmp_path / "ok.ipynb", cells)
        assert scan_notebook(p)["hits"] == []

    def test_markdown_cells_ignored(self, tmp_path):
        cells = [
            _md('# Title\n#load "X.cs" in prose'),  # markdown, not code
            _code('#load "Broken.cs"'),
        ]
        p = _write_nb(tmp_path / "mixed.ipynb", cells)
        result = scan_notebook(p)
        assert len(result["hits"]) == 1
        assert result["hits"][0]["cell_index"] == 1

    def test_unreadable_notebook_returns_error_dict(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{ not json", encoding="utf-8")
        result = scan_notebook(bad)
        assert result["error"] is not None
        assert isinstance(result["error"], str)
        assert result["hits"] == []

    def test_path_field_recorded(self, tmp_path):
        p = _write_nb(tmp_path / "named.ipynb", [_code("var x = 1;")])
        result = scan_notebook(p)
        assert result["path"] == str(p)


# ---------------------------------------------------------------------------
# main() exit codes (0 clean / 1 hit with --check / 2 error)
# ---------------------------------------------------------------------------

class TestMainExitCodes:
    def test_check_clean_exit_0(self, tmp_path):
        p = _write_nb(tmp_path / "clean.ipynb",
                      [_code('#load "../Probas/Infer/SvgChartHelper.cs"')])
        assert main([str(p), "--check"]) == 0

    def test_check_hit_exit_1(self, tmp_path):
        p = _write_nb(tmp_path / "broken.ipynb", [_code('#load "Missing.cs"')])
        assert main([str(p), "--check"]) == 1

    def test_missing_notebook_exit_2(self, tmp_path):
        assert main([str(tmp_path / "nope.ipynb")]) == 2

    def test_no_check_exits_0_even_with_hits(self, tmp_path):
        p = _write_nb(tmp_path / "broken.ipynb", [_code('#load "Missing.cs"')])
        assert main([str(p)]) == 0

    def test_json_mode_emits_valid_json(self, tmp_path, capsys):
        p = _write_nb(tmp_path / "broken.ipynb", [_code('#load "Missing.cs"')])
        rc = main([str(p), "--json"])
        out = capsys.readouterr().out
        payload = json.loads(out)
        assert payload["total_hits"] == 1
        assert payload["notebooks_scanned"] == 1
        assert rc == 0  # no --check => exit 0

    def test_family_not_found_exit_2(self, tmp_path):
        assert main(["--family", "NoSuchFamily", "--root", str(tmp_path)]) == 2
