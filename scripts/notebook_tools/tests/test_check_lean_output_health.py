"""Tests for scripts/notebook_tools/check_lean_output_health.py — lean4-wsl broken-repl output gate.

Why this test file exists
-------------------------
``check_lean_output_health.py`` (#11874 / Epic #11703) closes a gap that the
output-PRESENCE guards (``check_null_exec``, ``validate_pr_notebooks`` under
H.3/C.2) leave open: a ``lean4-wsl`` cell can carry ``execution_count != null``
AND non-empty ``outputs`` yet be a *broken* execute — when the kernel is
``REPL_STDLIB_BROKEN`` the alectryon renderer commits ``❌ Unknown identifier`` /
``❌ Unknown constant`` / ``invalid 'import' command`` while the cell "ran".
This test pins the signature matcher and the gate semantics.

Clusters:

  1. TestSignatureRegex        -- alectryon broken-repl error signatures
  2. TestScanNotebook          -- routing (lean4-wsl vs not), finding collection
  3. TestFailingCellCount      -- distinct-cell semantics behind the threshold
  4. TestRunAuditAndFail       -- end-to-end scan + --fail exit codes
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_lean_output_health import (  # noqa: E402
    _ALECTRYON_ERR_RE,
    _DEFAULT_FAIL_THRESHOLD,
    NotebookHealth,
    run_audit,
    scan_notebook,
)

_LEAN_KERNEL = "lean4-wsl"


def _notebook(cells: list[dict], kernel: str = _LEAN_KERNEL) -> dict:
    return {
        "metadata": {"kernelspec": {"name": kernel}},
        "cells": cells,
    }


def _code(source: str, outputs: list[dict] | None = None) -> dict:
    return {
        "cell_type": "code",
        "execution_count": 1,
        "metadata": {},
        "source": source.splitlines(keepends=True),
        "outputs": outputs or [],
    }


def _display(text: str) -> dict:
    sub = {
        "text/plain": text.splitlines(keepends=True),
    }
    # some alectryon outputs also carry the html render
    sub["text/html"] = sub["text/plain"]
    return {"output_type": "display_data", "data": sub}


class TestSignatureRegex:
    def test_unknown_identifier(self):
        assert _ALECTRYON_ERR_RE.search("#check Regex\n──────▶ ❌ Unknown identifier `Regex`")

    def test_unknown_constant(self):
        assert _ALECTRYON_ERR_RE.search("──────▶ ❌ Unknown constant `OfNat`")

    def test_invalid_import(self):
        assert _ALECTRYON_ERR_RE.search("──────▶ ❌ invalid 'import' command")

    def test_no_marker_still_matches(self):
        # the red-X is optional; the lean error text alone is the signal
        assert _ALECTRYON_ERR_RE.search("Unknown identifier `X`")

    def test_healthy_check_is_not_matched(self):
        assert not _ALECTRYON_ERR_RE.search("Sensitivity.Q (n : ℕ) : Type")
        assert not _ALECTRYON_ERR_RE.search("#eval 2+2")  # a real eval line


class TestScanNotebook:
    def test_non_lean_returns_none(self, tmp_path):
        nb = _notebook([_code("x")], kernel="python3")
        path = tmp_path / "fake.ipynb"
        path.write_text(json.dumps(nb), encoding="utf-8")
        assert scan_notebook(path, root=tmp_path) is None  # routed by kernel name

    def test_lean_broken_output_is_flagged(self, tmp_path):
        nb = _notebook([
            _code("#check Regex", [_display("──────▶ ❌ Unknown identifier `Regex`")]),
        ])
        p = tmp_path / "bad.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        h = scan_notebook(p, root=tmp_path)
        assert h is not None
        assert h.kernel == _LEAN_KERNEL
        assert h.findings
        assert h.failing_cell_count == 1

    def test_lean_healthy_output_is_clean(self, tmp_path):
        nb = _notebook([
            _code("#check Regex", [_display("Regex : Type")]),
        ])
        p = tmp_path / "good.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        h = scan_notebook(p, root=tmp_path)
        assert h is not None
        assert not h.findings
        assert h.healthy

    def test_multiple_matches_one_cell_counts_once(self, tmp_path):
        nb = _notebook([
            _code("#check a\n#check b", [
                _display("──────▶ ❌ Unknown identifier `a`\n──────▶ ❌ Unknown identifier `b`"),
            ]),
        ])
        p = tmp_path / "bad.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        h = scan_notebook(p, root=tmp_path)
        assert h.failing_cell_count == 1  # one distinct cell, two matches


class TestFailingCellCount:
    def test_reflects_distinct_cell_indices(self):
        h = NotebookHealth(rel_path="x", kernel=_LEAN_KERNEL, code_cells=3)
        h.failing_cell_indices = {0, 2}
        assert h.failing_cell_count == 2


class TestRunAuditAndFail:
    def test_gate_exit_with_threshold(self, tmp_path, monkeypatch):
        from check_lean_output_health import main

        bad = tmp_path / "bad.ipynb"
        nb = _notebook([_code("#check a", [_display("❌ Unknown identifier `a`")])])
        bad.write_text(json.dumps(nb), encoding="utf-8")
        # one failing cell < default threshold 2 -> diagnostic, no gate
        assert main(["--path", str(bad), "--fail"]) == 0

        # push below-threshold default but above 1 -> gate fires
        assert main(["--path", str(bad), "--fail", "--fail-threshold", "1"]) == 1

        # without --fail, always 0
        assert main(["--path", str(bad)]) == 0
