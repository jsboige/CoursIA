"""Tests for scripts/audit/check_lean_notebook_sorry.py (#8051 scientific_review axis).

Covers the cell-level ``sorry`` tally for ``lean4-wsl`` notebooks:
  - kernel detection (lean4-wsl only; non-lean counted separately),
  - word-bounded ``sorry`` (sorryFoo / notsorry excluded),
  - comment stripping (``--`` line + ``/- ... -/`` block sorry NOT counted),
  - multi-cell aggregation, markdown cells ignored,
  - verdict classification + JSON record shape.

Uses a synthetic mini-tree (tmp_path) — no dependency on live repo state.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_lean_notebook_sorry.py"


def _load_check():
    spec = importlib.util.spec_from_file_location("check_lean_notebook_sorry", CHECK_PATH)
    mod = importlib.util.module_from_spec(spec)
    # Register before exec so pytest's dataclass/@property introspection
    # (sys.modules.get(cls.__module__)) resolves — see importlib docs.
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def _notebook(path: Path, kernel: str = "lean4-wsl", cells: list[dict] | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells or [],
        "metadata": {"kernelspec": {"name": kernel, "display_name": kernel}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": source.splitlines(keepends=True)}


def _md(text: str) -> dict:
    return {"cell_type": "markdown", "source": text.splitlines(keepends=True)}


# --------------------------------------------------------------------------- #
# kernel detection + scan_notebook
# --------------------------------------------------------------------------- #
class TestScanNotebook:
    def setup_method(self):
        self.mod = _load_check()

    def test_returns_none_for_non_lean_kernel(self, tmp_path):
        nbp = tmp_path / "PythonNB.ipynb"
        _notebook(nbp, kernel="python3", cells=[_code("sorry")])
        assert self.mod.scan_notebook(nbp) is None

    def test_detects_lean4_wsl_kernel(self, tmp_path):
        nbp = tmp_path / "LeanNB.ipynb"
        _notebook(nbp, kernel="lean4-wsl", cells=[_code("theorem t : True := by sorry")])
        result = self.mod.scan_notebook(nbp)
        assert result is not None
        assert result.kernel == "lean4-wsl"
        assert result.sorry_count == 1

    def test_rel_path_is_posix(self, tmp_path, monkeypatch):
        nbp = tmp_path / "sub" / "NB.ipynb"
        _notebook(nbp, cells=[_code("sorry")])
        monkeypatch.setattr(self.mod, "_REPO_ROOT", tmp_path)
        monkeypatch.setattr(self.mod, "_NOTEBOOKS_ROOT", tmp_path)
        result = self.mod.scan_notebook(nbp)
        assert result.rel_path == "sub/NB.ipynb"


# --------------------------------------------------------------------------- #
# sorry counting semantics (word boundary + comment stripping)
# --------------------------------------------------------------------------- #
class TestSorryCounting:
    def setup_method(self):
        self.mod = _load_check()

    def test_word_boundary_excludes_sorryfoo(self, tmp_path):
        nbp = tmp_path / "NB.ipynb"
        _notebook(nbp, cells=[_code("def sorryFoo := 1\nnotsorry")])
        assert self.mod.scan_notebook(nbp).sorry_count == 0

    def test_line_comment_sorry_not_counted(self, tmp_path):
        nbp = tmp_path / "NB.ipynb"
        _notebook(nbp, cells=[_code("-- this is sorry in a comment\ntheorem t := 1")])
        assert self.mod.scan_notebook(nbp).sorry_count == 0

    def test_block_comment_sorry_not_counted(self, tmp_path):
        nbp = tmp_path / "NB.ipynb"
        _notebook(nbp, cells=[_code("/- sorry inside block comment -/\ntheorem t := 1")])
        assert self.mod.scan_notebook(nbp).sorry_count == 0

    def test_real_sorry_tactic_counted(self, tmp_path):
        nbp = tmp_path / "NB.ipynb"
        _notebook(nbp, cells=[_code("theorem t : True := by sorry\ntheorem u : True := by sorry")])
        assert self.mod.scan_notebook(nbp).sorry_count == 2

    def test_aggregates_across_cells(self, tmp_path):
        nbp = tmp_path / "NB.ipynb"
        _notebook(nbp, cells=[_code("sorry"), _code("sorry"), _code("-- sorry")])
        result = self.mod.scan_notebook(nbp)
        assert result.sorry_count == 2
        assert result.code_cells == 3

    def test_markdown_cells_ignored(self, tmp_path):
        nbp = tmp_path / "NB.ipynb"
        _notebook(nbp, cells=[_md("We use sorry here in prose"), _code("sorry")])
        result = self.mod.scan_notebook(nbp)
        assert result.sorry_count == 1
        assert result.code_cells == 1

    def test_empty_notebook(self, tmp_path):
        nbp = tmp_path / "NB.ipynb"
        _notebook(nbp, cells=[])
        result = self.mod.scan_notebook(nbp)
        assert result.sorry_count == 0
        assert result.code_cells == 0
        assert result.verdict == "SORRY-FREE-CANDIDATE"


# --------------------------------------------------------------------------- #
# verdict classification + report aggregation
# --------------------------------------------------------------------------- #
class TestReport:
    def setup_method(self):
        self.mod = _load_check()

    def test_verdict_branches(self, tmp_path):
        nbp = tmp_path / "NB.ipynb"
        _notebook(nbp, cells=[_code("sorry")])
        assert self.mod.scan_notebook(nbp).verdict == "HAS-SORRY-DEBT"
        nbp2 = tmp_path / "NB2.ipynb"
        _notebook(nbp2, cells=[_code("theorem t := 1")])
        assert self.mod.scan_notebook(nbp2).verdict == "SORRY-FREE-CANDIDATE"

    def test_run_audit_classifies_and_skips(self, tmp_path, monkeypatch):
        _notebook(tmp_path / "lean1.ipynb", cells=[_code("sorry")])
        _notebook(tmp_path / "lean2.ipynb", cells=[_code("ok")])
        _notebook(tmp_path / "py.ipynb", kernel="python3", cells=[_code("sorry")])
        monkeypatch.setattr(self.mod, "_NOTEBOOKS_ROOT", tmp_path)
        report = self.mod.run_audit()
        assert len(report.notebooks) == 2
        assert report.skipped_nonlean == 1
        assert report.total_sorry == 1
        assert report.sorry_free_count == 1

    def test_to_dict_shape_and_ordering(self, tmp_path, monkeypatch):
        _notebook(tmp_path / "debt.ipynb", cells=[_code("sorry\nsorry")])
        _notebook(tmp_path / "free.ipynb", cells=[_code("ok")])
        monkeypatch.setattr(self.mod, "_NOTEBOOKS_ROOT", tmp_path)
        d = self.mod.run_audit().to_dict()
        assert d["scanned_lean_notebooks"] == 2
        assert d["total_sorry_cell_level"] == 2
        assert d["sorry_free_candidates"] == 1
        assert d["sorry_debt_notebooks"] == 1
        assert "NOT transitive" in d["scope"]
        assert d["notebooks"][0]["sorry_count"] >= d["notebooks"][1]["sorry_count"]  # desc order


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
class TestCLI:
    def setup_method(self):
        self.mod = _load_check()

    def test_json_flag_emits_valid_record(self, tmp_path, monkeypatch, capsys):
        _notebook(tmp_path / "lean.ipynb", cells=[_code("sorry")])
        monkeypatch.setattr(self.mod, "_NOTEBOOKS_ROOT", tmp_path)
        rc = self.mod.main(["--json"])
        out = capsys.readouterr().out
        assert rc == 0
        parsed = json.loads(out)
        assert parsed["scanned_lean_notebooks"] == 1
        assert parsed["notebooks"][0]["sorry_count"] == 1

    def test_exit_code_always_zero(self, tmp_path, monkeypatch):
        # diagnostic, not a gate: sorry-debt is acknowledged research
        _notebook(tmp_path / "debt.ipynb", cells=[_code("sorry\nsorry\nsorry")])
        monkeypatch.setattr(self.mod, "_NOTEBOOKS_ROOT", tmp_path)
        assert self.mod.main([]) == 0
