#!/usr/bin/env python3
"""Pytest suite for `scripts/notebook_tools/cell_order_ci.py`.

Per-PR cell-ordering REGRESSION gate (Epic #3240). The module compares HIGH
cell-ordering findings of a notebook between its base revision and its PR
(head) revision and fails (exit 1) only on a *regression* -- a HIGH finding
present in head that was NOT already present in base. Pre-existing HIGH
findings in legacy notebooks therefore do NOT block unrelated PRs.

The module imports `scan_notebook` from `scan_cell_ordering`; we mock it via
monkeypatch (no real notebook parsing needed) to exercise the gate's pure
set-difference logic deterministically.

Strategy:
  - high_signatures: NONE / None / missing-file / scan-error -> empty set;
    otherwise {(category, message)} filtered to severity == HIGH.
  - regressions: sorted(head - base), deterministic, base=NONE counts every
    head HIGH as a regression (new-notebook semantics).
  - main(): exit 0 on no regression, exit 1 + formatted print on regression;
    --base optional (defaults to NONE-equivalent); missing head file -> exit 0
    ("head unreadable -> nothing to gate").

G.9 honesty: bug-hunt firsthand BEFORE tests (c.534 lesson). 0 functional bug
found -- the module is clean pure set logic. Pinned as-is (honest coverage,
no fix).
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

# cell_order_ci.py does sys.path.insert on its own dir at import, but we load
# it explicitly to control the import path.
_MODULE_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(_MODULE_DIR))

import cell_order_ci as ci  # noqa: E402


def _finding(category: str, message: str, severity: str = "HIGH", cell_index: int = 0) -> dict:
    """Build a scan_notebook-style finding dict."""
    return {
        "category": category,
        "message": message,
        "severity": severity,
        "cell_index": cell_index,
    }


def _mock_scan(monkeypatch, findings: list, error: str | None = None):
    """Replace ci.scan_notebook with a stub returning the given findings/error."""
    def _fake(path: Path) -> dict:
        rep = {"path": str(path), "findings": findings}
        if error is not None:
            rep["error"] = error
        return rep
    monkeypatch.setattr(ci, "scan_notebook", _fake)


# ── high_signatures ─────────────────────────────────────────────────────────


class TestHighSignatures:
    """{(category, message)} for HIGH findings; empty for NONE/missing/error."""

    def test_none_path_returns_empty(self, monkeypatch):
        _mock_scan(monkeypatch, [_finding("c", "m")])
        assert ci.high_signatures(None) == set()

    def test_none_literal_returns_empty(self, monkeypatch):
        _mock_scan(monkeypatch, [_finding("c", "m")])
        assert ci.high_signatures("NONE") == set()

    def test_missing_file_returns_empty(self, monkeypatch, tmp_path):
        _mock_scan(monkeypatch, [_finding("c", "m")])
        assert ci.high_signatures(str(tmp_path / "does_not_exist.ipynb")) == set()

    def test_scan_error_returns_empty(self, monkeypatch, tmp_path):
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [], error="json decode failed")
        assert ci.high_signatures(str(nb)) == set()

    def test_filters_to_high_severity_only(self, monkeypatch, tmp_path):
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [
            _finding("section_order", "S1 before S2", severity="HIGH"),
            _finding("exercise_order", "Exo before course", severity="MEDIUM"),
            _finding("consecutive_code", "two code cells", severity="LOW"),
        ])
        out = ci.high_signatures(str(nb))
        assert out == {("section_order", "S1 before S2")}

    def test_returns_category_message_tuples(self, monkeypatch, tmp_path):
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [
            _finding("section_order", "S3 before S1"),
            _finding("exercise_order", "Exo 2 before Exo 1"),
        ])
        out = ci.high_signatures(str(nb))
        assert out == {
            ("section_order", "S3 before S1"),
            ("exercise_order", "Exo 2 before Exo 1"),
        }

    def test_no_findings_returns_empty(self, monkeypatch, tmp_path):
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [])
        assert ci.high_signatures(str(nb)) == set()


# ── regressions ─────────────────────────────────────────────────────────────


class TestRegressions:
    """Sorted head - base; base=NONE => every head HIGH is a regression."""

    def test_empty_head_empty_base_no_regressions(self, monkeypatch, tmp_path):
        _mock_scan(monkeypatch, [])
        assert ci.regressions(str(tmp_path / "a.ipynb"), str(tmp_path / "b.ipynb")) == []

    def test_head_subset_of_base_no_regressions(self, monkeypatch, tmp_path):
        # Pre-existing HIGH in base -> not a regression even if in head.
        nb_a = tmp_path / "a.ipynb"
        nb_a.write_text("{}")
        nb_b = tmp_path / "b.ipynb"
        nb_b.write_text("{}")
        calls = {"a": 0, "b": 0}

        def _fake(path: Path) -> dict:
            key = "a" if path.name == "a.ipynb" else "b"
            calls[key] += 1
            return {"path": str(path), "findings": [_finding("c", "pre-existing")]}
        monkeypatch.setattr(ci, "scan_notebook", _fake)
        assert ci.regressions(str(nb_a), str(nb_b)) == []

    def test_new_high_in_head_is_regression(self, monkeypatch, tmp_path):
        nb_a = tmp_path / "a.ipynb"  # base
        nb_a.write_text("{}")
        nb_b = tmp_path / "b.ipynb"  # head
        nb_b.write_text("{}")

        def _fake(path: Path) -> dict:
            if path.name == "b.ipynb":
                return {"path": str(path), "findings": [_finding("c", "NEW bug")]}
            return {"path": str(path), "findings": []}
        monkeypatch.setattr(ci, "scan_notebook", _fake)
        assert ci.regressions(str(nb_a), str(nb_b)) == [("c", "NEW bug")]

    def test_base_none_all_head_high_are_regressions(self, monkeypatch, tmp_path):
        # New notebook (no base): every HIGH finding counts as a regression.
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [_finding("c1", "m1"), _finding("c2", "m2")])
        out = ci.regressions(None, str(nb))
        assert out == [("c1", "m1"), ("c2", "m2")]

    def test_result_is_sorted_deterministic(self, monkeypatch, tmp_path):
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        # Insert in non-sorted order to verify sorted output.
        _mock_scan(monkeypatch, [
            _finding("zeta", "zz"),
            _finding("alpha", "aa"),
            _finding("mid", "mm"),
        ])
        out = ci.regressions(None, str(nb))
        assert out == [("alpha", "aa"), ("mid", "mm"), ("zeta", "zz")]

    def test_duplicate_findings_collapsed(self, monkeypatch, tmp_path):
        # Set semantics: the same (category, message) twice -> one entry.
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [
            _finding("c", "dup"),
            _finding("c", "dup"),
        ])
        assert ci.regressions(None, str(nb)) == [("c", "dup")]


# ── main() ──────────────────────────────────────────────────────────────────


class TestMain:
    """CLI exit codes: 0 clean / nothing-to-gate, 1 on regression."""

    def test_no_regression_exit_0(self, monkeypatch, tmp_path, capsys):
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [])
        rc = ci.main(["--head", str(nb)])
        assert rc == 0
        assert "REGRESSION" not in capsys.readouterr().out

    def test_regression_exit_1_and_prints_findings(self, monkeypatch, tmp_path, capsys):
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [_finding("section_order", "S2 before S1")])
        rc = ci.main(["--base", "NONE", "--head", str(nb)])
        assert rc == 1
        out = capsys.readouterr().out
        assert "REGRESSION" in out
        assert "1 new HIGH" in out
        assert "[section_order]" in out
        assert "S2 before S1" in out

    def test_base_none_literal_new_notebook(self, monkeypatch, tmp_path):
        # --base NONE: all HIGH in head count (new-notebook semantics).
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [_finding("c", "m")])
        assert ci.main(["--base", "NONE", "--head", str(nb)]) == 1

    def test_missing_head_file_exit_0(self, monkeypatch, tmp_path):
        # Docstring: "head unreadable -> nothing to gate -> exit 0".
        _mock_scan(monkeypatch, [_finding("c", "m")])
        rc = ci.main(["--head", str(tmp_path / "ghost.ipynb")])
        assert rc == 0

    def test_pre_existing_high_not_a_regression(self, monkeypatch, tmp_path, capsys):
        # Same HIGH in base and head -> exit 0 (the core regression-gate promise).
        nb_base = tmp_path / "base.ipynb"
        nb_base.write_text("{}")
        nb_head = tmp_path / "head.ipynb"
        nb_head.write_text("{}")

        def _fake(path: Path) -> dict:
            return {"path": str(path), "findings": [_finding("c", "legacy bug")]}
        monkeypatch.setattr(ci, "scan_notebook", _fake)
        rc = ci.main(["--base", str(nb_base), "--head", str(nb_head)])
        assert rc == 0
        assert "REGRESSION" not in capsys.readouterr().out

    def test_head_required_argument(self):
        # argparse should error if --head is missing.
        with pytest.raises(SystemExit) as exc:
            ci.main([])
        # argparse exits with code 2 on missing required args.
        assert exc.value.code == 2

    def test_multiple_new_regressions_counted(self, monkeypatch, tmp_path, capsys):
        nb = tmp_path / "nb.ipynb"
        nb.write_text("{}")
        _mock_scan(monkeypatch, [_finding("c1", "m1"), _finding("c2", "m2"), _finding("c3", "m3")])
        rc = ci.main(["--head", str(nb)])
        assert rc == 1
        out = capsys.readouterr().out
        assert "3 new HIGH" in out
