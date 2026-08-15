#!/usr/bin/env python3
"""Tests for solution_leak_delta (HIGH delta guard, WARN mode, See #8053).

``solution_leak_delta`` is the WARN-phase mirror of ``pip_leak_delta`` (#6314,
which IS tested — ``test_pip_leak_delta.py``). It compares two
``audit_solution_leaks.py --json`` scans and reports HIGH-severity findings
*newly introduced* by a PR. Unlike pip_leak_delta (FAIL mode, exit 1 on delta>0),
this guard runs in **WARN mode**: it lists newly-introduced HIGH findings but
**always exits 0** — the FAIL switch is gated on a detector-precision fix.

The mirror was tested; this guard was not. This suite closes that asymmetry.

Covers:
    * ``_fingerprint`` — stable identity, excludes ``context``.
    * ``_high_findings`` / ``_high_set`` — HIGH-only, dedup, missing-key robust.
    * ``main`` — delta==0 inherited tolerated (exit 0); delta>0 WARN-mode still
      exit 0 (the central contract); delta<0 (PR fixes leaks, exit 0);
      MEDIUM/LOW excluded; inherited HIGH with a changed ``context`` does NOT
      create a phantom new finding; findings grouped by path in output;
      malformed JSON / missing file → exit 2.

Run:
    pytest scripts/notebook_tools/tests/test_solution_leak_delta.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent  # scripts/notebook_tools/
sys.path.insert(0, str(SCRIPT_DIR))

import solution_leak_delta as sld  # noqa: E402


# --- fixtures / helpers ---------------------------------------------------


def _leak(
    severity: str = "HIGH",
    type_: str = "function_body_leak",
    func_name: str = "solve",
    cell_index: int = 2,
    start_line: int = 10,
    logic_lines: int = 8,
    context: str = "x = 1",
):
    """One finding dict in ``audit_solution_leaks.py --json`` shape."""
    return {
        "severity": severity,
        "type": type_,
        "func_name": func_name,
        "cell_index": cell_index,
        "start_line": start_line,
        "logic_lines": logic_lines,
        "context": context,
    }


def _audit(path_to_leaks):
    """Build a minimal audit-JSON document ``{findings: {path: [leak, ...]}}``."""
    return {"findings": {path: leaks for path, leaks in path_to_leaks}}


def _run(tmp_path: Path, base_doc, head_doc):
    base = tmp_path / "base.json"
    head = tmp_path / "head.json"
    base.write_text(json.dumps(base_doc), encoding="utf-8")
    head.write_text(json.dumps(head_doc), encoding="utf-8")
    return sld.main([str(base), str(head)])


# --- pure helpers ---------------------------------------------------------


def test_fingerprint_excludes_context():
    """``context`` (raw source lines) is excluded from the fingerprint: a
    reviewer-touched comment or whitespace tweak must NOT create a phantom
    'new' finding for the same logical leak."""
    path = "nb.ipynb"
    a = _leak(context="x = 1")
    b = _leak(context="x = 2  # reviewer added a note")
    assert sld._fingerprint(path, a) == sld._fingerprint(path, b)


def test_fingerprint_distinguishes_func_and_cell():
    path = "nb.ipynb"
    base_fp = sld._fingerprint(path, _leak(func_name="solve", cell_index=2))
    assert sld._fingerprint(path, _leak(func_name="solve", cell_index=3)) != base_fp
    assert sld._fingerprint(path, _leak(func_name="other", cell_index=2)) != base_fp


def test_high_findings_only_high():
    """Only HIGH participates in the delta; MEDIUM/LOW/FLAG are noise."""
    doc = _audit(
        [
            ("a.ipynb", [_leak(severity="HIGH"), _leak(severity="MEDIUM")]),
            ("b.ipynb", [_leak(severity="LOW"), _leak(severity="FLAG")]),
        ]
    )
    highs = list(sld._high_findings(doc))
    assert len(highs) == 1
    assert highs[0][0] == "a.ipynb"


def test_high_findings_dedups_duplicate_fingerprints():
    """The base detector can emit the same function twice (e.g. cell 47 x2);
    dedup must collapse it so it does not inflate the delta."""
    doc = _audit([("a.ipynb", [_leak(func_name="f"), _leak(func_name="f")])])
    highs = list(sld._high_findings(doc))
    assert len(highs) == 1


def test_high_findings_missing_findings_key_yields_nothing():
    """A document without a ``findings`` key is treated as empty (robust)."""
    assert list(sld._high_findings({})) == []
    assert list(sld._high_findings({"findings": {}})) == []


def test_high_set_returns_fingerprint_to_leak_map():
    doc = _audit([("a.ipynb", [_leak(func_name="f")])])
    m = sld._high_set(doc)
    assert len(m) == 1
    fp = next(iter(m))
    assert fp[0] == "a.ipynb"
    assert m[fp]["func_name"] == "f"


# --- CLI / WARN-mode contract --------------------------------------------


def test_delta_zero_inherited_tolerated_exit_0(capsys, tmp_path):
    doc = _audit([("leak.ipynb", [_leak(func_name="solve")])])
    rc = _run(tmp_path, doc, doc)
    out = capsys.readouterr().out
    assert rc == 0
    assert "new=0" in out


def test_delta_positive_warn_mode_still_exit_0(capsys, tmp_path):
    """Central contract: even with newly-introduced HIGH findings, the guard
    is WARN-only and exits 0 (FAIL switch is a future ``--fail-on-delta``
    gated on detector-precision work). Contrast pip_leak_delta, which exits 1."""
    base = _audit([("a.ipynb", [_leak(func_name="solve")])])
    head = _audit(
        [
            ("a.ipynb", [_leak(func_name="solve")]),   # inherited, unchanged
            ("new.ipynb", [_leak(func_name="answers")]),  # NEW HIGH
        ]
    )
    rc = _run(tmp_path, base, head)
    out = capsys.readouterr().out
    assert rc == 0  # WARN phase — never fails
    assert "new=1" in out
    assert "newly-introduced" in out
    assert "new.ipynb" in out
    assert "answers" in out  # func_name surfaced for reviewer


def test_delta_negative_fix_encouraged_exit_0(capsys, tmp_path):
    """HEAD fixes a leak present in BASE → delta is negative, exit 0."""
    base = _audit(
        [("a.ipynb", [_leak(func_name="f")]), ("b.ipynb", [_leak(func_name="g")])]
    )
    head = _audit([("a.ipynb", [_leak(func_name="f")])])  # b fixed
    rc = _run(tmp_path, base, head)
    out = capsys.readouterr().out
    assert rc == 0
    assert "new=0" in out


def test_medium_new_in_head_not_counted(capsys, tmp_path):
    """A newly-introduced MEDIUM finding is excluded from the delta (noise)."""
    base = _audit([("a.ipynb", [_leak(severity="HIGH", func_name="f")])])
    head = _audit(
        [
            ("a.ipynb", [_leak(severity="HIGH", func_name="f")]),
            ("new.ipynb", [_leak(severity="MEDIUM", func_name="m")]),  # excluded
        ]
    )
    rc = _run(tmp_path, base, head)
    out = capsys.readouterr().out
    assert rc == 0
    assert "new=0" in out  # MEDIUM does not count


def test_inherited_high_context_change_no_phantom_new(capsys, tmp_path):
    """An inherited HIGH whose ``context`` (raw lines) differs between BASE and
    HEAD must NOT be reported as new — ``context`` is excluded from the
    fingerprint precisely to avoid phantom deltas on comment/whitespace tweaks."""
    base = _audit([("a.ipynb", [_leak(func_name="solve", context="x = 1\n")])])
    head = _audit(
        [("a.ipynb", [_leak(func_name="solve", context="x = 1  # clarified\n")])]
    )
    rc = _run(tmp_path, base, head)
    out = capsys.readouterr().out
    assert rc == 0
    assert "new=0" in out


def test_findings_grouped_by_path(capsys, tmp_path):
    """Multiple new findings across several paths are grouped by path in the
    output (reviewer readability)."""
    base = _audit([])
    head = _audit(
        [
            ("b.ipynb", [_leak(func_name="fb")]),
            ("a.ipynb", [_leak(func_name="fa")]),
        ]
    )
    rc = _run(tmp_path, base, head)
    out = capsys.readouterr().out
    assert rc == 0
    # Paths appear grouped (sorted), each with its func_name.
    assert "new=2" in out
    assert out.index("a.ipynb") < out.index("b.ipynb")  # sorted grouping
    assert "fa" in out and "fb" in out


def test_malformed_json_exit_2(tmp_path):
    base = tmp_path / "base.json"
    head = tmp_path / "head.json"
    base.write_text("{not json", encoding="utf-8")
    head.write_text("{}", encoding="utf-8")
    assert sld.main([str(base), str(head)]) == 2


def test_missing_file_exit_2(tmp_path):
    assert sld.main([str(tmp_path / "no-base.json"), str(tmp_path / "no-head.json")]) == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
