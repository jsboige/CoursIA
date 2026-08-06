#!/usr/bin/env python3
"""Tests for exercise_leak_delta (HIGH delta guard, FAIL mode, See #8053).

``exercise_leak_delta`` is the **third member of the delta-guard family**, wired
into the pre-merge CI gate ``exercise-leak-ci.yml`` (L70-72, "Fail if HIGH delta
> 0"). It compares two ``detect_solution_leaks.py --scan-all`` **text** captures
(BASE vs HEAD) and fails a PR only when it *introduces* new HIGH-severity
exercise-leak occurrences. Inherited leaks (48 HIGH + 27 MEDIUM on origin/main)
are tolerated so the gate never freezes the cluster.

Family map (delta guards over the solution/pip leak scanners):

    * ``pip_leak_delta``        (#6314) FAIL mode, JSON   — tested
    * ``solution_leak_delta``   (#8053) WARN mode, JSON   — tested (c.991, #8876)
    * ``exercise_leak_delta``   (#8053) FAIL mode, TEXT   — THIS suite (was untested)

The distinguishing contract vs its WARN-mode sibling ``solution_leak_delta``:
this guard is **FAIL mode** — a positive HIGH delta exits 1 and blocks the PR
(contrast ``solution_leak_delta``, which is WARN-only and always exits 0). The
FAIL switch there is a future ``--fail-on-delta``; here it ships today, so
locking the exit-1 behaviour is the suite's primary purpose.

A second nuance locked here: the gate keys on **HIGH only**. MEDIUM and error
deltas are parsed and surfaced in the summary line but never change the exit
code — a PR that adds MEDIUM/ERROR noise while keeping HIGH flat still passes.

Input format: unlike the JSON-consuming pip/solution siblings, this guard parses
the detector's free-text summary line ``Results: X HIGH (leaks), Y MEDIUM
(duplicates), Z errors`` (the detector does not yet expose ``--json``).

Covers:
    * ``parse_counts`` / ``_first_results_line`` — canonical parse, first-line
      selection, missing-line / malformed-schema ValueError, surrounding-text
      tolerance.
    * ``main`` — delta==0 inherited tolerated (exit 0); **delta>0 FAIL-mode
      exit 1** (central contract) and stderr names count + fix guidance;
      delta<0 (PR fixes leaks, exit 0); MEDIUM-delta-alone exit 0 (HIGH-only
      gating); error-delta-alone exit 0; unreadable file exit 2; unparseable
      (no Results line) exit 2; malformed schema exit 2.

Run:
    pytest scripts/notebook_tools/tests/test_exercise_leak_delta.py
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent  # scripts/notebook_tools/
sys.path.insert(0, str(SCRIPT_DIR))

import exercise_leak_delta as eld  # noqa: E402


# --- fixtures / helpers ---------------------------------------------------


def _detector_stdout(
    high: int = 48,
    medium: int = 27,
    errors: int = 0,
    *,
    with_preamble: bool = True,
):
    """A realistic ``detect_solution_leaks.py --scan-all`` stdout capture, ending
    in the canonical ``Results:`` summary line the guard parses."""
    lines = []
    if with_preamble:
        lines += [
            "Scanning notebooks for exercise-leak regressions...",
            "Some/Notebook.ipynb: cell 5 HIGH (function body leak)",
            "Other/Notebook.ipynb: cell 2 MEDIUM (duplicate)",
        ]
    lines.append(
        f"Results: {high} HIGH (leaks), {medium} MEDIUM (duplicates), {errors} errors"
    )
    return "\n".join(lines) + "\n"


def _results_line(high: int, medium: int, errors: int) -> str:
    """Bare canonical summary line (no preamble)."""
    return f"Results: {high} HIGH (leaks), {medium} MEDIUM (duplicates), {errors} errors\n"


def _run(tmp_path: Path, base_text: str, head_text: str):
    base = tmp_path / "base.txt"
    head = tmp_path / "head.txt"
    base.write_text(base_text, encoding="utf-8")
    head.write_text(head_text, encoding="utf-8")
    return eld.main([str(base), str(head)])


# --- pure helpers ---------------------------------------------------------


def test_parse_counts_canonical():
    """Canonical summary line parses to (high, medium, errors)."""
    assert eld.parse_counts(_results_line(48, 27, 0)) == (48, 27, 0)
    assert eld.parse_counts(_results_line(0, 0, 0)) == (0, 0, 0)
    assert eld.parse_counts(_results_line(3, 5, 2)) == (3, 5, 2)


def test_parse_counts_tolerates_surrounding_text():
    """The ``Results:`` line is found amid multi-line detector stdout."""
    assert eld.parse_counts(_detector_stdout(high=48, medium=27, errors=0)) == (48, 27, 0)


def test_first_results_line_returns_first_match():
    """``_first_results_line`` returns the FIRST line starting with ``Results:``
    even if a later line also does — ``parse_counts`` then applies the schema
    regex to that first line."""
    text = (
        "Results: 10 HIGH (leaks), 1 MEDIUM (duplicates), 0 errors\n"
        "Results: 99 HIGH (leaks), 99 MEDIUM (duplicates), 99 errors\n"
    )
    assert eld._first_results_line(text) is not None
    # parse_counts uses the FIRST Results line → (10, 1, 0), not (99, 99, 99).
    assert eld.parse_counts(text) == (10, 1, 0)


def test_parse_counts_missing_results_line_raises():
    """No ``Results:`` line at all → ValueError (the detector output format may
    have drifted)."""
    with pytest.raises(ValueError):
        eld.parse_counts("just some stdout\nno summary here\n")


def test_parse_counts_malformed_schema_raises():
    """A ``Results:`` line that does not match the exact schema → ValueError."""
    with pytest.raises(ValueError):
        eld.parse_counts("Results: lots of HIGH and some MEDIUM, plus errors\n")


# --- CLI / FAIL-mode contract --------------------------------------------


def test_delta_zero_inherited_tolerated_exit_0(capsys, tmp_path):
    """BASE == HEAD → delta 0, inherited HIGH tolerated, exit 0."""
    rc = _run(tmp_path, _detector_stdout(48, 27, 0), _detector_stdout(48, 27, 0))
    out = capsys.readouterr().out
    assert rc == 0
    assert "Δhigh=+0" in out
    assert "OK" in out and "no new HIGH" in out


def test_delta_positive_fail_mode_exit_1(capsys, tmp_path):
    """**Central contract**: HEAD introduces new HIGH → FAIL mode, exit 1, stderr
    names the count + content-based fix guidance. Contrast solution_leak_delta
    (WARN mode, exit 0) — the FAIL switch ships today on this guard."""
    rc = _run(tmp_path, _detector_stdout(48, 27, 0), _detector_stdout(50, 27, 0))
    captured = capsys.readouterr()
    assert rc == 1  # FAIL mode — blocks the PR
    assert "Δhigh=+2" in captured.out
    assert "FAIL" in captured.err
    assert "2 new HIGH" in captured.err
    # Content-based fix guidance is surfaced (relabel vs stub, cf labeling rule).
    assert "Exemple guide" in captured.err or "stub" in captured.err


def test_delta_negative_fix_encouraged_exit_0(capsys, tmp_path):
    """HEAD drains HIGH vs BASE (PR fixes leaks) → delta negative, exit 0."""
    rc = _run(tmp_path, _detector_stdout(50, 27, 0), _detector_stdout(48, 27, 0))
    out = capsys.readouterr().out
    assert rc == 0
    assert "Δhigh=-2" in out


def test_medium_delta_alone_does_not_fail(capsys, tmp_path):
    """HIGH flat, MEDIUM up → still exit 0. The gate keys on HIGH only; MEDIUM
    is parsed and surfaced but never gates."""
    rc = _run(
        tmp_path,
        _detector_stdout(high=48, medium=27, errors=0),
        _detector_stdout(high=48, medium=40, errors=0),
    )
    out = capsys.readouterr().out
    assert rc == 0
    assert "Δmedium=+13" in out  # surfaced in the summary line...


def test_error_delta_alone_does_not_fail(capsys, tmp_path):
    """HIGH flat, error count up → still exit 0. Errors are surfaced but do not
    gate (only HIGH can fail the PR)."""
    rc = _run(
        tmp_path,
        _detector_stdout(high=48, medium=27, errors=0),
        _detector_stdout(high=48, medium=27, errors=5),
    )
    out = capsys.readouterr().out
    assert rc == 0
    assert "Δerror=+5" in out


def test_unreadable_file_exit_2(tmp_path):
    """A missing/unreadable input file → exit 2 (guard degrades loudly, never
    silently passes)."""
    rc = eld.main([str(tmp_path / "no-base.txt"), str(tmp_path / "no-head.txt")])
    assert rc == 2


def test_unparseable_no_results_line_exit_2(tmp_path):
    """Readable file but no ``Results:`` line (detector format drift) → exit 2,
    not a silent pass/fail."""
    base = tmp_path / "base.txt"
    head = tmp_path / "head.txt"
    base.write_text("Results: 48 HIGH (leaks), 27 MEDIUM (duplicates), 0 errors\n", encoding="utf-8")
    head.write_text("detector crashed, no summary\n", encoding="utf-8")
    assert eld.main([str(base), str(head)]) == 2


def test_malformed_schema_exit_2(tmp_path):
    """A ``Results:`` line that fails the schema regex → exit 2 (treated as
    unparseable, not a false OK)."""
    base = tmp_path / "base.txt"
    head = tmp_path / "head.txt"
    base.write_text("Results: 48 HIGH (leaks), 27 MEDIUM (duplicates), 0 errors\n", encoding="utf-8")
    head.write_text("Results: many HIGH, some MEDIUM, few errors\n", encoding="utf-8")
    assert eld.main([str(base), str(head)]) == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
