"""Unit tests for the FX-12 structural-edits counter on TacticTools (#6790 pathology 3).

Background: #6790 pathology 3 (DEMO 62 forensic) is a run that aborted after
ONE build-verified ``file_replace_lines`` (a monolithic sorry decomposed into
N compiling sub-sorries) plus several compiles and 75 trace entries, yet
reported ``iterations=0`` and ``attempts=0`` in the result dict. The cause:
``iterations`` counts tactic-submission turns (``max_iterations -
remaining_iterations``) and ``attempts`` counts ``len(tactic_history)``, and
a structural edit (file_replace_lines / file_insert_lines) touches neither.

FX-12 adds ``TacticTools._structural_edits_verified`` — a count of
build-verified structural edits (those whose build_check passed) — and
surfaces it in the MultiAgent / Autonomous result dicts as
``structural_edits``. This lets forensic ROI distinguish ``no progress at
all`` from ``structural progress without a tactic``.

These tests exercise the counter invariant directly:
  * starts at 0
  * increments iff build_check passes (NOT on build failure, NOT when skipped)
  * accumulates across multiple verified edits
  * is surfaced for both file_replace_lines and file_insert_lines

They mock ``_build_check_or_revert`` (the only Lean-dependent call) so the
tests run fully offline — no lake build required.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Mirror the conftest path used by the other prover test modules.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.state import ProofState, SorryContext  # noqa: E402
from prover.tools import TacticTools  # noqa: E402


# --- helpers ---------------------------------------------------------------


def _make_tactic_tools(tmp_path, sorry_body_lines=("  sorry",)):
    """Build a TacticTools against a fake .lean file (no real Lean needed).

    The file is padded so the file-size guard (blocks >50% deltas) does not
    fire on small single-line edits. Mirrors the ``tactic_tools`` fixture in
    test_prover_guards.py.
    """
    fake = tmp_path / "Fake.lean"
    body = (
        "import Mathlib.Tactic\n"
        "namespace TestSpace\n"
        + "\n".join(f"-- comment line {i} for size padding" for i in range(50))
        + "\ntheorem t : True := by\n"
        + "\n".join(sorry_body_lines)
        + "\n"
        + "\n".join(f"-- trailing line {i} for size padding" for i in range(50))
        + "\nend TestSpace\n"
    )
    fake.write_text(body, encoding="utf-8")
    sorry_line = next(
        i + 1 for i, line in enumerate(body.split("\n")) if "sorry" in line
    )
    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=sorry_line, indentation=2,
        indent_str="  ", full_file=body,
    )
    tt = TacticTools(state, str(fake), sctx)
    return tt, sorry_line


# --- counter initialization ------------------------------------------------


def test_counter_starts_at_zero(tmp_path):
    """A fresh TacticTools MUST initialize _structural_edits_verified to 0
    so a run that makes no structural edits reports 0, not a stale value
    from a prior run on the same instance."""
    tt, _ = _make_tactic_tools(tmp_path)
    assert getattr(tt, "_structural_edits_verified", None) == 0, (
        "_structural_edits_verified must exist and start at 0"
    )


# --- file_replace_lines counter invariant ----------------------------------


def test_counter_increments_on_build_verified_replace(tmp_path, monkeypatch):
    """file_replace_lines whose build_check PASSES MUST increment the
    counter — this is precisely the pathology-3 signal (a structural edit
    made real progress that iterations/attempts cannot see)."""
    tt, sorry_line = _make_tactic_tools(tmp_path)
    # Mock the Lean build to report success (no lake build needed).
    monkeypatch.setattr(tt, "_build_check_or_revert", lambda content, tag: None)

    out = json.loads(tt.file_replace_lines(
        start=sorry_line, end=sorry_line,
        new_content="  trivial",
        build_check=True,
    ))
    assert "error" not in out, out
    assert out["build_check"] == "passed"
    assert tt._structural_edits_verified == 1, (
        "build-verified file_replace_lines must increment the counter"
    )


def test_counter_unchanged_on_build_failure_replace(tmp_path, monkeypatch):
    """file_replace_lines whose build_check FAILS MUST NOT increment the
    counter — a reverted edit is not progress. This is the guard against
    counting smoke (non-compiling replacements) as structural progress."""
    tt, sorry_line = _make_tactic_tools(tmp_path)
    # Mock the Lean build to report FAILURE (returns an error dict, which
    # _build_check_or_revert does on compile error before reverting).
    monkeypatch.setattr(
        tt, "_build_check_or_revert",
        lambda content, tag: {"error": "compile failed: unknown identifier"},
    )
    before = tt._structural_edits_verified
    out = json.loads(tt.file_replace_lines(
        start=sorry_line, end=sorry_line,
        new_content="  not_a_tactic_xyz",
        build_check=True,
    ))
    assert "error" in out, "build-failure path must surface an error"
    assert tt._structural_edits_verified == before, (
        "build-FAILED file_replace_lines must NOT increment the counter"
    )


def test_counter_unchanged_when_build_check_skipped_replace(tmp_path):
    """file_replace_lines with build_check=False MUST NOT increment the
    counter — the increment lives inside ``if build_check:``, consistent
    with the snapshot invariant (no build = no progress recorded)."""
    tt, sorry_line = _make_tactic_tools(tmp_path)
    before = tt._structural_edits_verified
    out = json.loads(tt.file_replace_lines(
        start=sorry_line, end=sorry_line,
        new_content="  show ?a ≦ ?b -- PROBE",
        build_check=False,
    ))
    assert "error" not in out, out
    assert out["build_check"] == "skipped"
    assert tt._structural_edits_verified == before, (
        "build_check=False must NOT increment the counter (no verification)"
    )


# --- file_insert_lines counter invariant -----------------------------------


def test_counter_increments_on_build_verified_insert(tmp_path, monkeypatch):
    """file_insert_lines whose build_check PASSES MUST increment the
    counter too — inserting a helper lemma that compiles is structural
    progress (the canonical decomposition move)."""
    tt, sorry_line = _make_tactic_tools(tmp_path)
    monkeypatch.setattr(tt, "_build_check_or_revert", lambda content, tag: None)

    out = json.loads(tt.file_insert_lines(
        after_line=2,  # insert right after `namespace TestSpace`
        content="-- helper inserted by test\n",
        build_check=True,
    ))
    assert "error" not in out, out
    assert out["build_check"] == "passed"
    assert tt._structural_edits_verified == 1, (
        "build-verified file_insert_lines must increment the counter"
    )


def test_counter_unchanged_on_build_failure_insert(tmp_path, monkeypatch):
    """file_insert_lines whose build_check FAILS MUST NOT increment the
    counter — symmetric to the file_replace_lines failure invariant."""
    tt, sorry_line = _make_tactic_tools(tmp_path)
    monkeypatch.setattr(
        tt, "_build_check_or_revert",
        lambda content, tag: {"error": "compile failed: unknown identifier"},
    )
    before = tt._structural_edits_verified
    out = json.loads(tt.file_insert_lines(
        after_line=2,
        content="-- bogus insertion\n",
        build_check=True,
    ))
    assert "error" in out, "build-failure path must surface an error"
    assert tt._structural_edits_verified == before, (
        "build-FAILED file_insert_lines must NOT increment the counter"
    )


# --- accumulation ----------------------------------------------------------


def test_counter_accumulates_across_verified_edits(tmp_path, monkeypatch):
    """Multiple build-verified structural edits MUST accumulate — the
    counter is a session-total, not a per-edit flag. This is what lets
    forensic rank a run that decomposed a goal into 3 sub-sorries above
    one that made a single edit."""
    tt, sorry_line = _make_tactic_tools(tmp_path)
    monkeypatch.setattr(tt, "_build_check_or_revert", lambda content, tag: None)

    # First verified structural edit (replace the sorry).
    out1 = json.loads(tt.file_replace_lines(
        start=sorry_line, end=sorry_line,
        new_content="  have h : True := trivial",
        build_check=True,
    ))
    assert "error" not in out1, out1
    # Second verified structural edit (insert a helper lemma).
    # Re-locate a valid insertion anchor after the rewrite.
    out2 = json.loads(tt.file_insert_lines(
        after_line=2,
        content="-- second helper inserted by test\n",
        build_check=True,
    ))
    assert "error" not in out2, out2
    assert tt._structural_edits_verified == 2, (
        "two build-verified structural edits must accumulate to 2"
    )
