"""Unit tests for the error-signature loop guard on TacticTools (#1453, cycle-99).

Background: forensic c.5496938996 (cycle-99, EPIC #1453) established two gaps
the existing guards cannot close on the dominant ``_build_check_or_revert``
hard-revert path:

  * P3 — the verbatim loop detector ``_check_tool_loop`` keys ``(tool,
    args_hash)``: six different edits with different arguments all produced
    the same ``1 errors. Reverted.`` result (Voting L338, run 1778459482),
    and the hash never repeated, so it never fired.
  * P2 — the P4 fail-streak resets on ANY successful build: the zai trace
    shows 14 fails reset by a single delta0 compile success, so the streak
    never reached cap 12.

The guard added here keys the NORMALIZED error signature (line + 60-char
message prefix per error, first 4 errors) and fires LOOP_DETECTED at >= 3
consecutive fails carrying the SAME signature. The streak resets ONLY on
signature change — never on build success — by design (P2 evasion).

These tests exercise the counter and firing semantics directly on the
internal methods — no lake build, no verifier, fully offline.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Mirror the conftest path used by the other prover test modules.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.state import ProofState, SorryContext  # noqa: E402
from prover.tools import TacticTools  # noqa: E402


def _make_tactic_tools(tmp_path):
    """Build a TacticTools against a fake .lean file (no real Lean needed)."""
    fake = tmp_path / "Fake.lean"
    body = (
        "import Mathlib.Tactic\n"
        "namespace TestSpace\n"
        + "\n".join(f"-- comment line {i}" for i in range(30))
        + "\ntheorem t : True := by\n  sorry\n"
        + "\n".join(f"-- trailing line {i}" for i in range(30))
        + "\nend TestSpace\n"
    )
    fake.write_text(body, encoding="utf-8")
    sorry_line = next(i + 1 for i, l in enumerate(body.split("\n")) if "sorry" in l)
    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=sorry_line, indentation=2,
        indent_str="  ", full_file=body,
    )
    return TacticTools(state, str(fake), sctx)


_ERR_A_BASE = "unknown identifier 'foo' in the declaration body at line start here"
ERR_A = [{"line": 12, "message": _ERR_A_BASE}]
ERR_A_NOISY = [{"line": 12, "message": _ERR_A_BASE + ", extra suffix noise past the 60-char truncation point"}]
assert len(_ERR_A_BASE) >= 60  # the differing noise must live past the prefix
ERR_B = [{"line": 34, "message": "type mismatch: expected Nat, got String"}]


def test_signature_none_on_empty_errors(tmp_path):
    tt = _make_tactic_tools(tmp_path)
    assert tt._error_signature([]) is None


def test_streak_increments_on_identical_signature(tmp_path):
    tt = _make_tactic_tools(tmp_path)
    assert tt._bump_error_signature_streak(ERR_A) == 1
    assert tt._bump_error_signature_streak(ERR_A) == 2
    assert tt._bump_error_signature_streak(ERR_A) == 3


def test_streak_resets_to_one_on_different_signature(tmp_path):
    tt = _make_tactic_tools(tmp_path)
    tt._bump_error_signature_streak(ERR_A)
    tt._bump_error_signature_streak(ERR_A)
    assert tt._bump_error_signature_streak(ERR_B) == 1


def test_streak_persists_across_build_success(tmp_path):
    """P2 evasion: a successful build between two same-signature fails must
    NOT reset the streak — only a signature change resets it."""
    tt = _make_tactic_tools(tmp_path)
    tt._bump_error_signature_streak(ERR_A)
    tt._bump_error_signature_streak(ERR_A)
    # Simulate a successful build: the success path never calls the bump.
    # (On the real path, _consecutive_compile_fail resets here — the signature
    # streak deliberately does not.)
    tt._consecutive_compile_fail = 0
    assert tt._bump_error_signature_streak(ERR_A) == 3


def test_loop_error_fires_at_threshold(tmp_path):
    tt = _make_tactic_tools(tmp_path)
    for _ in range(3):
        tt._bump_error_signature_streak(ERR_A)
    out = tt._error_signature_loop_error(ERR_A)
    assert out is not None
    assert "LOOP_DETECTED" in out["error"]
    assert out["loop_detected"] is True
    assert out["reverted"] is True


def test_loop_error_silent_below_threshold(tmp_path):
    tt = _make_tactic_tools(tmp_path)
    tt._bump_error_signature_streak(ERR_A)
    tt._bump_error_signature_streak(ERR_A)
    assert tt._error_signature_loop_error(ERR_A) is None


def test_loop_error_silent_when_signatures_alternate(tmp_path):
    """Green path: genuinely different errors (agent progressing) never fire."""
    tt = _make_tactic_tools(tmp_path)
    tt._bump_error_signature_streak(ERR_A)
    tt._bump_error_signature_streak(ERR_B)
    tt._bump_error_signature_streak(ERR_A)
    assert tt._same_error_signature_streak == 1
    assert tt._error_signature_loop_error(ERR_A) is None


def test_signature_truncates_message_noise(tmp_path):
    """Messages differing only past the 60-char prefix share one signature."""
    tt = _make_tactic_tools(tmp_path)
    assert tt._error_signature(ERR_A) == tt._error_signature(ERR_A_NOISY)
    tt._bump_error_signature_streak(ERR_A)
    assert tt._bump_error_signature_streak(ERR_A_NOISY) == 2


def test_loop_error_requires_nonempty_errors(tmp_path):
    tt = _make_tactic_tools(tmp_path)
    for _ in range(3):
        tt._bump_error_signature_streak(ERR_A)
    assert tt._error_signature_loop_error([]) is None
