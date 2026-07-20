"""Unit tests for #7477 P5a — `heartbeat_budget_exceeded` run verdict.

A Lean tactic that blows the ``maxHeartbeats`` budget is reported by Lean as a
*build error* (not a sorry), of the form::

    (deterministic) timeout at `<phase>`, maximum number of heartbeats (<N>) has been reached

Without dedicated detection such a run scored ``result_kind == no_progress`` —
indistinguishable from a tactic that simply failed. The fix has three parts,
each exercised here:

  1. ``tools._is_heartbeat_timeout`` matches the canonical Lean string (verified
     firsthand against ``lean.exe`` v4.32.0, both the ``elaborator`` and
     ``isDefEq`` phase variants).
  2. ``TacticTools.compile`` latches ``state.heartbeat_budget_exceeded`` (single
     capture site — every proof path compiles through it).
  3. ``run_prover_bg._derive_result_kind`` gains a ``heartbeat_budget_exceeded``
     branch (ranked AFTER sorry_decreased / structural_only / provider_outage /
     correctly_refused: real progress outranks the diagnostic).

Run from ``agent_tests/``::

    python -m pytest tests/test_prover_heartbeat_budget.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked (same
# bootstrap convention as tests/test_prover_correctly_refused.py).
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover import run_prover_bg  # noqa: E402
from prover.state import ProofState  # noqa: E402
from prover.tools import TacticTools, _is_heartbeat_timeout  # noqa: E402


# ──────────────────────────────────────────────────────────────────────────
# _is_heartbeat_timeout — the canonical-string detector (verified firsthand)
# ──────────────────────────────────────────────────────────────────────────

# Verbatim Lean output reproduced locally with lean.exe v4.32.0 (2026-07) under
# `set_option maxHeartbeats 1 in` + a nontrivial tactic. The <phase> and <N>
# vary; the tokens `maximum number of heartbeats` + `has been reached` do not.
_HB_ELABORATOR = (
    "(deterministic) timeout at `elaborator`, maximum number of heartbeats "
    "(1) has been reached"
)
_HB_ISDEFEQ = (
    "(deterministic) timeout at `isDefEq`, maximum number of heartbeats "
    "(1) has been reached"
)
# What the string looks like once _parse_lean_errors strips the `file:l:c: error:` prefix
# and Lake wraps it — the message field carries the heartbeat clause verbatim.
_HB_WRAPPED = (
    "Foo.lean:2:10: error: (deterministic) timeout at `simp`, maximum number "
    "of heartbeats (200000) has been reached"
)


@pytest.mark.parametrize("msg", [_HB_ELABORATOR, _HB_ISDEFEQ, _HB_WRAPPED])
def test_is_heartbeat_timeout_matches_real_strings(msg):
    """The detector matches every firsthand-reproduced Lean heartbeat string,
    regardless of the <phase> name or the <N> budget value."""
    assert _is_heartbeat_timeout(msg) is True


def test_is_heartbeat_timeout_matches_at_default_budget():
    """The real prover hits the default 200000 budget; the detector must not
    hardcode the low reproduction value (1)."""
    default = (
        "(deterministic) timeout at `simp`, maximum number of heartbeats "
        "(200000) has been reached"
    )
    assert _is_heartbeat_timeout(default) is True


@pytest.mark.parametrize("msg", [
    "",                                              # empty
    "unsolved goals",                                # normal sorry leak
    "type mismatch, application",                    # normal type error
    "maximum number of heartbeats",                  # only half the signature
    "has been reached",                              # only half the signature
    "(deterministic) timeout at `omega`",            # timeout WITHOUT heartbeats
    None,                                            # None input
])
def test_is_heartbeat_timeout_rejects_non_heartbeat(msg):
    """Non-heartbeat messages (normal errors, half-signatures, unrelated
    timeouts, empty/None) must NOT latch the flag — a false positive would hide
    a real type error behind the heartbeat diagnostic."""
    assert _is_heartbeat_timeout(msg) is False


# ──────────────────────────────────────────────────────────────────────────
# _derive_result_kind — the heartbeat_budget_exceeded branch
# ──────────────────────────────────────────────────────────────────────────


def _derive(result, final_sorry, original_sorry):
    """Thin wrapper so each test reads as the verdict for one scenario."""
    return run_prover_bg._derive_result_kind(result, final_sorry, original_sorry)


def test_heartbeat_budget_exceeded_when_flag_set():
    """A run whose result carries heartbeat_budget_exceeded=True is classified
    heartbeat_budget_exceeded, not no_progress."""
    result = {"heartbeat_budget_exceeded": True}
    assert _derive(result, final_sorry=5, original_sorry=5) == "heartbeat_budget_exceeded"


def test_heartbeat_flag_needs_truthy():
    """Flag absent or False falls through to no_progress (no false positive).
    A run that never blew the budget must NOT be mislabelled."""
    assert _derive({}, 5, 5) == "no_progress"
    assert _derive({"heartbeat_budget_exceeded": False}, 5, 5) == "no_progress"
    assert _derive({"heartbeat_budget_exceeded": None}, 5, 5) == "no_progress"


def test_sorry_decreased_outranks_heartbeat():
    """Real progress outranks the diagnostic: a run that lowered the sorry
    count before blowing the budget is still a harvest."""
    result = {"heartbeat_budget_exceeded": True}
    assert _derive(result, final_sorry=3, original_sorry=5) == "sorry_decreased"


def test_structural_progress_outranks_heartbeat():
    """A decomposition landed (structural_progress=True) before the budget
    blew: structural_only, not heartbeat_budget_exceeded."""
    result = {"heartbeat_budget_exceeded": True, "structural_progress": True}
    assert _derive(result, 5, 5) == "structural_only"


def test_provider_outage_outranks_heartbeat():
    """A provider death mid-run is provider_outage regardless of heartbeat:
    the prover never got to work."""
    result = {"heartbeat_budget_exceeded": True, "provider_outage": True}
    assert _derive(result, 5, 5) == "provider_outage"


def test_correctly_refused_outranks_heartbeat():
    """An explicit Coordinator abandon (intractable) is correctly_refused
    regardless of heartbeat — the agent refused; it did not try a tactic.
    (Ordering matches the docstring ranking: intractable is checked first.)"""
    result = {"heartbeat_budget_exceeded": True, "intractable": True}
    assert _derive(result, 5, 5) == "correctly_refused"


def test_crashed_outranks_heartbeat():
    """An explicit error is crashed regardless of heartbeat."""
    result = {"error": "kaboom", "heartbeat_budget_exceeded": True}
    assert _derive(result, 5, 5) == "crashed"


def test_heartbeat_plumbs_through_classification_from_result_fields():
    """End-to-end of the classification: a result dict shaped like the real
    provers.py return (heartbeat_budget_exceeded surfaced via getattr(state,...),
    no sorry drop, no structural progress, no outage, no intractable) classifies
    as heartbeat_budget_exceeded — the exact path a real heartbeat run takes."""
    result = {
        "success": False,
        "sorry_evolution": "5 -> 5",
        "structural_progress": False,
        "provider_outage": False,
        "provider_failures": 0,
        "intractable": False,
        "heartbeat_budget_exceeded": True,
        "iterations": 8,
    }
    assert _derive(result, final_sorry=5, original_sorry=5) == "heartbeat_budget_exceeded"


# ──────────────────────────────────────────────────────────────────────────
# TacticTools.compile — the single capture site latches state
# ──────────────────────────────────────────────────────────────────────────


def _patch_verifier_raw_output(monkeypatch, raw_output, build_success=False):
    """Mock the LeanVerifier so compile() sees ``raw_output`` without a real
    lake build (same pattern as test_prover_guards._patch_verifier_and_reverify)."""
    import prover.verifier as vmod

    class _FakeVerifier:
        def verify_project_file(self, rel, force=False):
            return {"success": build_success, "errors": "", "raw_output": raw_output}

    monkeypatch.setattr(vmod, "get_verifier", lambda *a, **k: _FakeVerifier())


def test_compile_latches_heartbeat_on_build_error(tmp_path, monkeypatch):
    """A compile() whose build log carries the heartbeat string sets
    state.heartbeat_budget_exceeded=True (the run will then classify as
    heartbeat_budget_exceeded, not no_progress)."""
    fake = tmp_path / "Target.lean"
    fake.write_text("theorem t : True := by sorry\n", encoding="utf-8")

    _patch_verifier_raw_output(
        monkeypatch, raw_output=_HB_WRAPPED, build_success=False,
    )

    state = ProofState(theorem_statement="t")
    tools = TacticTools(state=state, filepath=str(fake))
    # Drive a compile — the latch fires inside, regardless of the build verdict.
    tools.compile()

    assert state.heartbeat_budget_exceeded is True, (
        "compile() must latch heartbeat_budget_exceeded when the build log "
        "carries the Lean heartbeat signature"
    )


def test_compile_does_not_latch_on_normal_build_error(tmp_path, monkeypatch):
    """A normal type error (no heartbeat signature) must NOT latch the flag —
    guards against a detector that would fire on every failed build."""
    fake = tmp_path / "Target.lean"
    fake.write_text("theorem t : True := by sorry\n", encoding="utf-8")

    _patch_verifier_raw_output(
        monkeypatch,
        raw_output="Target.lean:1:20: error: unsolved goals\n",
        build_success=False,
    )

    state = ProofState(theorem_statement="t")
    tools = TacticTools(state=state, filepath=str(fake))
    tools.compile()

    assert state.heartbeat_budget_exceeded is False, (
        "a normal type error must not be misread as a heartbeat exhaustion"
    )


def test_compile_latches_only_once(tmp_path, monkeypatch):
    """The `not state.heartbeat_budget_exceeded` guard short-circuits repeated
    compiles — once latched, subsequent compiles do not re-enter the check.
    (Sanity: the latch is sticky, not toggling.)"""
    fake = tmp_path / "Target.lean"
    fake.write_text("theorem t : True := by sorry\n", encoding="utf-8")

    _patch_verifier_raw_output(
        monkeypatch, raw_output=_HB_WRAPPED, build_success=False,
    )

    state = ProofState(theorem_statement="t")
    tools = TacticTools(state=state, filepath=str(fake))
    tools.compile()
    assert state.heartbeat_budget_exceeded is True
    # Second compile on a CLEAN log must NOT clear the flag.
    _patch_verifier_raw_output(
        monkeypatch, raw_output="", build_success=True,
    )
    tools.compile()
    assert state.heartbeat_budget_exceeded is True, (
        "latch is sticky: a later clean compile must not clear the flag"
    )
