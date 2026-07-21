"""Regression suite for ``prover.state.ProofState.to_dict`` aliasing (c.735, #7477).

Background. ``to_dict`` historically returned the live mutable fields
``current_proof`` and ``discovered_lemmas`` BY REFERENCE (``"current_proof":
self.current_proof``) instead of copying them. So the dict returned by
``to_dict()`` ALIASED the live ``ProofState`` list objects: a caller doing
``d = state.to_dict(); d["current_proof"].append(x)`` would mutate the live
``state.current_proof`` in place -- silently corrupting the session state.

This is the SAME aliasing pattern class as the ``restore_checkpoint`` bug fixed
in c.732 (#7701): a method exposing ``self.<mutable>`` must copy it on the way
out, not hand back the live reference. ``get_state_snapshot(summarize=False)``
delegates to ``to_dict()``, so the exposure travelled through both entry points
(the ``summarize=True`` branch already builds a fresh dict and is unaffected).

These tests pin the contract: **``to_dict()`` returns an independent snapshot;
mutating its lists does NOT corrupt the live ``ProofState``; two calls are
independent.** G.9 non-vacuous: against the pre-fix ``to_dict`` (returning the
bare references) the ``test_*_not_aliased`` cases FAIL (the live state gains
the appended entry), so the suite genuinely guards the fix.

Stdlib-only -- imports ``ProofState`` via ``sys.path`` insert exactly like
``test_prover_guards.py`` (#7477), so it runs without the LLM stack.

Run: ``python -m pytest tests/test_to_dict_aliasing.py -q``
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked.
ROOT = Path(__file__).resolve().parents[1]  # agent_tests/
sys.path.insert(0, str(ROOT))

from prover.state import ProofState  # noqa: E402


def _fresh_state() -> ProofState:
    return ProofState(theorem_name="t", current_goal="g")


# ---------------------------------------------------------------------------
# to_dict : current_proof aliasing
# ---------------------------------------------------------------------------


def test_to_dict_current_proof_not_aliased():
    """Appending to the list returned by to_dict must NOT mutate the live state."""
    ps = _fresh_state()
    ps.add_tactic_attempt("tactic_A", success=True)  # appends current_proof
    d = ps.to_dict()
    d["current_proof"].append("INJECTED")
    assert ps.current_proof == ["tactic_A"], (
        f"live current_proof was aliased/mutated via to_dict: {ps.current_proof}"
    )


def test_to_dict_current_proof_independent_across_calls():
    """Two to_dict calls return independent lists; mutating one touches neither
    the other nor the live state."""
    ps = _fresh_state()
    ps.add_tactic_attempt("tactic_A", success=True)
    d1 = ps.to_dict()
    d2 = ps.to_dict()
    d1["current_proof"].append("X")
    assert ps.current_proof == ["tactic_A"]
    assert d2["current_proof"] == ["tactic_A"], (
        f"second to_dict was aliased to the first: {d2['current_proof']}"
    )


# ---------------------------------------------------------------------------
# to_dict : discovered_lemmas aliasing
# ---------------------------------------------------------------------------


def test_to_dict_discovered_lemmas_not_aliased():
    """Appending to the discovered_lemmas list returned by to_dict must NOT
    mutate the live state."""
    ps = _fresh_state()
    ps.add_lemma("lem1", statement="stmt1")
    d = ps.to_dict()
    d["discovered_lemmas"].append("INJECTED_LEM")
    assert "INJECTED_LEM" not in ps.discovered_lemmas, (
        f"live discovered_lemmas was aliased/mutated via to_dict: {ps.discovered_lemmas}"
    )
    assert len(ps.discovered_lemmas) == 1


# ---------------------------------------------------------------------------
# to_dict : round-trip (to_dict -> mutate returned -> to_dict = original snapshot)
# ---------------------------------------------------------------------------


def test_to_dict_roundtrip_after_mutation():
    """to_dict -> mutate the returned dict -> to_dict again must still reflect
    the live state (not the mutation applied to the first returned dict)."""
    ps = _fresh_state()
    ps.add_tactic_attempt("tactic_A", success=True)
    d = ps.to_dict()
    d["current_proof"].append("GHOST")
    d2 = ps.to_dict()
    assert d2["current_proof"] == ["tactic_A"], (
        f"second to_dict leaked the mutation: {d2['current_proof']}"
    )


# ---------------------------------------------------------------------------
# get_state_snapshot(summarize=False) delegates to to_dict -> also safe
# ---------------------------------------------------------------------------


def test_get_state_snapshot_summarize_false_not_aliased():
    """get_state_snapshot(summarize=False) returns to_dict(); the mutable lists
    must not alias the live state either."""
    ps = _fresh_state()
    ps.add_tactic_attempt("tactic_A", success=True)
    ps.add_lemma("lem1", statement="stmt1")
    snap = ps.get_state_snapshot(summarize=False)
    snap["current_proof"].append("INJECTED")
    snap["discovered_lemmas"].append("INJECTED_LEM")
    assert ps.current_proof == ["tactic_A"]
    assert "INJECTED_LEM" not in ps.discovered_lemmas


# ---------------------------------------------------------------------------
# summarize=True is a fresh dict (sanity -- already safe, unaffected by fix)
# ---------------------------------------------------------------------------


def test_get_state_snapshot_summarize_true_is_fresh():
    """The summarize=True branch builds a fresh dict of scalars + a short
    previous_tactics list-comprehension; mutating it must never reach the live
    state (this held pre-fix too -- pins it against future regressions)."""
    ps = _fresh_state()
    ps.add_tactic_attempt("tactic_A", success=True)
    snap = ps.get_state_snapshot(summarize=True)
    # summarize=True exposes no live mutable list directly, but mutate every
    # list value defensively to prove none aliases the live state.
    for v in snap.values():
        if isinstance(v, list):
            v.append("INJECTED")
    assert ps.current_proof == ["tactic_A"]
