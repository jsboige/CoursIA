"""Regression suite for ``prover.state.ProofState`` checkpoint immutability (c.732, #7477).

Background. ``save_checkpoint`` makes defensive copies of the mutable fields
(``list(self.current_proof)``, ``list(self.discovered_lemmas)``,
``list(self.plan)``, ``dict(self.sorry_goals)``) so each stored checkpoint is
an independent snapshot. ``restore_checkpoint`` historically assigned the
STORED list/dict reference directly (``self.current_proof = cp["current_proof"]``)
instead of re-copying -- so after a restore, ``self.current_proof`` WAS the
checkpoint's list object. Any subsequent mutation via the normal API
(``add_tactic_attempt`` appends to ``current_proof``; ``add_lemma`` appends to
``discovered_lemmas``; ``provers.py:1384 state.sorry_goals[k] = v``) then
corrupted the STORED checkpoint in place, and a second ``restore_checkpoint``
of the same label returned the post-mutation state instead of the snapshot.

This silently breaks the preserve/revert gate (``tools._build_check_or_revert``
relies on a checkpoint being an immutable fallback to revert to when a
candidate edit does not compile clean) -- exactly the class of subtle harness
integrity pathology the #7477 forensic catalogues.

These tests pin the contract: **a checkpoint is an immutable snapshot; restore
does not alias it; restore-then-mutate-then-restore round-trips to the
original snapshot.** G.9 non-vacuous: against the pre-fix ``restore_checkpoint``
the ``test_*_not_aliased`` cases FAIL (the stored list gains the appended
entry), so the suite genuinely guards the fix.

Stdlib-only -- imports ``ProofState`` via ``sys.path`` insert exactly like
``test_prover_guards.py`` (#7477), so it runs without the LLM stack.

Run: ``python -m pytest tests/test_state_checkpoint_aliasing.py -q``
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
# current_proof aliasing
# ---------------------------------------------------------------------------


def test_current_proof_not_aliased_after_restore():
    """After restore, appending a tactic must NOT mutate the stored checkpoint."""
    ps = _fresh_state()
    ps.current_proof.append("tactic_A")
    label = ps.save_checkpoint("cp")
    ps.restore_checkpoint(label)
    ps.add_tactic_attempt("tactic_B", success=True)  # appends to current_proof
    stored = ps._checkpoints[label]["current_proof"]
    assert stored == ["tactic_A"], (
        f"checkpoint current_proof was aliased/mutated: {stored}"
    )


def test_current_proof_roundtrip_after_mutation():
    """restore -> mutate -> restore must return the ORIGINAL snapshot."""
    ps = _fresh_state()
    ps.current_proof.append("tactic_A")
    label = ps.save_checkpoint("cp")
    ps.restore_checkpoint(label)
    ps.add_tactic_attempt("tactic_B", success=True)
    ps.current_proof.append("tactic_C")
    assert ps.restore_checkpoint(label) is True
    assert ps.current_proof == ["tactic_A"], (
        f"second restore did not return the snapshot: {ps.current_proof}"
    )


# ---------------------------------------------------------------------------
# discovered_lemmas aliasing
# ---------------------------------------------------------------------------


def test_discovered_lemmas_not_aliased_after_restore():
    """After restore, add_lemma must NOT mutate the stored checkpoint."""
    ps = _fresh_state()
    ps.add_lemma("lem1", statement="stmt1")
    label = ps.save_checkpoint("cp")
    ps.restore_checkpoint(label)
    ps.add_lemma("lem2", statement="stmt2")  # appends to discovered_lemmas
    stored = ps._checkpoints[label]["discovered_lemmas"]
    assert len(stored) == 1, f"checkpoint discovered_lemmas was aliased: {stored}"
    assert "lem1" in stored[0]
    assert not any("lem2" in s for s in stored)


# ---------------------------------------------------------------------------
# sorry_goals aliasing (mutated live by provers.py:1384)
# ---------------------------------------------------------------------------


def test_sorry_goals_not_aliased_after_restore():
    """After restore, an external sorry_goals[k]=v must NOT mutate the stored
    checkpoint (provers.py:1384 does exactly this assignment)."""
    ps = _fresh_state()
    ps.sorry_goals[5] = "goal_at_5"
    label = ps.save_checkpoint("cp")
    ps.restore_checkpoint(label)
    ps.sorry_goals[9] = "goal_at_9"  # mirrors provers.py:1384
    stored = ps._checkpoints[label]["sorry_goals"]
    assert stored == {5: "goal_at_5"}, (
        f"checkpoint sorry_goals was aliased: {stored}"
    )


# ---------------------------------------------------------------------------
# plan aliasing
# ---------------------------------------------------------------------------


def test_plan_not_aliased_after_restore():
    """After restore, appending to plan must NOT mutate the stored checkpoint."""
    ps = _fresh_state()
    ps.plan.append("step1")
    label = ps.save_checkpoint("cp")
    ps.restore_checkpoint(label)
    ps.plan.append("step2")
    stored = ps._checkpoints[label]["plan"]
    assert stored == ["step1"], f"checkpoint plan was aliased: {stored}"


# ---------------------------------------------------------------------------
# Full round-trip independence across multiple checkpoints
# ---------------------------------------------------------------------------


def test_two_checkpoints_independent():
    """Two distinct checkpoints must stay independent even when the live state
    is mutated between restores -- no cross-contamination via shared aliases."""
    ps = _fresh_state()
    ps.current_proof.append("a")
    cp1 = ps.save_checkpoint("cp1")
    ps.current_proof.append("b")
    cp2 = ps.save_checkpoint("cp2")
    # Mutate live state heavily
    ps.add_tactic_attempt("c", success=True)
    ps.add_lemma("L", statement="S")
    ps.sorry_goals[1] = "g1"
    # Both stored checkpoints must be untouched
    assert ps._checkpoints[cp1]["current_proof"] == ["a"]
    assert ps._checkpoints[cp2]["current_proof"] == ["a", "b"]
    assert ps._checkpoints[cp1]["discovered_lemmas"] == []
    assert ps._checkpoints[cp2]["discovered_lemmas"] == []
    assert ps._checkpoints[cp1]["sorry_goals"] == {}
    assert ps._checkpoints[cp2]["sorry_goals"] == {}
    # Restoring either must give its own snapshot, not the mutated live state
    ps.restore_checkpoint(cp1)
    assert ps.current_proof == ["a"]
    ps.restore_checkpoint(cp2)
    assert ps.current_proof == ["a", "b"]


# ---------------------------------------------------------------------------
# Restore of a missing checkpoint
# ---------------------------------------------------------------------------


def test_restore_missing_checkpoint_returns_false():
    """Restoring an unknown label returns False and leaves state untouched."""
    ps = _fresh_state()
    ps.current_proof.append("x")
    assert ps.restore_checkpoint("does_not_exist") is False
    assert ps.current_proof == ["x"]
