"""Unit tests for #7477 P5a-search — `reasoning_budget_exceeded` run verdict.

The search-twin of ``heartbeat_budget_exceeded`` (P5a, #7548). Where the
heartbeat verdict captures a *compile-level* wall (a Lean tactic blew
``maxHeartbeats`` during a single build), this captures the *session-level*
wall: the agent loop burned its whole reasoning wall-clock
(``max_session_seconds`` / ``workflow_timeout_s``) without converging on an
edit — typically Search-phase reasoning that never emitted an attempt.

Forensic evidence (jsboige A-B, 2026-07-20): on DEMO 62 ``ne`` arm
(``HashlifeCorrectness.lean:3193``), ``moonshotai/kimi-k3`` run ``bt56gsv78``
scored 8->8 with **0 attempts** and a "reasoning-budget timeout 1800s en phase
Search". Without a typed verdict such a run was indistinguishable from
``no_progress`` (a tactic that simply failed). The fix:

  1. ``ProofState.reasoning_budget_exceeded`` (state.py) — the latch flag.
  2. ``provers.py`` sets it in BOTH the multi-agent ``except
     _asyncio.TimeoutError`` (the "Workflow reasoning-budget timeout" path)
     and the autonomous ``WALL-CLOCK CAP`` branch — the two session-level
     reasoning wall-clock capture sites.
  3. The result dict surfaces it (both the multi-agent and autonomous return
     paths) so ``run_prover_bg._derive_result_kind`` can classify it.

These tests exercise the classification contract (the part that matters for
forensic ROI) and the field default. The latch itself is driven by the BG
integration runs (kimi-k3 ``bt56gsv78`` is the firsthand reproduction); the
session-supervisor loop that hosts it is not a clean unit so it is not
mocked here, mirroring how the heartbeat latch is the one exercised by real
``compile()`` calls.

Run from ``agent_tests/``::

    python -m pytest tests/test_prover_reasoning_budget.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked (same
# bootstrap convention as tests/test_prover_heartbeat_budget.py).
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover import run_prover_bg  # noqa: E402
from prover.state import ProofState  # noqa: E402


# ──────────────────────────────────────────────────────────────────────────
# _derive_result_kind — the reasoning_budget_exceeded branch
# ──────────────────────────────────────────────────────────────────────────


def _derive(result, final_sorry, original_sorry):
    """Thin wrapper so each test reads as the verdict for one scenario."""
    return run_prover_bg._derive_result_kind(result, final_sorry, original_sorry)


def test_reasoning_budget_exceeded_when_flag_set():
    """A run whose result carries reasoning_budget_exceeded=True is classified
    reasoning_budget_exceeded, not no_progress."""
    result = {"reasoning_budget_exceeded": True}
    assert _derive(result, final_sorry=5, original_sorry=5) == "reasoning_budget_exceeded"


def test_reasoning_flag_needs_truthy():
    """Flag absent or False falls through to no_progress (no false positive).
    A run that never burned the budget must NOT be mislabelled."""
    assert _derive({}, 5, 5) == "no_progress"
    assert _derive({"reasoning_budget_exceeded": False}, 5, 5) == "no_progress"
    assert _derive({"reasoning_budget_exceeded": None}, 5, 5) == "no_progress"


def test_sorry_decreased_outranks_reasoning():
    """Real progress outranks the diagnostic: a run that lowered the sorry
    count before the session timed out is still a harvest."""
    result = {"reasoning_budget_exceeded": True}
    assert _derive(result, final_sorry=3, original_sorry=5) == "sorry_decreased"


def test_structural_progress_outranks_reasoning():
    """A decomposition landed (structural_progress=True) before the budget
    burned: structural_only, not reasoning_budget_exceeded."""
    result = {"reasoning_budget_exceeded": True, "structural_progress": True}
    assert _derive(result, 5, 5) == "structural_only"


def test_provider_outage_outranks_reasoning():
    """A provider death mid-run is provider_outage regardless of the reasoning
    wall: the prover never got to work."""
    result = {"reasoning_budget_exceeded": True, "provider_outage": True}
    assert _derive(result, 5, 5) == "provider_outage"


def test_correctly_refused_outranks_reasoning():
    """An explicit Coordinator abandon (intractable) is correctly_refused
    regardless of the reasoning wall — the agent refused; it did not spin."""
    result = {"reasoning_budget_exceeded": True, "intractable": True}
    assert _derive(result, 5, 5) == "correctly_refused"


def test_heartbeat_outranks_reasoning():
    """A compile-level heartbeat wall (Lean tactic blew maxHeartbeats) is more
    specific than a session-level reasoning wall, so heartbeat_budget_exceeded
    wins when both flags are set. (The agent got a tactic to the compiler AND
    the session later timed out — the actionable signal is the compile wall.)"""
    result = {
        "reasoning_budget_exceeded": True,
        "heartbeat_budget_exceeded": True,
    }
    assert _derive(result, 5, 5) == "heartbeat_budget_exceeded"


def test_decomposition_regression_outranks_reasoning():
    """An unverified sorry-spray (P3 decomposition_regression) is a more
    specific pathology than the generic session reasoning wall, so it wins
    when both flags are set."""
    result = {
        "reasoning_budget_exceeded": True,
        "decomposition_regression": True,
    }
    assert _derive(result, 5, 5) == "decomposition_regression"


def test_crashed_outranks_reasoning():
    """An explicit error is crashed regardless of the reasoning wall."""
    result = {"error": "kaboom", "reasoning_budget_exceeded": True}
    assert _derive(result, 5, 5) == "crashed"


def test_reasoning_plumbs_through_classification_from_result_fields():
    """End-to-end of the classification: a result dict shaped like the real
    provers.py return (reasoning_budget_exceeded surfaced via getattr(state,...),
    no sorry drop, no structural progress, no outage, no intractable, no
    heartbeat, no decomposition regression) classifies as
    reasoning_budget_exceeded — the exact path a real reasoning-wall run takes."""
    result = {
        "success": False,
        "sorry_evolution": "5 -> 5",
        "structural_progress": False,
        "provider_outage": False,
        "provider_failures": 0,
        "intractable": False,
        "heartbeat_budget_exceeded": False,
        "decomposition_regression": False,
        "reasoning_budget_exceeded": True,
        "iterations": 0,
        "attempts": 0,
    }
    assert _derive(result, final_sorry=5, original_sorry=5) == "reasoning_budget_exceeded"


# ──────────────────────────────────────────────────────────────────────────
# ProofState — the latch field
# ──────────────────────────────────────────────────────────────────────────


def test_proofstate_reasoning_budget_exceeded_defaults_false():
    """A fresh ProofState must default reasoning_budget_exceeded=False so a run
    that never hit the session wall is not mislabelled. (Mirrors the heartbeat
    field default.)"""
    state = ProofState(theorem_statement="t")
    assert state.reasoning_budget_exceeded is False
    # The heartbeat sibling is present too — guards against a rename that would
    # silently break the ranking test above.
    assert state.heartbeat_budget_exceeded is False


def test_proofstate_reasoning_budget_exceeded_is_settable():
    """The field is settable by the session-supervisor latch (the multi-agent
    `except _asyncio.TimeoutError` / autonomous WALL-CLOCK CAP branches set
    `state.reasoning_budget_exceeded = True`). Sanity that the attribute is
    writable, not a read-only property."""
    state = ProofState(theorem_statement="t")
    state.reasoning_budget_exceeded = True
    assert state.reasoning_budget_exceeded is True
