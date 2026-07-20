"""Unit tests for #7477 P3 — ``decomposition_regression`` run verdict.

A net-sorry-INCREASE decomposition with ZERO build-verified tactics (runaway
sub-sorry spraying) was previously mis-labelled ``structural_progress`` by the
multi-agent path (founder L2551 grew 4->8 with ``verified_tactic_count==0``
across 11 dedup'd runs). The fix has two parts:

  1. ``provers.MultiAgentSorryProver`` classifies the outcome via
     ``is_decomposition_regression(final, original, verified)`` (pure helper in
     ``prover/decomposition_regression.py``, exercised by
     ``tests/test_decomposition_regression.py``) and, on a regression, forces
     ``structural_progress = False`` + sets the ``decomposition_regression``
     flag on the result dict.
  2. ``run_prover_bg._derive_result_kind`` gains a ``decomposition_regression``
     branch (ranked AFTER sorry_decreased / structural_only / provider_outage /
     correctly_refused / heartbeat_budget_exceeded: real progress and the other
     forensic siblings outrank it) so the forensic harvest ranks these runs
     honestly instead of letting them fall through to ``no_progress``.

This module locks in part 2 — the ``_derive_result_kind`` branch — and the
HARD invariant (mandate user forensic #7477): the result_kinds **coexist**,
no resolution clobbers a sibling. The classification logic itself (part 1) is
covered by ``test_decomposition_regression.py``.

Run from ``agent_tests/``::

    python -m pytest tests/test_prover_decomposition_regression.py -q

Requires the prover stack (``agent-framework-openai``) — same collection
contract as ``tests/test_prover_heartbeat_budget.py``. See #7477 (forensic),
#1453 (prover co-evolution epic).
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


# ──────────────────────────────────────────────────────────────────────────
# _derive_result_kind — the decomposition_regression branch
# ──────────────────────────────────────────────────────────────────────────


def _derive(result, final_sorry, original_sorry):
    """Thin wrapper so each test reads as the verdict for one scenario."""
    return run_prover_bg._derive_result_kind(result, final_sorry, original_sorry)


def test_decomposition_regression_when_flag_set():
    """A run whose result carries decomposition_regression=True (final > original,
    verified==0 — set by provers.py via is_decomposition_regression) is classified
    decomposition_regression, not no_progress."""
    result = {"decomposition_regression": True}
    assert _derive(result, final_sorry=8, original_sorry=4) == "decomposition_regression"


def test_decomposition_regression_flag_needs_truthy():
    """Flag absent or False falls through to no_progress (no false positive).
    A legitimate decomposition or a plain stall must NOT be mislabelled."""
    assert _derive({}, 8, 4) == "no_progress"
    assert _derive({"decomposition_regression": False}, 8, 4) == "no_progress"
    assert _derive({"decomposition_regression": None}, 8, 4) == "no_progress"


def test_sorry_decreased_outranks_decomposition_regression():
    """Real progress outranks the diagnostic: a run that lowered the sorry count
    is still a harvest even if the regression flag was somehow set."""
    result = {"decomposition_regression": True}
    assert _derive(result, final_sorry=3, original_sorry=5) == "sorry_decreased"


def test_structural_progress_outranks_decomposition_regression():
    """A verified decomposition landed (structural_progress=True) — structural_only.
    In practice the P3 guard forces structural_progress=False on a regression, so
    these are mutually exclusive; the ranking still holds if both were set."""
    result = {"decomposition_regression": True, "structural_progress": True}
    assert _derive(result, 8, 4) == "structural_only"


def test_provider_outage_outranks_decomposition_regression():
    """A provider death mid-run is provider_outage regardless of regression flag:
    the prover never got to work."""
    result = {"decomposition_regression": True, "provider_outage": True}
    assert _derive(result, 8, 4) == "provider_outage"


def test_correctly_refused_outranks_decomposition_regression():
    """An explicit Coordinator abandon (intractable) is correctly_refused
    regardless of the regression flag — the agent refused; it did not spray."""
    result = {"decomposition_regression": True, "intractable": True}
    assert _derive(result, 8, 4) == "correctly_refused"


def test_heartbeat_budget_exceeded_outranks_decomposition_regression():
    """A Lean tactic that blew the maxHeartbeats budget (heartbeat_budget_exceeded)
    outranks decomposition_regression — the sibling is checked first. This is the
    HARD invariant: the P3 branch does NOT clobber the P5a sibling (#7477)."""
    result = {"decomposition_regression": True, "heartbeat_budget_exceeded": True}
    assert _derive(result, 8, 4) == "heartbeat_budget_exceeded"


def test_crashed_outranks_decomposition_regression():
    """An explicit error is crashed regardless of the regression flag."""
    result = {"error": "kaboom", "decomposition_regression": True}
    assert _derive(result, 8, 4) == "crashed"


# ──────────────────────────────────────────────────────────────────────────
# HARD invariant — siblings preserved (no clobber), 4 branches coexist
# ──────────────────────────────────────────────────────────────────────────


def test_correctly_refused_sibling_still_works():
    """The P2a sibling (correctly_refused) is untouched by the P3 branch:
    a run with only intractable=True still classifies correctly_refused."""
    assert _derive({"intractable": True}, 5, 5) == "correctly_refused"


def test_heartbeat_budget_sibling_still_works():
    """The P5a sibling (heartbeat_budget_exceeded) is untouched by the P3 branch:
    a run with only heartbeat_budget_exceeded=True still classifies as such."""
    assert _derive({"heartbeat_budget_exceeded": True}, 5, 5) == "heartbeat_budget_exceeded"


def test_four_forensic_siblings_coexist():
    """The 4 forensic result_kinds coexist: each flag, set alone, yields its own
    verdict (none is shadowed by another). This is the mandate-user HARD
    invariant for #7477 — no resolution overwrites a sibling."""
    assert _derive({"intractable": True}, 5, 5) == "correctly_refused"
    assert _derive({"heartbeat_budget_exceeded": True}, 5, 5) == "heartbeat_budget_exceeded"
    assert _derive({"decomposition_regression": True}, 8, 4) == "decomposition_regression"
    # structural_only is the 4th forensic-adjacent kind (verified decomposition).
    assert _derive({"structural_progress": True}, 5, 5) == "structural_only"


def test_plain_no_progress_unchanged():
    """A flat run (no flag, final==original) is still no_progress — the P3 branch
    only fires on the explicit decomposition_regression flag, never on shape."""
    assert _derive({}, 5, 5) == "no_progress"
