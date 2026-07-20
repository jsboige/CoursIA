"""Unit tests for #7477 P3 — `decomposition_regression` run verdict.

A *strategic decomposition* (one sorry split into N sub-sorries via ``have``) is
legitimate structural progress **only when it pays off** — i.e. when at least
one sub-sorry is eventually discharged so the net count does not grow. The
autonomous success gate (``_autonomous_success_gate``, provers.py) sets
``structural_progress = True`` whenever ``final >= original`` and the build
passes, so a 4->8 split (the build still compiles) scored ``structural_only``
== "keep iterating" — but iterating *another* decomposition spirals (4->8->16).
Forensic (#7477, DEMO 62 L2551): a run grew 4->8 within the per-edit budget,
committed net +4, and was reported as ``structural_progress: true``
(misleading — it was a regression, not progress).

The fix ranks a net-increasing decomposition as ``decomposition_regression``
(distinct from ``structural_only``) so a coordinator changes strategy (target a
leaf, not another split) instead of mistaking the increase for progress. FX-8
already closed the ``final == original`` statement-mutation case; this closes
the ``final > original`` true-decomposition case.

Run from ``agent_tests/``::

    python -m pytest tests/test_prover_decomposition_regression.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

# Make `prover/` importable regardless of how pytest was invoked (same
# bootstrap convention as tests/test_prover_correctly_refused.py).
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover import run_prover_bg  # noqa: E402


def _derive(result, final_sorry, original_sorry):
    """Thin wrapper so each test reads as the verdict for one scenario."""
    return run_prover_bg._derive_result_kind(result, final_sorry, original_sorry)


# ──────────────────────────────────────────────────────────────────────────
# the decomposition_regression branch
# ──────────────────────────────────────────────────────────────────────────


def test_net_sorry_increase_with_decomposition_is_regression():
    """A decomposition that net-increased the sorry count (final > original)
    with the build passing (structural_progress=True) is decomposition_regression,
    NOT structural_only. The forensic 4->8 case."""
    result = {"structural_progress": True}
    assert _derive(result, final_sorry=8, original_sorry=4) == "decomposition_regression"


def test_net_increase_regardless_of_magnitude():
    """Even a single-net-sorry increase via decomposition is a regression — the
    magnitude does not matter (a 5->6 split that did not discharge is still a
    split that did not help)."""
    result = {"structural_progress": True}
    assert _derive(result, final_sorry=6, original_sorry=5) == "decomposition_regression"
    # Larger jump (the forensic's 4->8).
    assert _derive(result, final_sorry=8, original_sorry=4) == "decomposition_regression"


def test_equal_count_decomposition_stays_structural_only():
    """final == original with structural_progress is structural_only — a
    decomposition that split then discharged one sub-sorry (net zero) is a
    legitimate restructure (the FX-8 statement-mutation case is handled
    upstream via verified_tactic_count; here we only pin that the equality
    case is NOT misclassified as regression)."""
    result = {"structural_progress": True}
    assert _derive(result, final_sorry=4, original_sorry=4) == "structural_only"


def test_sorry_decrease_outranks_decomposition_regression():
    """A run that net-LOWERED the sorry count is sorry_decreased regardless of
    structural_progress — real progress outranks the regression gate (the
    decomposition path is checked after the sorry_decreased check)."""
    result = {"structural_progress": True}
    assert _derive(result, final_sorry=3, original_sorry=5) == "sorry_decreased"


def test_decomposition_regression_only_when_structural_progress():
    """A net sorry increase WITHOUT structural_progress is NOT
    decomposition_regression — it falls through to the later checks. Guards
    against misclassifying a plain sorry regression (no decomposition) as a
    decomposition regression."""
    # No structural_progress flag -> the branch is never entered.
    assert _derive({}, final_sorry=8, original_sorry=4) == "no_progress"
    assert _derive({"structural_progress": False}, 8, 4) == "no_progress"


def test_crashed_outranks_decomposition_regression():
    """An explicit error is crashed regardless of a net-increasing
    decomposition (the crashed check ranks first)."""
    result = {"error": "kaboom", "structural_progress": True}
    assert _derive(result, final_sorry=8, original_sorry=4) == "crashed"


def test_decomposition_regression_plumbs_through_result_dict():
    """End-to-end of the classification: a result dict shaped like the real
    provers.py return (structural_progress surfaced, net sorry increase) — the
    exact path a real 4->8 decomposition run takes."""
    result = {
        "success": True,  # _autonomous_success_gate: build passes, final > 0
        "sorry_evolution": "4 -> 8",
        "structural_progress": True,
        "provider_outage": False,
        "intractable": False,
        "iterations": 8,
    }
    assert _derive(result, final_sorry=8, original_sorry=4) == "decomposition_regression"
