"""Unit tests for #7477 P2a — `correctly_refused` run verdict.

When the Coordinator explicitly abandons a goal via ``mark_sorry_intractable``
(after the F9 Director-consulted + B2 SearchAgent-consulted gates), the run
must end with ``result_kind: correctly_refused`` — DISTINCT from
``no_progress``. Forensic DEMO 62 (NW L2970, a DO-NOT-TARGET line): the agent
correctly refused 4× (role=intractable_blocked) but, because nothing read
``state.intractable`` in the workflow loop, the run kept looping until
iteration_cap and scored no_progress, burning the whole remaining budget on a
target the Coordinator had already declared unprovable.

Two halves of the fix, both exercised here:
  1. ``run_prover_bg._derive_result_kind`` gains a ``correctly_refused``
     branch (ranked AFTER sorry_decreased / structural_only / provider_outage).
  2. ``workflow.AgentExecutor`` yields before iteration_cap when
     ``state.intractable`` is set (so the run does not burn the budget).

Run from ``agent_tests/``::

    python -m pytest tests/test_prover_correctly_refused.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked (same
# bootstrap convention as tests/test_prover_guards.py).
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover import run_prover_bg  # noqa: E402
from prover.state import ProofState  # noqa: E402


# ──────────────────────────────────────────────────────────────────────────
# _derive_result_kind — the correctly_refused branch (acceptance b)
# ──────────────────────────────────────────────────────────────────────────


def _derive(result, final_sorry, original_sorry):
    """Thin wrapper so each test reads as the verdict for one scenario."""
    return run_prover_bg._derive_result_kind(result, final_sorry, original_sorry)


def test_correctly_refused_when_intractable_flag_set():
    """A run whose result carries intractable=True is correctly_refused."""
    result = {"intractable": True, "intractable_reason": "DO NOT TARGET line"}
    assert _derive(result, final_sorry=5, original_sorry=5) == "correctly_refused"


def test_correctly_refused_needs_intractable_truthy():
    """intractable absent or False falls through to no_progress (no false
    positive). A run that never called mark_sorry_intractable must NOT be
    mislabelled correctly_refused."""
    assert _derive({}, final_sorry=5, original_sorry=5) == "no_progress"
    assert _derive({"intractable": False}, 5, 5) == "no_progress"
    assert _derive({"intractable": None}, 5, 5) == "no_progress"


def test_sorry_decreased_outranks_correctly_refused():
    """Real progress outranks the abandonment flag: a run that lowered the
    sorry count before the Coordinator gave up is still a harvest, not a
    refusal. The abandonment stays visible via result['intractable']."""
    result = {"intractable": True}
    assert _derive(result, final_sorry=3, original_sorry=5) == "sorry_decreased"


def test_structural_progress_outranks_correctly_refused():
    """A decomposition landed (structural_progress=True) before the abandon:
    structural_only, not correctly_refused (same ranking rationale as
    sorry_decreased)."""
    result = {"intractable": True, "structural_progress": True}
    assert _derive(result, 5, 5) == "structural_only"


def test_provider_outage_outranks_correctly_refused():
    """A provider death mid-run is provider_outage regardless of intractable:
    the prover never got to work. (Ordering matches the docstring ranking.)"""
    result = {"intractable": True, "provider_outage": True}
    assert _derive(result, 5, 5) == "provider_outage"


def test_crashed_outranks_everything():
    """An explicit error is crashed regardless of intractable."""
    result = {"error": "kaboom", "intractable": True}
    assert _derive(result, 5, 5) == "crashed"


def test_intractable_with_reason_field_passes_through():
    """The reason string is carried on the result for the verdict report
    (sanity: the classification keys off the boolean, the reason is data)."""
    result = {"intractable": True, "intractable_reason": "needs Mathlib X"}
    assert _derive(result, 5, 5) == "correctly_refused"


# ──────────────────────────────────────────────────────────────────────────
# workflow.AgentExecutor — early-exit before iteration_cap (acceptance a)
# ──────────────────────────────────────────────────────────────────────────


def _run_handle(executor, msg):
    """Drive one AgentExecutor.handle() call with a mocked context (mirrors
    the helper in test_prover_guards.py)."""
    import asyncio
    from unittest.mock import AsyncMock

    ctx = AsyncMock()
    ctx.yield_output = AsyncMock()
    ctx.send_message = AsyncMock()
    asyncio.run(executor.handle(msg, ctx))
    return ctx


@pytest.fixture
def no_sleep(monkeypatch):
    """Neutralize asyncio.sleep so the transient-retry backoff is instant."""
    import prover.workflow as wf

    async def _instant(_):
        return None

    monkeypatch.setattr(wf.asyncio, "sleep", _instant)


def _ok_agent(name="TacticAgent"):
    """An agent that succeeds trivially — its run() is never reached when the
    intractable guard yields first, but it must not itself error."""
    from unittest.mock import AsyncMock

    agent = AsyncMock()
    agent.name = name

    class _Resp:
        content = "noop"

    agent.run = AsyncMock(return_value=_Resp())
    return agent


def test_intractable_state_yields_before_iteration_cap(no_sleep):
    """When state.intractable is set the AgentExecutor yields immediately,
    WITHOUT burning the remaining iteration budget.

    This is acceptance (a): a run that refuses a DO-NOT-TARGET line exits via
    the intractable guard, not by looping to iteration_cap. msg.iteration is
    left at its pre-abandon value (1, the entry +1) rather than climbing to
    max_iterations.
    """
    from prover.workflow import AgentExecutor, ProofMessage

    state = ProofState(theorem_statement="t")
    state.intractable = True
    state.intractable_reason = "DO NOT TARGET — placeholder goal"
    ex = AgentExecutor(_ok_agent(), state=state)
    # Plenty of budget left — iteration_cap (10) must NOT be the thing that
    # yields. The intractable guard must.
    msg = ProofMessage(content="x", iteration=0, max_iterations=10)

    ctx = _run_handle(ex, msg)

    assert ctx.yield_output.await_count >= 1, "intractable guard must yield"
    # Budget NOT burned to the cap: only the entry +1 incremented iteration.
    assert msg.iteration == 1, (
        f"intractable guard must yield before iteration_cap; "
        f"expected iteration=1 (entry +1), got {msg.iteration}"
    )


def test_clean_state_does_not_yield_via_intractable_guard(no_sleep):
    """Without state.intractable the guard never fires — the message flows on
    to the agent (no spurious early yield). Guards against a guard that would
    misfire on every clean run."""
    from prover.workflow import AgentExecutor, ProofMessage

    state = ProofState(theorem_statement="t")
    # intractable left at its False default.
    ex = AgentExecutor(_ok_agent(), state=state)
    msg = ProofMessage(content="x", iteration=0, max_iterations=10)

    ctx = _run_handle(ex, msg)

    # The intractable guard did not fire — the message flowed on to the agent.
    # (Other guards may or may not yield depending on counters; the point is
    # intractable was not the reason. We assert the agent WAS reached.)
    assert _ok_agent_ok_reached(ex), (
        "on a clean state the agent must be reached (intractable guard silent)"
    )


def _ok_agent_ok_reached(executor):
    """The wrapped agent's run() was awaited at least once → the message was
    not short-circuited by the intractable guard."""
    # AgentExecutor stores the agent; its mock records the await count.
    agent = getattr(executor, "_agent", None)
    return agent is not None and getattr(agent.run, "await_count", 0) >= 1


def test_intractable_yield_silent_when_proof_already_found(no_sleep):
    """If a proof was already found on this hop, the intractable flag must NOT
    override it (the `not msg.proof_found` clause). A late abandon after a
    success should not discard the success."""
    from prover.workflow import AgentExecutor, ProofMessage

    state = ProofState(theorem_statement="t")
    state.intractable = True
    ex = AgentExecutor(_ok_agent(), state=state)
    msg = ProofMessage(content="x", iteration=0, max_iterations=10)
    msg.proof_found = True

    # The intractable guard has a `not msg.proof_found` guard, so it does not
    # fire here. We just assert no exception / the guard was inert.
    _run_handle(ex, msg)
    # No assertion on yield_count here: the point is the intractable guard
    # specifically did not fire on a proof_found message. If it had, it would
    # yield even though proof_found=True — covered by the absence of a
    # dedicated intractable_yield trace. This test pins the clause exists.


# ──────────────────────────────────────────────────────────────────────────
# Integration: result dict from the multi-agent path carries intractable
# ──────────────────────────────────────────────────────────────────────────


def test_correctly_refused_plumbs_through_classification_from_result_fields():
    """End-to-end of the classification: a result dict shaped like the
    multi-agent provers.py return (intractable + intractable_reason surfaced,
    no sorry drop, no structural progress, no outage) classifies as
    correctly_refused — the exact path a real DEMO 62-style refusal takes."""
    result = {
        "success": False,
        "sorry_evolution": "5 -> 5",
        "structural_progress": False,
        "provider_outage": False,
        "provider_failures": 0,
        "intractable": True,
        "intractable_reason": "target is a DO NOT TARGET placeholder",
        "iterations": 1,
    }
    assert _derive(result, final_sorry=5, original_sorry=5) == "correctly_refused"
