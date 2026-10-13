"""C3 (#1453 calibration forensic, 2026-09-19): freeze-loop typed termination.

Founder case (calibration DEMOS 45/41/52 pass 2, qwen2.5:7b via Ollama,
lane myia-po-2024): the model emits tool-calls as fenced-JSON prose, the
harness echoes its own text back as [receive] — the C617 freeze_loop_guard
fired 6x over 8 iterations forcing Coordinator handoffs, but nothing
enforced a ceiling on the ESCALATION cycle, so the run burned the full
iteration budget with 0 tactic submissions.

The hardcap must:
  (a) yield once escalations reach the hardcap while tactic_history is
      EMPTY (the model structurally cannot tool-call),
  (b) latch state.freeze_loop_terminal so _derive_result_kind classifies
      freeze_loop (distinct from no_progress),
  (c) NOT fire when a tactic was ever submitted (a run that works the
      tools is iterating, not frozen),
  (d) stay legacy-safe in the classifier (field absent -> no_progress).

The yield tests call the REAL AgentExecutor.handle early-exit path (the
freeze check runs before any SK runtime is touched), mirroring the
__new__-bypass harness of test_prover_freeze_loop_guard.py.
"""

from __future__ import annotations

import asyncio
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.state import ProofState  # noqa: E402
from prover.workflow import (  # noqa: E402
    AgentExecutor,
    FREEZE_LOOP_HARDCAP,
    ProofMessage,
)
from prover.run_prover_bg import _derive_result_kind  # noqa: E402


class _FakeTrace:
    def __init__(self):
        self.events = []

    def log(self, agent, role, content):
        self.events.append({"agent": agent, "role": role, "content": content})


class _FakeCtx:
    def __init__(self):
        self.sent = []
        self.yielded = []

    async def send_message(self, msg):
        self.sent.append(msg)

    async def yield_output(self, msg):
        self.yielded.append(msg)


def _make_executor(state, hardcap=FREEZE_LOOP_HARDCAP):
    """AgentExecutor without SK runtime — the freeze early-exit runs
    before any agent invocation, so only the attribute surface it reads
    is needed (same bypass as test_prover_freeze_loop_guard.py)."""
    exe = AgentExecutor.__new__(AgentExecutor)
    exe._agent = SimpleNamespace(name="TacticAgent")
    exe._trace = _FakeTrace()
    exe._state = state
    exe._delta0_stagnation_hardcap = 6
    exe._fail_streak_hardcap = 12
    exe._freeze_loop_hardcap = hardcap
    return exe


# --- executor yield (real handle early-exit path) --------------------------


def test_yield_fires_at_hardcap_with_empty_tactic_history():
    state = ProofState()
    state.freeze_loop_escalations = FREEZE_LOOP_HARDCAP
    exe = _make_executor(state)
    msg = ProofMessage(content="placeholder")
    ctx = _FakeCtx()

    asyncio.run(exe.handle(msg, ctx))

    assert len(ctx.yielded) == 1
    assert state.freeze_loop_terminal is True
    assert ctx.yielded[0].error_type == "tactic_freeze_loop"
    assert "cannot tool-call" in ctx.yielded[0].error
    roles = [e["role"] for e in exe._trace.events]
    assert "freeze_loop_yield" in roles


def test_no_yield_below_hardcap():
    state = ProofState()
    state.freeze_loop_escalations = FREEZE_LOOP_HARDCAP - 1
    exe = _make_executor(state)
    msg = ProofMessage(content="placeholder")
    ctx = _FakeCtx()

    # Past the freeze block without yielding, handle proceeds toward the
    # SK agent call which this harness cannot satisfy — any exception is
    # the expected continuation; what matters is the exit did NOT fire.
    with pytest.raises(Exception):
        asyncio.run(exe.handle(msg, ctx))
    assert ctx.yielded == []
    assert state.freeze_loop_terminal is False


def test_no_yield_when_a_tactic_was_submitted():
    """A run that ever submitted a tactic is iterating, not frozen — the
    empty-tactic_history condition is what makes the hardcap safe."""
    state = ProofState()
    state.tactic_history.append(SimpleNamespace(tactic="rw [Int]"))
    state.freeze_loop_escalations = FREEZE_LOOP_HARDCAP + 3
    exe = _make_executor(state)
    msg = ProofMessage(content="placeholder")
    ctx = _FakeCtx()

    with pytest.raises(Exception):
        asyncio.run(exe.handle(msg, ctx))
    assert ctx.yielded == []
    assert state.freeze_loop_terminal is False


def test_no_yield_when_proof_already_found():
    state = ProofState()
    state.freeze_loop_escalations = FREEZE_LOOP_HARDCAP
    exe = _make_executor(state)
    msg = ProofMessage(content="placeholder")
    msg.proof_found = True
    ctx = _FakeCtx()

    with pytest.raises(Exception):
        asyncio.run(exe.handle(msg, ctx))
    assert ctx.yielded == []
    assert state.freeze_loop_terminal is False


# --- classifier (real _derive_result_kind) --------------------------------


def test_classifies_freeze_loop():
    assert _derive_result_kind({"freeze_loop": True}, 4, 4) == "freeze_loop"


def test_freeze_loop_outranked_by_every_progress_and_outage_flag():
    outranking = {
        "error": "crashed",
        "provider_outage": "provider_outage",
        "intractable": "correctly_refused",
        "heartbeat_budget_exceeded": "heartbeat_budget_exceeded",
        "decomposition_regression": "decomposition_regression",
        "reasoning_budget_exceeded": "reasoning_budget_exceeded",
    }
    for key, expected in outranking.items():
        result = {"freeze_loop": True, key: True}
        assert _derive_result_kind(result, 4, 4) == expected, key
    # Real progress outranks everything:
    assert _derive_result_kind({"freeze_loop": True}, 3, 4) == "sorry_decreased"
    assert (
        _derive_result_kind({"freeze_loop": True, "structural_progress": True}, 4, 4)
        == "structural_only"
    )


def test_legacy_safe_without_field():
    assert _derive_result_kind({}, 4, 4) == "no_progress"
    assert _derive_result_kind({"attempts": 0}, 4, 4) == "no_progress"


# --- state defaults --------------------------------------------------------


def test_state_defaults_are_legacy_safe():
    state = ProofState()
    assert state.freeze_loop_escalations == 0
    assert state.freeze_loop_terminal is False


def test_hardcap_default_matches_two_revision_cycles():
    # Soft guard fires at 3 consecutive no-tool turns; the hardcap ends
    # the run after 3 SEPARATE escalation/revision cycles (founder case
    # burned 6 firings over 8 iterations — cap 3 frees half that budget).
    assert FREEZE_LOOP_HARDCAP == 3
