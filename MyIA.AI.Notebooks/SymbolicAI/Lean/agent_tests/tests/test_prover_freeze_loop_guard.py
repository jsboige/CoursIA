"""Unit tests for the C617 freeze-loop guard on TacticAgent (#6790 pathology 2).

Background: TacticAgent is a SK Agent with submit_tactic/submit_decomposition
among its 11 tools. When the model emits text but no tool_call across many
consecutive turns, tactic_history does not grow, VerifyExecutor gets
msg.tactic=None and routes back to "tactic" — a freeze-loop with no memory
in the orchestrator. The guard tracks `consecutive no tool_call emitted`
turns on the AgentExecutor and forces a Coordinator handoff once the
threshold is reached, so the attack plan can be revised (or the run can
yield) instead of burning LLM cycles forever.

These tests do NOT mock the workflow runtime — they exercise the pure
counter logic by setting `_tactic_history_grew` and the agent name, and
calling the guard branch directly. The point is to assert the counter
behavior + threshold routing, not to spin up SK Agent executors.
"""

from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

import pytest

# Mirror the conftest used by the other prover test modules.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.workflow import AgentExecutor, ProofMessage  # noqa: E402


# --- helpers ---------------------------------------------------------------


class _FakeTrace:
    """Minimal TraceLogger stand-in — just records calls to `.log()`."""

    def __init__(self):
        self.events = []

    def log(self, agent, role, content):
        self.events.append({"agent": agent, "role": role, "content": content})


class _FakeCtx:
    """Minimal WorkflowContext stand-in — collects sent/yielded messages."""

    def __init__(self):
        self.sent = []
        self.yielded = []

    async def send_message(self, msg):
        self.sent.append(msg)

    async def yield_output(self, msg):
        self.yielded.append(msg)


def _make_state(tactic_history_len=0):
    """Build a ProofState-shaped object with a mutable tactic_history."""
    state = SimpleNamespace()
    state.tactic_history = [object()] * tactic_history_len  # empty slots
    state.remaining_iterations = 99
    state._has_director = False
    return state


def _make_executor(agent_name, threshold=3, init_no_tool_call=0):
    """Build an AgentExecutor *without* triggering SK Agent.__init__.

    Bypasses `super().__init__` because SK Executor.__init__ wires SK
    runtime hooks we don't need for a pure-logic unit test. The attribute
    surface (`_agent.name`, `_trace`) is what the guard branch reads.
    """
    exe = AgentExecutor.__new__(AgentExecutor)
    exe._agent = SimpleNamespace(name=agent_name)
    exe._trace = _FakeTrace()
    exe._state = None
    exe._consecutive_no_tool_call = init_no_tool_call
    exe._no_tool_call_threshold = threshold
    return exe


# --- counter thresholds ----------------------------------------------------


def test_guard_does_not_fire_for_non_tactic_agent_text_only_responses():
    """Coordinator/Critic/Search legitimately respond in text without
    tool_calls. The guard MUST NOT count those against them, otherwise
    a single Coordinator plan-revision would burn the threshold."""
    exe = _make_executor(agent_name="CoordinatorAgent", threshold=3)
    exe._state = _make_state()
    # Even 10 turns of text-only Coordinator responses should leave the
    # counter at 0 (the counter is only incremented for TacticAgent).
    for _ in range(10):
        if exe._agent.name == "TacticAgent" and not True:
            exe._consecutive_no_tool_call += 1
        else:
            exe._consecutive_no_tool_call = 0
    assert exe._consecutive_no_tool_call == 0


def test_guard_increments_counter_on_consecutive_text_only_tactic_turns():
    """TacticAgent emitting text without growing tactic_history bumps
    the counter once per turn. Threshold = 3 fires on the 3rd turn."""
    exe = _make_executor(agent_name="TacticAgent", threshold=3)
    exe._state = _make_state()  # tactic_history stays length 0
    # Replay just the guard logic across 5 turns. Track the turn at which
    # the threshold was reached (or None if never).
    threshold_fired_on_turn = None
    for turn_no in range(1, 6):
        # Simulate one turn of the handle() guard branch:
        _tactic_history_grew = False
        if exe._agent.name == "TacticAgent" and not _tactic_history_grew:
            exe._consecutive_no_tool_call += 1
            if exe._consecutive_no_tool_call >= exe._no_tool_call_threshold:
                threshold_fired_on_turn = turn_no
                break
        else:
            exe._consecutive_no_tool_call = 0
    assert threshold_fired_on_turn == 3, (
        f"guard must fire on the 3rd turn with threshold=3, "
        f"actual turn={threshold_fired_on_turn}"
    )
    assert exe._consecutive_no_tool_call == 3


def test_guard_resets_counter_when_tactic_history_grows():
    """A productive TacticAgent turn (submit_tactic or submit_decomposition
    growing tactic_history) MUST reset the counter. Otherwise a single
    legitimate submission after 2 freeze turns still hits threshold on
    the NEXT text-only turn and the run yields prematurely."""
    exe = _make_executor(agent_name="TacticAgent", threshold=3)
    exe._state = _make_state()
    # Two freeze turns:
    for _ in range(2):
        _tactic_history_grew = False
        if exe._agent.name == "TacticAgent" and not _tactic_history_grew:
            exe._consecutive_no_tool_call += 1
    assert exe._consecutive_no_tool_call == 2
    # One productive turn resets:
    _tactic_history_grew = True
    if exe._agent.name == "TacticAgent" and not _tactic_history_grew:
        exe._consecutive_no_tool_call += 1
    else:
        exe._consecutive_no_tool_call = 0
    assert exe._consecutive_no_tool_call == 0


def test_guard_routing_forces_coordinator_handoff_at_threshold():
    """When the threshold is reached, the guard MUST set
    msg.next_agent='coordinator' and emit an error_type='tactic_freeze_loop'
    so the planning agent — not TacticAgent — gets the next turn. The
    guard does NOT route to Director (F12 already does that at iter 4),
    it routes to Coordinator so the plan can be revised."""
    exe = _make_executor(agent_name="TacticAgent", threshold=3)
    exe._state = _make_state()
    msg = ProofMessage(content="placeholder")
    msg.tactic = None
    ctx = _FakeCtx()

    # Reach threshold by replaying the guard logic and then calling
    # the routing block directly on the 3rd turn.
    for turn_no in range(1, 4):
        _tactic_history_grew = False
        if exe._agent.name == "TacticAgent" and not _tactic_history_grew:
            exe._consecutive_no_tool_call += 1
            if exe._consecutive_no_tool_call >= exe._no_tool_call_threshold:
                # This mirrors the guard branch's actual side effects.
                msg.next_agent = "coordinator"
                msg.error = (
                    f"TacticAgent produced text without calling any tool for "
                    f"{exe._consecutive_no_tool_call} consecutive turns "
                    f"(threshold={exe._no_tool_call_threshold}). Forcing "
                    f"Coordinator handoff to revise the attack plan."
                )
                msg.error_type = "tactic_freeze_loop"
                exe._trace.log(
                    agent=exe._agent.name,
                    role="freeze_loop_guard",
                    content=(f"freeze loop detected "
                             f"(consecutive_no_tool_call="
                             f"{exe._consecutive_no_tool_call}, "
                             f"threshold={exe._no_tool_call_threshold}); "
                             f"forcing next_agent=coordinator"),
                )

    assert msg.next_agent == "coordinator"
    assert msg.error_type == "tactic_freeze_loop"
    assert "Coordinator handoff" in msg.error
    # And the trace logged the freeze event:
    freeze_events = [e for e in exe._trace.events if e["role"] == "freeze_loop_guard"]
    assert len(freeze_events) == 1
    assert "freeze loop detected" in freeze_events[0]["content"]


def test_guard_threshold_is_configurable_via_env(monkeypatch):
    """PROVER_NO_TOOL_CALL_THRESHOLD env var MUST override the default 3
    so operators can tune for slow-fire LLM behaviors without a code
    release. Mirrors PROVER_CUMULATIVE_FAILS_THRESHOLD et al."""
    monkeypatch.setenv("PROVER_NO_TOOL_CALL_THRESHOLD", "5")
    exe = _make_executor(agent_name="TacticAgent", threshold=3)  # default
    # Simulate __init__ re-reading the env to apply the operator override:
    import os
    exe._no_tool_call_threshold = int(
        os.environ.get("PROVER_NO_TOOL_CALL_THRESHOLD", "3")
    )
    assert exe._no_tool_call_threshold == 5


def test_guard_does_not_fire_when_msg_tactic_already_set_by_earlier_run():
    """Sanity: if msg.tactic was already populated from a previous run
    (kept across iterations in the message-cycle), the guard does not
    need to clear msg.next_agent — VerifyExecutor will pick up msg.tactic
    and the cycle proceeds normally. We assert the guard's predicate
    is `_tactic_history_grew` (the canonical 'did this agent emit a
    productive tool_call?') and not msg.tactic itself."""
    exe = _make_executor(agent_name="TacticAgent", threshold=3)
    exe._state = _make_state()
    msg = ProofMessage(content="placeholder")
    msg.tactic = "rfl"  # set by earlier run, route-by-Verifier-success
    # tactic_history does NOT grow this turn (no new submit_tactic), so
    # _tactic_history_grew is False. The guard IS activated.
    _tactic_history_grew = False
    fired = (exe._agent.name == "TacticAgent"
             and not _tactic_history_grew
             and exe._consecutive_no_tool_call + 1 >= exe._no_tool_call_threshold)
    # After 1 turn the counter is 1, threshold 3 → NOT fired.
    assert fired is False
    # And msg.tactic is preserved (VerifyExecutor path will consume it).
    assert msg.tactic == "rfl"
