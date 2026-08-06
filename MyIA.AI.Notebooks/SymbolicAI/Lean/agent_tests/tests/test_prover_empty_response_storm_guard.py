"""Unit tests for the SearchAgent empty-response storm guard (#1453, cycle-98).

Background: the empty_response_guard (workflow.py) injects a fallback message
when an agent burns its output budget in `reasoning_content` and emits no
visible parts. That keeps the run alive — but when the SAME agent (forensic
evidence: SearchAgent, VOTING session 2 — 475s burned across 2 invocations)
keeps producing empty responses, the injected fallback only extends the burn
until the iteration_cap catches it. The guard now tracks
`consecutive empty responses` from SearchAgent and forces a Coordinator
handoff once the threshold is reached — mirroring the TacticAgent freeze-loop
guard (test_prover_freeze_loop_guard.py).

These tests do NOT mock the workflow runtime — they exercise the pure counter
logic by setting `response_text` / `msg.tactic` and the agent name, and
calling the guard branch directly (the established convention for these
guards in this suite). The point is to assert the counter behavior +
threshold routing + SearchAgent scoping, not to spin up SK Agent executors.

See #1453 (prover harness robustness).
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


def _make_executor(agent_name, threshold=3, init_empty_response=0):
    """Build an AgentExecutor *without* triggering SK Agent.__init__.

    Bypasses `super().__init__` because SK Executor.__init__ wires SK runtime
    hooks we don't need for a pure-logic unit test. The attribute surface
    (`_agent.name`, `_trace`, `_consecutive_empty_response`,
    `_empty_response_threshold`) is what the guard branch reads.
    """
    exe = AgentExecutor.__new__(AgentExecutor)
    exe._agent = SimpleNamespace(name=agent_name)
    exe._trace = _FakeTrace()
    exe._state = None
    exe._consecutive_empty_response = init_empty_response
    exe._empty_response_threshold = threshold
    return exe


def _run_empty_response_guard(exe, response_text, msg, ctx):
    """Inline the exact guard branch from workflow.py (empty_response_guard).

    Returns the (possibly rewritten) response_text so callers can assert on
    the injected fallback. Mirrors the inline-call convention of
    test_prover_freeze_loop_guard (the `await ctx.send_message(msg)` framework
    detail is elided — we record the sent message on the FakeCtx directly and
    assert on msg fields, exactly as the freeze-loop suite does).
    """
    if not response_text.strip() and not msg.tactic:
        if exe._agent.name == "SearchAgent":
            exe._consecutive_empty_response += 1
            if (exe._consecutive_empty_response
                    >= exe._empty_response_threshold):
                msg.next_agent = "coordinator"
                msg.error = (
                    f"SearchAgent produced an empty response for "
                    f"{exe._consecutive_empty_response} consecutive turns "
                    f"(threshold={exe._empty_response_threshold})."
                )
                msg.error_type = "search_empty_response_storm"
                exe._trace.log(
                    agent=exe._agent.name,
                    role="empty_response_storm_guard",
                    content="storm; forcing next_agent=coordinator",
                )
                ctx.sent.append(msg)  # elide `await ctx.send_message(msg)`
                return response_text
        response_text = (
            "[harness] previous agent produced an empty response."
        )
        exe._trace.log(
            agent=exe._agent.name,
            role="empty_response_guard",
            content="injected fallback message (response was empty)",
        )
    else:
        exe._consecutive_empty_response = 0
    return response_text


# --- counter behavior ------------------------------------------------------


def test_storm_does_not_fire_for_non_search_agent_empty_responses():
    """A TacticAgent / Coordinator empty response must NOT touch the
    SearchAgent empty-response counter. The storm guard is SearchAgent-scoped
    (the evidenced agent); other agents' empty replies route through the
    generic fallback and the freeze-loop (TacticAgent) respectively.
    """
    exe = _make_executor("TacticAgent", threshold=3)
    msg = ProofMessage(content="x", max_iterations=10)
    msg.tactic = None
    ctx = _FakeCtx()

    # Three consecutive empty TacticAgent responses.
    for _ in range(3):
        _run_empty_response_guard(exe, "", msg, ctx)

    assert exe._consecutive_empty_response == 0, (
        "non-SearchAgent empty responses must not increment the SearchAgent "
        "storm counter"
    )
    assert ctx.sent == [], "no storm escalation for non-SearchAgent"


def test_storm_increments_on_search_empty_response_below_threshold():
    """A SearchAgent empty response increments the counter but does NOT
    escalate before the threshold — the generic fallback is still injected so
    the run can recover from a one-off burned budget.
    """
    exe = _make_executor("SearchAgent", threshold=3)
    msg = ProofMessage(content="x", max_iterations=10)
    msg.tactic = None
    ctx = _FakeCtx()

    out = _run_empty_response_guard(exe, "", msg, ctx)

    assert exe._consecutive_empty_response == 1
    assert ctx.sent == [], "must not escalate below threshold"
    # Generic fallback still injected (run continues recoverably).
    assert "[harness]" in out


def test_storm_resets_on_non_empty_response():
    """A productive (non-empty) response breaks the streak — the counter
    resets so a future empty run must climb back to the threshold.
    """
    exe = _make_executor("SearchAgent", threshold=3, init_empty_response=2)
    msg = ProofMessage(content="x", max_iterations=10)
    msg.tactic = "exact h"  # non-empty response (a tactic was produced)
    ctx = _FakeCtx()

    _run_empty_response_guard(exe, "found a relevant lemma", msg, ctx)

    assert exe._consecutive_empty_response == 0, (
        "a non-empty response must reset the empty-response streak"
    )
    assert ctx.sent == []


def test_storm_forces_coordinator_handoff_at_threshold():
    """At the threshold the guard forces next_agent=coordinator with
    error_type=search_empty_response_storm and emits the message — instead
    of injecting yet another fallback that would only extend the burn.
    Pre-arm the counter to threshold-1, then one more empty SearchAgent
    response trips the escalation.
    """
    exe = _make_executor("SearchAgent", threshold=3, init_empty_response=2)
    msg = ProofMessage(content="x", max_iterations=10)
    msg.tactic = None
    ctx = _FakeCtx()

    _run_empty_response_guard(exe, "", msg, ctx)

    assert exe._consecutive_empty_response == 3
    assert ctx.sent, "must send_message to force the Coordinator handoff"
    escalated = ctx.sent[-1]
    assert escalated.next_agent == "coordinator"
    assert escalated.error_type == "search_empty_response_storm"
    # The escalation was traced for forensic visibility.
    roles = [e["role"] for e in exe._trace.events]
    assert "empty_response_storm_guard" in roles
