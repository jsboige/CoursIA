"""WorkflowBuilder graph for multi-agent proof sessions.

Architecture:
    SearchAgent -> TacticAgent -> VerifyExecutor -> CriticAgent
                                                       |
                                    +------------------+------------------+
                                    v                  v                  v
                              SearchAgent         TacticAgent     CoordinatorAgent
                                                                      |
                                                   +------------------+------------------+
                                                   v                  v                  v
                                             SearchAgent         TacticAgent        yield_output

Hardening (2026-05-08):
- Each `AgentExecutor` enforces a wall-clock timeout on its single LLM call so
  a stalled provider can't freeze the graph indefinitely.
- `ProofMessage.iteration` is incremented on every traversal. When it exceeds
  `max_iterations` the message is yielded immediately, ending the run cleanly.
"""

import asyncio
import time
from dataclasses import dataclass
from typing import Optional

from agent_framework import (
    WorkflowBuilder,
    Agent,
    Executor,
    WorkflowContext,
    handler,
    Case,
    Default,
)

from .state import SorryContext
from .trace import TraceLogger
from .knowledge import ProofKnowledgeBase


# Default per-agent LLM timeout. Reasoning models (z.ai GLM-5.1, Qwen3.6) burn
# the bulk of their token budget in `reasoning_content` before producing a
# visible response — measured 39s wall-clock on z.ai for a trivial smoke test
# with max_tokens=2048 (entirely consumed by reasoning). 600s lets the model
# actually think on Mathlib goals; the workflow wall-clock cap in provers.py
# still bounds the total session.
DEFAULT_AGENT_TIMEOUT_S = 600

# Transient-error retry policy. Forensic analysis of prover traces
# (traces/*.spans.jsonl) showed whole iterations lost to TRANSIENT provider
# errors (HTTP 5xx, connection reset/aborted, read/connect timeouts) that
# crashed an agent mid-run with no retry. Retries are bounded: 2 attempts with
# short exponential backoff (2s, 4s). Note: a 404 is NOT transient — it means a
# bad/missing model_id (config bug) — and must NOT be retried (see
# `_is_transient_error`).
TRANSIENT_RETRY_MAX = 2
TRANSIENT_RETRY_BACKOFF_S = (2.0, 4.0)

# P1 stagnation hard-cap (Epic #1453). The compile tool (tools.py) computes
# the number of consecutive Δ0 compiles — a build that succeeds but does NOT
# reach a new sorry-count low — and mirrors it to
# `state.consecutive_delta0_compiles`. It also emits a soft `directive` string
# in the compile result, on which the orchestrator used to rely entirely: the
# count was written but never enforced. Forensic trace
# multi_custom_Lattice_L147_zai.json: 26 of 30 compiles were Δ0 (22 consecutive
# at 4 sorry right from the start) yet the run never terminated — it burned the
# full iteration + LLM budget making zero proof progress. This ceiling is the
# hard backstop: it fires at 2x the tools.py soft threshold (3), so the soft
# directive and the existing Director escalations get a window first, but a run
# that ignores the signal for this many consecutive Δ0 compiles is yielded
# rather than left to waste compute.
DELTA0_STAGNATION_HARDCAP = 6


def _is_transient_error(exc: BaseException) -> bool:
    """Return True if `exc` looks like a transient provider/network error.

    Matches ONLY conditions worth retrying:
      - HTTP 5xx server errors (500, 502, 503, 504),
      - connection reset / aborted / refused,
      - read / connect timeouts.

    Explicitly EXCLUDES 404 (bad/missing model_id — a config bug, retrying just
    wastes time) and other 4xx client errors (401/403/422). `agent_framework`
    may wrap the underlying httpx / openai error, so we probe both the
    `status_code` attribute and the stringified message defensively.
    """
    # 1. Structured HTTP status code, if the provider exposed one. Checked on
    #    the exception and a common nested `.response` (httpx-style) attribute.
    for candidate in (exc, getattr(exc, "response", None)):
        if candidate is None:
            continue
        status = getattr(candidate, "status_code", None)
        if isinstance(status, int):
            # 5xx → transient. Any 4xx (incl. 404) → NOT transient.
            return status in (500, 502, 503, 504)

    # 2. Fall back to message inspection (wrapped errors lose the attribute).
    msg = str(exc).lower()

    # Guard: never treat an explicit 404 / other 4xx as transient even if the
    # message also happens to contain a generic word like "timeout".
    if any(code in msg for code in (" 404", "404 ", "not found",
                                    " 401", " 403", " 422",
                                    "unauthorized", "forbidden")):
        return False

    transient_markers = (
        "500", "502", "503", "504",
        "internal server error", "bad gateway",
        "service unavailable", "gateway timeout",
        "connection reset", "connection aborted", "connection refused",
        "connectionreset", "connectionerror",
        "read timeout", "connect timeout", "timed out", "timeout",
        "temporarily unavailable", "remote end closed",
    )
    return any(marker in msg for marker in transient_markers)


@dataclass
class ProofMessage:
    """Message flowing between agents in the workflow."""
    content: str = ""
    iteration: int = 0
    sorry_count: int = 0
    tactic: Optional[str] = None
    error: Optional[str] = None
    error_type: Optional[str] = None
    is_decomposition: bool = False
    proof_found: bool = False
    next_agent: str = "coordinator"  # B.3: coordinator runs first to set attack plan
    max_iterations: int = 10
    plan: Optional[list] = None  # attack plan from CoordinatorAgent
    # F5 (2026-05-11): set when Coordinator calls mark_sorry_intractable.
    # AgentExecutor yields immediately when this is true.
    intractable: bool = False
    intractable_reason: Optional[str] = None
    # Director (Track C): counts how many times the DirectorAgent has been
    # consulted this session. Capped at 3 to avoid budget burn.
    director_calls: int = 0
    # B2a (issue #1224): identifiers the Director flagged as absent from
    # Mathlib / the current project. TacticAgent receives a warning to NOT
    # try these identifiers. Populated by AgentExecutor after DirectorAgent
    # runs; consumed when TacticAgent receives the message.
    absent_identifiers: list = None
    # Feature 3: DiagnosisAgent qualitative assessment fields
    diagnosis_assessment: Optional[str] = None
    is_structural_progress: bool = False
    diagnosis_reason: Optional[str] = None
    agent_opinion: str = ""


class AgentExecutor(Executor):
    """Wraps an Agent to accept/output ProofMessage in the workflow.

    Converts ProofMessage -> agent.run(content) -> ProofMessage. Enforces a
    per-call timeout (default 90s) so stalled providers don't hang the graph.
    """

    def __init__(self, agent: Agent, trace: TraceLogger = None,
                 timeout_s: int = DEFAULT_AGENT_TIMEOUT_S,
                 state: "ProofState" = None, **kwargs):
        super().__init__(id=agent.name or agent.id or "agent", **kwargs)
        self._agent = agent
        self._trace = trace
        self._timeout_s = timeout_s
        self._state = state  # B.3: shared state for plan propagation
        # P1 (Epic #1453): hard ceiling on consecutive Δ0 compiles; see
        # DELTA0_STAGNATION_HARDCAP. Read live from state on every iteration.
        self._delta0_stagnation_hardcap = DELTA0_STAGNATION_HARDCAP

    @handler
    async def handle(self, msg: ProofMessage, ctx: WorkflowContext[ProofMessage]) -> None:
        """Run the agent with the message content, produce updated ProofMessage."""
        # Iteration cap — if we've already hit max, end the run cleanly.
        # P1 (V5): tolerate +1 iteration if message is en-route to Director
        # and Director budget remains. The Director is a high-value frontier
        # LLM call (Opus 4.7 / GPT-5.5) that can break deadlocks — yielding
        # at exactly max_iterations when a Director response is in-flight
        # wastes the escalation budget already invested in reaching it.
        # Forensic evidence: Demo16 CYCLE78, iter_cap fired at [+3213.3s]
        # while Director was the designated next_agent, 2→2 no progress.
        msg.iteration += 1
        _director_budget_remaining = (
            self._state
            and hasattr(self._state, '_has_director')
            and self._state._has_director
            and msg.director_calls < (
                self._state._director_max_calls
                if hasattr(self._state, '_director_max_calls')
                else 3
            )
        )
        _over_cap = msg.max_iterations and msg.iteration > msg.max_iterations
        _director_in_flight = (
            msg.next_agent == "director" and _director_budget_remaining
        )
        if _over_cap and not _director_in_flight:
            if self._trace:
                self._trace.log(
                    agent=self._agent.name, role="iteration_cap",
                    content=f"iter {msg.iteration} > max {msg.max_iterations}, yielding",
                )
            await ctx.yield_output(msg)
            return
        elif _over_cap and _director_in_flight:
            if self._trace:
                self._trace.log(
                    agent=self._agent.name, role="iteration_cap_tolerated",
                    content=(f"iter {msg.iteration} > max {msg.max_iterations} "
                             f"but Director in-flight (calls={msg.director_calls}), "
                             f"allowing +1"),
                )

        # P1 (Epic #1453): Δ0 stagnation hard-cap. The compile tool mirrors the
        # consecutive-Δ0 count to state.consecutive_delta0_compiles and emits a
        # soft directive, but nothing enforced it — a run could compile cleanly
        # dozens of times without ever lowering the sorry count (forensic L147:
        # 22 consecutive Δ0 at 4 sorry). Once the count crosses the hard ceiling
        # the soft signal and every Director escalation have already had their
        # window, so we yield to stop wasting compute rather than escalate again.
        _delta0 = (
            getattr(self._state, "consecutive_delta0_compiles", 0)
            if self._state else 0
        )
        if (not msg.proof_found
                and _delta0 >= self._delta0_stagnation_hardcap):
            if self._trace:
                self._trace.log(
                    agent=self._agent.name, role="delta0_stagnation_yield",
                    content=(f"consecutive_delta0_compiles={_delta0} >= "
                             f"hardcap={self._delta0_stagnation_hardcap}, "
                             f"yielding to stop no-progress waste"),
                )
            await ctx.yield_output(msg)
            return

        # F12: Force Director invocation at iteration 4 (after first
        # Coordinator→Search→Tactic cycle completes). This ensures Director
        # is consulted even when the Coordinator times out or fails to call
        # request_director_guidance on its own (root cause of T1 forensic
        # finding: Coordinator GLM-5.1 timeout → workflow degraded to
        # Search→Tactic loop, Director never reached).
        if (msg.iteration == 4
                and msg.director_calls == 0
                and self._state
                and hasattr(self._state, '_has_director')
                and self._state._has_director):
            msg.next_agent = "director"
            if self._trace:
                self._trace.log(
                    agent=self._agent.name, role="force_director",
                    content="iter 4 reached, forcing Director consultation",
                )

        if self._trace:
            self._trace.log(
                agent=self._agent.name, role="receive",
                content=msg.content[:100],
            )

        # B.3: Inject attack plan context for downstream agents
        content = msg.content
        if msg.plan and self._agent.name != "CoordinatorAgent":
            plan_header = "PLAN D'ATTAQUE (suivre ces etapes):\n"
            plan_header += "\n".join(f"  {i+1}. {step}" for i, step in enumerate(msg.plan))
            plan_header += "\n\n---\n"
            content = plan_header + content

        # B2a (issue #1224): Inject absent-identifier warning for TacticAgent.
        # When the Director flagged identifiers as absent, TacticAgent must
        # NOT try `exact <absent_id>` — it will always produce "unknown
        # identifier". This prevents the Director→Tactic gap where the
        # Director says "X doesn't exist" but TacticAgent still tries X.
        if (msg.absent_identifiers
                and self._agent.name == "TacticAgent"):
            warning = (
                "WARNING — ABSENT IDENTIFIERS (Director-confirmed). "
                "Do NOT use these in any tactic; they do not exist in "
                "Mathlib or the current project:\n"
            )
            for ident in msg.absent_identifiers:
                warning += f"  - {ident}\n"
            warning += (
                "If the Director suggested a tactic using any of these, "
                "you must find an alternative identifier or decompose the "
                "goal differently.\n\n---\n"
            )
            content = warning + content

        # NOTE: do NOT wrap `agent.run` in `asyncio.wait_for`. The framework's
        # AgentTelemetryLayer sets/resets a ContextVar Token internally; running
        # inside a wait_for-spawned Task creates the Token in a child context
        # and the reset from the outer context raises
        # `ValueError: <Token> was created in a different Context`,
        # which silently corrupts every LLM call (verified via OTel trace
        # multi_SMOKE_ZERO_ADD_local_*.spans.jsonl, 2026-05-11). The wall-clock
        # cap in provers.py bounds the total session.
        # Snapshot tactic_history len so we can detect new submit_tactic /
        # submit_decomposition calls below and propagate them to msg.tactic.
        history_len_before = (
            len(self._state.tactic_history)
            if self._state and hasattr(self._state, "tactic_history") else 0
        )
        try:
            response = await self._agent.run(content)
            response_text = self._extract_response_text(response)
        except Exception as e:
            # P3 (V5): context-window overflow handler. Fast models (Critic,
            # Search) have smaller context windows than reasoning models.
            # When the accumulated context exceeds the window, the API
            # returns a 400 / context_length_exceeded error. Instead of
            # propagating the error (which stalls the workflow), truncate
            # to the last N chars and retry once.
            # Forensic: Demo16 CYCLE78, CriticAgent error at [+3128.2s]
            # — full proof-state context exceeded z.ai fast-model window.
            _err_str = str(e).lower()
            _is_context_err = any(s in _err_str for s in (
                "context_length", "context window", "too many tokens",
                "maximum context", "token limit", "status 400",
                "request_too_large",
            ))
            if _is_context_err:
                # Truncate to last 4000 chars (roughly 1-2K tokens, safe
                # for any model with ≥4K context). Preserve the tail which
                # contains the most recent agent output and state summary.
                _truncated = content[-4000:] if len(content) > 4000 else content
                _trunc_header = (
                    f"[harness] Context truncated from {len(content)} to "
                    f"{len(_truncated)} chars due to context-window overflow. "
                    f"Focus on the most recent state.\n\n---\n"
                )
                if self._trace:
                    self._trace.log(
                        agent=self._agent.name, role="context_truncate",
                        content=(f"context overflow, retrying with "
                                 f"{len(_truncated)}/{len(content)} chars"),
                    )
                try:
                    response = await self._agent.run(_trunc_header + _truncated)
                    response_text = self._extract_response_text(response)
                except Exception as e2:
                    # Second failure — produce minimal recovery signal
                    response_text = (
                        "[harness] Agent failed after context truncation "
                        f"retry: {str(e2)[:100]}. Route to next agent."
                    )
                    if self._trace:
                        self._trace.log(
                            agent=self._agent.name, role="error_retry_failed",
                            content=str(e2)[:200],
                        )
            elif _is_transient_error(e):
                # Transient provider/network error (HTTP 5xx, connection
                # reset/aborted, read/connect timeout). Forensic: several
                # iterations were lost when an agent crashed mid-run on a
                # transient error with no retry. Retry the SAME invocation,
                # bounded (TRANSIENT_RETRY_MAX) with short exponential backoff.
                # A 404 / other 4xx never reaches here (_is_transient_error
                # excludes them — those are config bugs, not worth retrying).
                response_text = None
                _last_exc = e
                for _attempt in range(1, TRANSIENT_RETRY_MAX + 1):
                    _backoff = TRANSIENT_RETRY_BACKOFF_S[
                        min(_attempt - 1, len(TRANSIENT_RETRY_BACKOFF_S) - 1)
                    ]
                    _retry_msg = (
                        f"[retry] transient provider error "
                        f"(attempt {_attempt}/{TRANSIENT_RETRY_MAX}): "
                        f"{repr(_last_exc)[:120]}"
                    )
                    if self._trace:
                        self._trace.log(
                            agent=self._agent.name, role="transient_retry",
                            content=_retry_msg,
                        )
                    await asyncio.sleep(_backoff)
                    try:
                        response = await self._agent.run(content)
                        response_text = self._extract_response_text(response)
                        break
                    except Exception as e_retry:
                        _last_exc = e_retry
                        # Only keep retrying while still transient; a fresh
                        # non-transient error must fall through immediately.
                        if not _is_transient_error(e_retry):
                            break
                if response_text is None:
                    # Retries exhausted (or a non-transient error surfaced) —
                    # fall through to the existing failure handling, do NOT
                    # swallow the error silently.
                    response_text = f"Agent error: {_last_exc}"
                    if self._trace:
                        self._trace.log(
                            agent=self._agent.name, role="transient_retry_failed",
                            content=str(_last_exc)[:200],
                        )
            else:
                response_text = f"Agent error: {e}"
                if self._trace:
                    self._trace.log(
                        agent=self._agent.name, role="error",
                        content=str(e)[:200],
                    )

        # Detect "burned response" — thinking models sometimes spend their entire
        # output budget in `reasoning_content` and emit no visible parts.
        # The framework's last message has finish_reason="length" with empty
        # parts. If we pass that empty text to the next agent, the workflow
        # silently degrades. Annotate the response so the downstream agent
        # sees a recoverable signal instead of silence.
        if not response_text.strip() and not msg.tactic:
            response_text = (
                "[harness] previous agent produced an empty response (likely "
                "burned its output budget in reasoning_content). Proceed using "
                "the proof state and tools directly; do not wait for input from "
                "the previous step."
            )
            if self._trace:
                self._trace.log(
                    agent=self._agent.name, role="empty_response_guard",
                    content="injected fallback message (response was empty)",
                )

        # Bridge TacticAgent's tool-side submissions to the workflow message:
        # `submit_tactic` and `submit_decomposition` write to
        # `state.tactic_history` but never touch the ProofMessage. Without this
        # bridge, `msg.tactic` stays None forever, VerifyExecutor fails with
        # "No tactic submitted" and routes back to TacticAgent until the
        # iteration cap. Pick up the latest attempt added during this run.
        if (self._state and hasattr(self._state, "tactic_history")
                and len(self._state.tactic_history) > history_len_before):
            latest = self._state.tactic_history[-1]
            tactic_text = getattr(latest, "tactic", None)
            # Filter control signals that are NOT valid Lean tactics
            _CONTROL_SIGNALS = {"LEAVERN", "ABORT", "SKIP", "GIVE_UP"}
            if tactic_text and tactic_text.strip().upper() in _CONTROL_SIGNALS:
                tactic_text = None
            if tactic_text:
                msg.tactic = tactic_text
                msg.is_decomposition = bool(getattr(latest, "is_decomposition", False))
                if self._trace:
                    self._trace.log(
                        agent=self._agent.name, role="tactic_bridge",
                        content=(f"propagated tactic to msg "
                                 f"(decomp={msg.is_decomposition}, "
                                 f"len={len(tactic_text)}): "
                                 f"{tactic_text[:80]}"),
                    )

        # B.3: Propagate plan from ProofState into message after Coordinator runs
        if self._agent.name == "CoordinatorAgent" and self._state and not msg.plan:
            if self._state.plan:
                msg.plan = list(self._state.plan)

        # F9 (2026-05-17): bridge state._next_agent -> msg.next_agent. Without
        # this, tools like request_director_guidance that call
        # state.designate_next_agent("director") have no effect on routing —
        # the workflow only inspects msg.next_agent. C37 DEMO 15/16/17 showed
        # the Coordinator had no functional path to invoke the Director.
        if self._state:
            designated = self._state.consume_next_agent_designation()
            if designated:
                # Map agent-class names to the lowercase routing tokens used
                # by the switch-case edges (director / tactic / coordinator /
                # critic / search).
                routing_token = designated.lower().replace("agent", "")
                msg.next_agent = routing_token
                if self._trace:
                    self._trace.log(
                        agent=self._agent.name, role="route_designate",
                        content=(f"designating next_agent={routing_token} "
                                 f"(from state)"),
                    )

        # Director call tracking
        if self._agent.name == "DirectorAgent":
            msg.director_calls += 1
            # F9: record that Director actually ran, so the intractable
            # gate sees a genuine consultation (not just a request).
            if self._state:
                self._state.director_consulted = True
                self._state.director_consulted_count += 1
            if self._trace:
                self._trace.log(
                    agent="DirectorAgent", role="director_call",
                    content=f"director call {msg.director_calls}/3",
                )

            # B2a (issue #1224): Parse Director output for identifiers the
            # Director explicitly flags as absent. Pattern examples:
            #   "identifier X doesn't exist"
            #   "X is absent from Mathlib"
            #   "X not found"
            #   "Mathlib doesn't have X"
            # Store them so TacticAgent gets a warning to NOT try them.
            import re as _re
            _absent_patterns = [
                r"identifier\s+(\S+)\s+(?:doesn'?t|does not)\s+exist",
                r"(\S+)\s+is\s+absent\s+from\s+Mathlib",
                r"(\S+)\s+not\s+found(?:\s+in\s+Mathlib)?",
                r"Mathlib\s+(?:doesn'?t|does not)\s+have\s+(\S+)",
                r"no\s+lemma\s+(?:called\s+)?['\"]?(\S+?)['\"]?",
                r"(\S+)\s+is\s+not\s+in\s+Mathlib",
            ]
            absent = []
            for pat in _absent_patterns:
                for m in _re.finditer(pat, response_text, _re.IGNORECASE):
                    ident = m.group(1).strip("`'\".,;:)")
                    if ident and ident not in absent and len(ident) < 60:
                        absent.append(ident)
            if absent:
                # P3 (Epic #1453): accumulate rather than replace. Previous
                # Director calls may have flagged identifiers that the current
                # call doesn't mention. Merging ensures TacticAgent always
                # sees the full blocklist.
                if msg.absent_identifiers is None:
                    msg.absent_identifiers = absent
                else:
                    for ident in absent:
                        if ident not in msg.absent_identifiers:
                            msg.absent_identifiers.append(ident)
                if self._trace:
                    self._trace.log(
                        agent="DirectorAgent", role="absent_identifiers",
                        content=f"flagged absent: {absent}",
                    )

        # B2 (issue #1224): Track SearchAgent consultations so the
        # intractable gate can require at least one SearchAgent pass
        # before abandoning a sorry.
        if self._agent.name == "SearchAgent":
            if self._state:
                self._state.search_agent_consulted = True
            if self._trace:
                self._trace.log(
                    agent="SearchAgent", role="search_consulted",
                    content="SearchAgent ran — intractable gate satisfied",
                )

        # F5: Coordinator can mark the current sorry intractable. End the
        # session cleanly so we don't waste iterations on a known-dead goal.
        if (self._state and getattr(self._state, "intractable", False)
                and not msg.intractable):
            msg.intractable = True
            msg.intractable_reason = getattr(
                self._state, "intractable_reason", None
            )
            msg.content = response_text
            if self._trace:
                self._trace.log(
                    agent=self._agent.name, role="intractable_propagate",
                    content=(f"yielding session: "
                             f"{msg.intractable_reason or '(no reason)'}"),
                )
            await ctx.yield_output(msg)
            return

        # Agent output becomes the new content
        msg.content = response_text

        if self._trace:
            self._trace.log(
                agent=self._agent.name, role="respond",
                content=response_text[:100],
            )

        await ctx.send_message(msg)

    @staticmethod
    def _extract_response_text(response) -> str:
        """Extract a useful text payload from an AgentResponse.

        Prior implementation grabbed only `response.messages[-1].text`. Two
        problems with that:
          (a) When the final message is a function_call (no text), `last.text`
              is empty and the burned-budget guard fires even if the agent
              produced perfectly fine assistant text earlier in the run.
          (b) When the model emits text + tool_calls in the same turn, the
              last message is the assistant text — but if the framework appends
              a result-sentinel message, the actual reasoning is lost.

        Strategy: walk all messages in reverse, collect any non-empty `.text`
        from text-bearing contents, and concatenate the most recent ones until
        we have something to send downstream. If nothing surfaces, return ""
        and let the caller's burned-response guard fire.
        """
        if not hasattr(response, 'messages') or not response.messages:
            return ""

        # First pass: prefer the last assistant text message.
        for msg in reversed(response.messages):
            text = getattr(msg, 'text', None)
            if text and text.strip():
                return text

        # Second pass: synthesize a summary from function_call payloads so
        # the downstream agent at least sees what tools were invoked even if
        # the final assistant text was empty.
        tool_calls: list[str] = []
        for msg in response.messages:
            contents = getattr(msg, 'contents', None) or []
            for content in contents:
                ctype = getattr(content, 'type', '')
                if ctype == 'function_call':
                    fname = getattr(content, 'name', '?') or '?'
                    fargs = getattr(content, 'arguments', '') or ''
                    tool_calls.append(f"  - {fname}({str(fargs)[:120]})")

        if tool_calls:
            return ("[harness summary] previous agent emitted no final text "
                    "but invoked these tools:\n" + "\n".join(tool_calls[-5:]))

        return ""


class VerifyExecutor(Executor):
    """Non-LLM executor: verifies tactics via Lean compiler.

    This is NOT an agent — it calls verify_sorry_replacement() directly.
    No LLM call needed to run `lake env lean`.
    """

    def __init__(self, sorry_context: SorryContext, imports: str,
                 trace: TraceLogger = None, kb: Optional[ProofKnowledgeBase] = None,
                 escalation_threshold: int = 5, has_director: bool = False,
                 director_max_calls: int = 3, **kwargs):
        super().__init__(id="verify_executor", **kwargs)
        self._sorry_ctx = sorry_context
        self._imports = imports
        self._trace = trace
        # B.1 ProofKnowledgeBase: record successful tactics so future sessions
        # can warm-start. Same JSON file that SearchTools reads.
        self._kb = kb or ProofKnowledgeBase()
        # F1 (2026-05-11): Deterministic Critic escalation. PR #923 attempted
        # to encode the "after 3 BUILD-FAIL on same line, escalate" rule in the
        # Critic prompt; iter 5-7 BG runs showed the model still routes back to
        # TacticAgent on consecutive failures. Encode it here in workflow code
        # so we don't depend on prompt adherence.
        self._consecutive_build_fails = 0
        self._total_fails = 0
        self._escalation_threshold = escalation_threshold
        # F7 (2026-05-15): when the Director lane is wired, F1 escalates
        # DIRECTLY to Director instead of looping through the Coordinator.
        # C34-03 forensic showed: even with Director wired, the Coordinator
        # ran once at session start and never set next_agent="director", so
        # the frontier model was never invoked despite 10+ BUILD-FAILs. The
        # docstring intent "Coordinator (stalled) -> Director -> Tactic" is
        # now hard-coded into F1 routing.
        self._has_director = has_director
        self._director_max_calls = director_max_calls
        # B2c (issue #1224): cumulative fail counter that NEVER resets on
        # decomposition. The existing _consecutive_build_fails resets to 0
        # when TacticAgent submits a decomposition, which means the Director
        # escalation threshold is never reached in sessions with many
        # decompositions. This counter keeps climbing and triggers Director
        # re-escalade after _cumulative_fails_threshold fails regardless.
        self._cumulative_fails = 0
        self._cumulative_fails_threshold = 5
        # Re-search trigger: after this many total fails, force a hint to
        # the Critic that fresh lemmas may be needed. The Critic still makes
        # the routing decision, but the hint makes re-search more likely.
        self._research_hint_threshold = 4
        # Reco 1 (C34-05 postmortem): wall-clock force trigger for Director.
        # Observed: 28-30 BUILD-FAILs with 0 Director invocations because
        # decomposition resets _consecutive_build_fails. If elapsed > 1500s
        # AND total_fails > 10, force Director escalation regardless.
        self._session_start = time.monotonic()
        self._wallclock_director_threshold_s = 1500
        self._wallclock_director_min_fails = 10
        # P1 (Epic #1453): no-progress compile detector. Forensic showed 13+
        # iterations where TacticAgent compiles successfully but sorry count
        # doesn't decrease — the agent probes the goal state without making
        # actual edits. Track consecutive iterations with neither proof found
        # nor sorry reduction. >=3 -> force Director/yield.
        self._consecutive_noprogress = 0
        self._noprogress_threshold = 3
        self._original_sorry_count: Optional[int] = None

    @handler
    async def handle(self, msg: ProofMessage, ctx: WorkflowContext[ProofMessage]) -> None:
        """Verify the tactic submitted by TacticAgent."""
        from .lean_utils import verify_sorry_replacement

        # P1: initialize original sorry count on first call
        if self._original_sorry_count is None:
            self._original_sorry_count = msg.sorry_count or 0

        if not msg.tactic:
            msg.error = "No tactic submitted"
            msg.next_agent = "tactic"
            await ctx.send_message(msg)
            return

        # Guard: reject tactics that contain a bare `sorry` token at the
        # statement level (LLM giveup pattern). Comments and strings are
        # excluded so a proof legitimately mentioning the word in
        # documentation isn't misclassified. Without this guard the LLM
        # can submit `-- explanation\n  sorry` as a "proof" and burn a
        # compile cycle before VerifyExecutor rejects it via sorry-count.
        # 2026-05-12 Shapley_2daf67cb86_L570 trace: TacticAgent did exactly
        # this — long comment block followed by literal `sorry`, build_fail
        # outcome already correct but wasted ~30s on the compile.
        import re as _re
        _stripped = _re.sub(r"--.*", "", msg.tactic)  # strip line comments
        _stripped = _re.sub(r"/-(.|\n)*?-/", "", _stripped)  # block comments
        if _re.search(r"(^|\s)sorry(\s|$)", _stripped):
            msg.error = (
                "Tactic contains a literal `sorry` token (LLM giveup pattern). "
                "A proof must close the goal with real tactics. Routing back "
                "to Coordinator to revise attack plan."
            )
            msg.error_type = "tactic_contains_sorry"
            msg.next_agent = "coordinator"
            self._consecutive_build_fails += 1
            if self._trace:
                self._trace.log(
                    agent="VerifyExecutor", role="sorry_guard",
                    content=f"rejected tactic containing sorry: {msg.tactic[:120]}",
                )
            await ctx.send_message(msg)
            return

        # P1 latch-success (Epic #1453, 2026-05-23 forensic): detect the case
        # where TacticAgent has ALREADY proved the target in-place before this
        # verify runs. tools.file_replace_lines edits the REAL target file on
        # disk (tools.py:1091) and its own build_check already passed, but
        # SorryContext.sorry_line is frozen at session start (provers.py:203)
        # and is NEVER updated. The downstream verify_sorry_replacement then
        # finds no sorry at the frozen line, P5-relocates to a nearest
        # UNRELATED sorry, injects msg.tactic there -> goal mismatch ->
        # spurious tactic_failed that MASKS a genuine proof. Latch here, before
        # that doomed re-verify, when all three hold (else fall through to the
        # existing verify -> P5 path preserved, no regression):
        #   1. the frozen target line no longer contains "sorry"
        #   2. the current raw sorry count is STRICTLY below the session-start
        #      count (full_file snapshot) -> distinguishes "a sorry was proved"
        #      from "lines merely shifted" (a shift leaves the count unchanged)
        #   3. a confirming build of the ACTUAL file succeeds
        # Cost: one file read + count per verify; a build only in the rare
        # in-place-proof case (conditions 1+2), and that build replaces the
        # doomed relocated one (net-zero) and is cache-eligible by content hash.
        try:
            from pathlib import Path as _LatchPath
            from .verifier import get_verifier as _latch_get_verifier
            _latch_fp = self._sorry_ctx.filepath
            _latch_cur = _LatchPath(_latch_fp).read_text(encoding="utf-8")
            _latch_lines = _latch_cur.split("\n")
            _latch_target = self._sorry_ctx.sorry_line
            _latch_line_clear = (
                1 <= _latch_target <= len(_latch_lines)
                and "sorry" not in _latch_lines[_latch_target - 1]
            )
            _latch_orig = (
                self._sorry_ctx.full_file.count("sorry")
                if getattr(self._sorry_ctx, "full_file", "")
                else (self._original_sorry_count or 0)
            )
            _latch_now = _latch_cur.count("sorry")
            if _latch_line_clear and _latch_now < _latch_orig:
                _latch_verifier = _latch_get_verifier(
                    str(_LatchPath(_latch_fp).parent.parent))
                _latch_rel = (f"{_LatchPath(_latch_fp).parent.name}/"
                              f"{_LatchPath(_latch_fp).name}")
                _latch_build = _latch_verifier.verify_project_file(_latch_rel)
                # Build-aware re-count: a passing build can still emit
                # "declaration uses sorry" warnings when the agent swapped an
                # explicit `sorry` for a search tactic (apply?/exact?/
                # solve_by_elim) that found nothing — an IMPLICIT sorry that the
                # text count above misses (#1500). Fold the warning count the
                # same way tools.compile() does and require the EFFECTIVE count
                # to have dropped below the session-start count, else the
                # "in-place proof" is illusory and we must fall through to the
                # normal verify path.
                from .tools import _count_sorries_from_build_output
                _latch_build_warn = _count_sorries_from_build_output(
                    _latch_build.get("raw_output", ""))
                _latch_effective = max(_latch_now, _latch_build_warn)
                if _latch_build.get("success") and _latch_effective < _latch_orig:
                    msg.proof_found = True
                    self._consecutive_build_fails = 0
                    self._consecutive_noprogress = 0
                    if self._trace:
                        self._trace.log(
                            agent="VerifyExecutor", role="verify",
                            content=(f"PROOF FOUND (in-place latch): frozen line "
                                     f"{_latch_target} clear, sorry {_latch_orig}"
                                     f"->{_latch_now}, clean build OK"),
                            tool_name="verify_project_file",
                            tool_result="success=True",
                        )
                    try:
                        self._kb.record_success(
                            goal=self._sorry_ctx.goal_state or "",
                            tactic=msg.tactic,
                            theorem="",
                            file=f"{_latch_fp}:{_latch_target}",
                        )
                    except Exception:
                        pass
                    await ctx.yield_output(msg)
                    return
        except Exception as _latch_err:
            if self._trace:
                self._trace.log(
                    agent="VerifyExecutor", role="latch_error",
                    content=(f"in-place latch check failed, falling through "
                             f"to verify_sorry_replacement: {_latch_err}"),
                )

        result = verify_sorry_replacement(
            filepath=self._sorry_ctx.filepath,
            sorry_line=self._sorry_ctx.sorry_line,
            replacement=msg.tactic,
        )

        if result["success"]:
            msg.proof_found = True
            self._consecutive_build_fails = 0
            self._consecutive_noprogress = 0  # P1: real progress
            if self._trace:
                self._trace.log(
                    agent="VerifyExecutor", role="verify",
                    content=f"PROOF FOUND: {msg.tactic[:80]}",
                    tool_name="verify_sorry_replacement",
                    tool_result="success=True",
                )
            try:
                self._kb.record_success(
                    goal=self._sorry_ctx.goal_state or "",
                    tactic=msg.tactic,
                    theorem="",  # SorryContext has no theorem name; line+file is enough
                    file=f"{self._sorry_ctx.filepath}:{self._sorry_ctx.sorry_line}",
                )
                if self._trace:
                    self._trace.log(
                        agent="VerifyExecutor", role="kb_record",
                        content=(f"recorded {self._sorry_ctx.filepath}:"
                                 f"{self._sorry_ctx.sorry_line} -> "
                                 f"{msg.tactic[:60]} (kb_size={self._kb.size})"),
                    )
            except Exception as e:
                if self._trace:
                    self._trace.log(
                        agent="VerifyExecutor", role="kb_record_error",
                        content=f"kb record failed: {e}",
                    )
            await ctx.yield_output(msg)
            return

        # Check if decomposition introduced new sorry
        new_sorry_count = self._count_sorry(msg.tactic)
        if msg.is_decomposition and new_sorry_count > msg.sorry_count:
            msg.sorry_count = new_sorry_count
            msg.error = f"Decomposition: {msg.sorry_count} sorry remaining"
            msg.next_agent = "tactic"
            # Decomposition is progress (new sub-goals to attack), reset.
            self._consecutive_build_fails = 0
            # P1: decomposition with sorry reduction is structural progress
            if new_sorry_count < self._original_sorry_count:
                self._consecutive_noprogress = 0
        else:
            msg.error = result.get("errors", "")[:500]
            msg.error_type = result.get("error_type", "unknown")
            # Reco 1: filter probe errors from build-fail counter.
            # "GoalExtract exact ()" is a Lean server transient, not a tactic failure.
            is_probe_error = "GoalExtract" in (msg.error or "")
            if not is_probe_error:
                self._consecutive_build_fails += 1
                self._total_fails += 1
                self._cumulative_fails += 1  # B2c: never resets
            elif self._trace:
                self._trace.log(
                    agent="VerifyExecutor", role="probe_filter",
                    content=f"filtered GoalExtract probe error, counters unchanged",
                )
            # Reco 1: wall-clock force trigger — if elapsed > 1500s AND
            # total_fails > 10, force Director regardless of per-line counter.
            elapsed = time.monotonic() - self._session_start
            wallclock_trigger = (
                elapsed > self._wallclock_director_threshold_s
                and self._total_fails >= self._wallclock_director_min_fails
                and self._has_director
                and msg.director_calls < self._director_max_calls
            )
            if wallclock_trigger:
                msg.next_agent = "director"
                msg.error = (
                    f"[F8 wall-clock escalation -> Director] "
                    f"{elapsed:.0f}s elapsed, {self._total_fails} total BUILD-FAIL. "
                    f"Consecutive counter was reset by decompositions. "
                    f"Forcing Director invocation. Last error: {msg.error}"
                )
                if self._trace:
                    self._trace.log(
                        agent="VerifyExecutor", role="f8_wallclock_escalation",
                        content=(f"elapsed={elapsed:.0f}s > "
                                 f"{self._wallclock_director_threshold_s}s, "
                                 f"total_fails={self._total_fails} >= "
                                 f"{self._wallclock_director_min_fails}, "
                                 f"forcing Director (calls={msg.director_calls}/"
                                 f"{self._director_max_calls})"),
                    )
                self._consecutive_build_fails = 0
            # B2c (issue #1224): cumulative fail re-escalade. Decompositions
            # reset _consecutive_build_fails to 0, which means the F1
            # escalation threshold (default 5) is never reached when the
            # prover alternates between decompositions and build-fails. This
            # counter never resets and forces Director re-escalade at a fixed
            # threshold. This fires ONLY if the other escalation paths haven't
            # already triggered (wallclock or consecutive).
            elif (self._cumulative_fails >= self._cumulative_fails_threshold
                    and self._has_director
                    and msg.director_calls < self._director_max_calls):
                msg.next_agent = "director"
                msg.error = (
                    f"[B2c cumulative re-escalade -> Director] "
                    f"{self._cumulative_fails} cumulative BUILD-FAIL "
                    f"(consecutive was reset to {self._consecutive_build_fails} "
                    f"by decompositions). Forcing Director invocation. "
                    f"Last error: {msg.error}"
                )
                if self._trace:
                    self._trace.log(
                        agent="VerifyExecutor", role="b2c_cumulative_escalation",
                        content=(f"cumulative_fails={self._cumulative_fails} >= "
                                 f"threshold={self._cumulative_fails_threshold}, "
                                 f"consecutive={self._consecutive_build_fails} "
                                 f"(reset by decomp), forcing Director "
                                 f"(calls={msg.director_calls}/"
                                 f"{self._director_max_calls})"),
                    )
                self._consecutive_build_fails = 0
                # Reset cumulative so we don't re-trigger immediately
                self._cumulative_fails = 0
            elif self._consecutive_build_fails >= self._escalation_threshold:
                # F1: deterministic escalation. Critic prompt heuristics
                # aren't reliable enough — when the same sorry_line has
                # failed N times in a row, the attack plan is wrong, not
                # the local tactic.
                # F7 (2026-05-15): if the Director lane is wired and budget
                # not spent, route DIRECTLY to Director (Opus 4.7). The
                # Coordinator already ran once at session start and won't
                # produce a new attack plan from another invocation — only
                # the frontier model has a chance on stuck targets. C34-03
                # forensic: Director was wired but never invoked because
                # Coordinator never set next_agent="director" itself.
                if (self._has_director
                        and msg.director_calls < self._director_max_calls):
                    msg.next_agent = "director"
                    escalation_target = "Director"
                    escalation_role = "f1_escalation_director"
                else:
                    msg.next_agent = "coordinator"
                    escalation_target = "Coordinator"
                    escalation_role = "f1_escalation_coordinator"
                escalation_note = (
                    f"[F1 escalation -> {escalation_target}] "
                    f"{self._consecutive_build_fails} consecutive BUILD-FAIL "
                    f"on sorry_line {self._sorry_ctx.sorry_line}. Local "
                    f"tactics aren't converging. Last error: {msg.error}"
                )
                msg.error = escalation_note
                if self._trace:
                    self._trace.log(
                        agent="VerifyExecutor", role=escalation_role,
                        content=(f"consecutive_fails="
                                 f"{self._consecutive_build_fails} >= "
                                 f"threshold={self._escalation_threshold}, "
                                 f"forcing route to {escalation_target} "
                                 f"(director_calls={msg.director_calls}/"
                                 f"{self._director_max_calls}, "
                                 f"has_director={self._has_director})"),
                    )
                # Reset so we don't immediately re-escalate on the next fail;
                # give the new agent a fresh window of `threshold` attempts.
                self._consecutive_build_fails = 0
                self._total_fails = 0  # reset after coordinator escalation
            else:
                # P1 (Epic #1453): no-progress detection. Increment counter
                # when iteration produces neither proof nor sorry reduction.
                # >=3 consecutive no-progress -> force Director/yield instead
                # of default critic route. Forensic: 13+ iterations wasted on
                # targets where TacticAgent probed goals without editing.
                self._consecutive_noprogress += 1
                if (self._consecutive_noprogress >= self._noprogress_threshold
                        and self._has_director
                        and msg.director_calls < self._director_max_calls):
                    msg.next_agent = "director"
                    msg.error = (
                        f"[P1 no-progress -> Director] "
                        f"{self._consecutive_noprogress} consecutive iterations "
                        f"with no sorry reduction. TacticAgent is probing goals "
                        f"without making edits. Forcing Director for strategic "
                        f"guidance. Last error: {msg.error}"
                    )
                    if self._trace:
                        self._trace.log(
                            agent="VerifyExecutor", role="p1_noprogress_escalation",
                            content=(f"consecutive_noprogress="
                                     f"{self._consecutive_noprogress} >= "
                                     f"threshold={self._noprogress_threshold}, "
                                     f"forcing Director "
                                     f"(calls={msg.director_calls}/"
                                     f"{self._director_max_calls})"),
                        )
                    self._consecutive_noprogress = 0
                    self._consecutive_build_fails = 0
                elif self._consecutive_noprogress >= self._noprogress_threshold:
                    # No Director available or budget spent -> yield
                    msg.error += (
                        f"\n[P1 no-progress] {self._consecutive_noprogress} "
                        f"consecutive iterations without sorry reduction. "
                        f"Yielding to avoid wasting compute."
                    )
                    self._consecutive_noprogress = 0
                    if self._trace:
                        self._trace.log(
                            agent="VerifyExecutor", role="p1_noprogress_yield",
                            content=(f"consecutive_noprogress="
                                     f"{self._consecutive_noprogress}, no Director "
                                     f"available, yielding"),
                        )
                    await ctx.yield_output(msg)
                    return
                else:
                    msg.next_agent = "critic"
                    # Re-search hint: if total fails exceed threshold, nudge the
                    # Critic toward SearchAgent for fresh lemma analysis.
                    if self._total_fails >= self._research_hint_threshold:
                        msg.error += (
                            f"\n[HINT] {self._total_fails} total BUILD-FAIL so far. "
                            f"Consider routing to SearchAgent for fresh lemma candidates "
                            f"— the current set may be insufficient."
                        )

        if self._trace:
            self._trace.log(
                agent="VerifyExecutor", role="verify",
                content=f"tactic={msg.tactic[:60]} -> {msg.error_type or 'decomp'}",
                tool_name="verify_sorry_replacement",
                tool_result=f"success=False, error_type={msg.error_type}",
            )

        await ctx.send_message(msg)

    def _count_sorry(self, tactic: str) -> int:
        content = self._sorry_ctx.full_file
        lines = content.split("\n")
        sorry_idx = self._sorry_ctx.sorry_line - 1
        indent = self._sorry_ctx.indentation
        indent_str = " " * indent
        replacement_lines = [indent_str + l.strip() for l in tactic.strip().split("\n") if l.strip()]
        new_lines = lines[:sorry_idx] + replacement_lines + lines[sorry_idx + 1:]
        return "\n".join(new_lines).count("sorry")


class DiagnosisExecutor(Executor):
    """Hybrid: LLM DiagnosisAgent with mechanical VerifyExecutor fallback.

    When the DiagnosisAgent fails (timeout, crash), permanently switches to
    the mechanical VerifyExecutor. Agent-driven routing: when the DiagnosisAgent
    specifies next_agent in assess_structural_progress, that routing takes
    precedence. Otherwise falls back to VerifyExecutor's routing logic.
    """

    def __init__(self, diagnosis_agent_executor: AgentExecutor,
                 fallback_verify: VerifyExecutor,
                 diagnosis_timeout_s: int = 60,
                 state: "ProofState" = None, **kwargs):
        super().__init__(id="diagnosis_executor", **kwargs)
        self._diagnosis = diagnosis_agent_executor
        self._fallback = fallback_verify
        self._diagnosis_timeout_s = diagnosis_timeout_s
        self._fallback_active = False
        self._state = state
        self._session_start = time.monotonic()

    @handler
    async def handle(self, msg: ProofMessage, ctx: WorkflowContext[ProofMessage]) -> None:
        # Update shared resource state so agents can make wrap-up decisions
        if self._state:
            self._state.elapsed_seconds = time.monotonic() - self._session_start
            if msg.max_iterations > 0:
                self._state.remaining_iterations = max(0, msg.max_iterations - msg.iteration)

        if self._fallback_active:
            await self._fallback.handle(msg, ctx)
            return

        # Run DiagnosisAgent with timeout
        try:
            # The DiagnosisAgent needs context about what just happened
            diagnosis_prompt = (
                f"Diagnose the latest proof attempt.\n\n"
                f"Previous agent output:\n{msg.content[:2000]}\n\n"
                f"Tactic attempted: {msg.tactic or '(none)'}\n"
                f"Current sorry count: {msg.sorry_count}\n"
                f"Iteration: {msg.iteration}/{msg.max_iterations}\n"
            )
            msg_copy = ProofMessage(
                content=diagnosis_prompt,
                iteration=msg.iteration,
                sorry_count=msg.sorry_count,
                tactic=msg.tactic,
                error=msg.error,
                max_iterations=msg.max_iterations,
                plan=msg.plan,
                intractable=msg.intractable,
                intractable_reason=msg.intractable_reason,
                director_calls=msg.director_calls,
                absent_identifiers=msg.absent_identifiers,
                next_agent=msg.next_agent,
            )

            try:
                result = await asyncio.wait_for(
                    self._diagnosis.handle(msg_copy, ctx),
                    timeout=self._diagnosis_timeout_s,
                )
            except asyncio.TimeoutError:
                raise TimeoutError(
                    f"DiagnosisAgent timed out after {self._diagnosis_timeout_s}s"
                )

            # If DiagnosisAgent set routing via next_agent, propagate it.
            # The assess_structural_progress tool stores the opinion in state.
            # We propagate the routing token from the agent's response.
            if msg_copy.next_agent and msg_copy.next_agent != msg.next_agent:
                msg.next_agent = msg_copy.next_agent

            # Propagate diagnosis fields
            msg.diagnosis_assessment = msg_copy.diagnosis_assessment
            msg.is_structural_progress = msg_copy.is_structural_progress
            msg.diagnosis_reason = msg_copy.diagnosis_reason
            msg.agent_opinion = msg_copy.agent_opinion
            msg.content = msg_copy.content

            await ctx.send_message(msg)

        except Exception as e:
            # First failure — permanently switch to mechanical fallback
            self._fallback_active = True
            if hasattr(self._diagnosis, '_trace') and self._diagnosis._trace:
                self._diagnosis._trace.log(
                    agent="DiagnosisExecutor", role="fallback",
                    content=f"DiagnosisAgent failed ({e}), switching to mechanical fallback",
                )
            await self._fallback.handle(msg, ctx)


class MergeSearchExecutor(Executor):
    """Aggregates results from multiple concurrent SearchAgents.

    Receives a ``list[ProofMessage]`` via fan-in, deduplicates discovered
    lemmas, and forwards a single merged ProofMessage to the TacticAgent.
    """

    def __init__(self, trace: TraceLogger = None, **kwargs):
        super().__init__(id="merge_search", **kwargs)
        self._trace = trace

    @handler
    async def handle(self, messages: list[ProofMessage], ctx: WorkflowContext) -> ProofMessage:
        if not messages:
            return
        # Use the first message as base, merge content from others
        base = messages[0]
        merged_parts = []
        all_lemmas = set()
        for msg in messages:
            if msg.content:
                merged_parts.append(msg.content)
            if hasattr(msg, '_discovered_lemmas') and msg._discovered_lemmas:
                all_lemmas.update(msg._discovered_lemmas)

        merged = ProofMessage(
            content="\n\n---\n\n".join(merged_parts) if merged_parts else base.content,
            iteration=max(m.iteration for m in messages),
            sorry_count=base.sorry_count,
            tactic=base.tactic,
            error=base.error,
            error_type=base.error_type,
            is_decomposition=base.is_decomposition,
            proof_found=base.proof_found,
            next_agent="tactic",
            max_iterations=base.max_iterations,
            plan=base.plan,
            intractable=base.intractable,
            intractable_reason=base.intractable_reason,
            director_calls=base.director_calls,
            absent_identifiers=base.absent_identifiers,
        )
        if self._trace:
            n = len(messages)
            self._trace.log(
                agent="MergeSearch", role="merge",
                content=f"merged {n} search results, forwarding to tactic",
            )
        await ctx.send_message(merged)


class ProofWorkflowBuilder:
    """Builds the multi-agent proof workflow graph.

    Optional DirectorAgent: external LLM (e.g. GPT-5.5 via OpenRouter) that
    provides strategic tactic suggestions when local agents stall. Inserted
    into the graph after F1 Coordinator escalation, so the flow becomes:
        Coordinator (stalled) -> Director -> Tactic (retry with guidance)
    The director has no tools — pure text output with APPROACH + TACTICS.
    Budget: max 3 calls per session, tracked via ``msg.director_calls``.
    """

    def __init__(self, search_agent: Agent, tactic_agent: Agent,
                 critic_agent: Agent, coordinator_agent: Agent,
                 sorry_context: SorryContext, imports: str,
                 trace: TraceLogger = None, state: "ProofState" = None,
                 kb: Optional[ProofKnowledgeBase] = None,
                 director_agent: Optional[Agent] = None,
                 diagnosis_agent: Optional[Agent] = None,
                 concurrent_search_count: int = 0,
                 extra_search_agents: Optional[list] = None):
        self._search = AgentExecutor(search_agent, trace=trace, state=state)
        # B.7: additional SearchAgents for parallel lemma discovery.
        # When concurrent_search_count > 0, extra_search_agents provides
        # the additional Agent instances (created in provers.py with
        # independent SearchTools). The workflow uses fan-out/fan-in to
        # run them concurrently and merge results before TacticAgent.
        self._concurrent_search_count = concurrent_search_count
        self._extra_search_execs: list = []
        if extra_search_agents:
            for i, agent in enumerate(extra_search_agents):
                self._extra_search_execs.append(
                    AgentExecutor(agent, trace=trace, state=state,
                                  name=f"SearchAgent-{i+2}")
                )
        self._tactic = AgentExecutor(tactic_agent, trace=trace, state=state)
        self._critic = AgentExecutor(critic_agent, trace=trace, state=state)
        self._coordinator = AgentExecutor(coordinator_agent, trace=trace, state=state)
        # F7 (2026-05-15): Director must be constructed BEFORE the verify
        # executor so we can hand the verify executor a `has_director` flag.
        # The flag drives the F1 escalation branch — if the Director lane is
        # wired, F1 sends the message straight to Director instead of looping
        # through Coordinator (which the C34-03 forensic showed never
        # produces a `next_agent="director"` route on its own).
        self._director: Optional[AgentExecutor] = (
            AgentExecutor(director_agent, trace=trace, state=state,
                          timeout_s=120)
            if director_agent else None
        )
        self._director_max_calls = 3
        self._verify = VerifyExecutor(
            sorry_context, imports, trace, kb=kb,
            has_director=bool(self._director),
            director_max_calls=self._director_max_calls,
        )
        # Feature 3: DiagnosisAgent replaces VerifyExecutor when provided.
        # DiagnosisExecutor wraps the LLM agent with mechanical fallback.
        self._diagnosis_executor: Optional[DiagnosisExecutor] = None
        if diagnosis_agent:
            diagnosis_agent_exec = AgentExecutor(
                diagnosis_agent, trace=trace, state=state,
                timeout_s=60,
            )
            self._diagnosis_executor = DiagnosisExecutor(
                diagnosis_agent_exec, self._verify,
                diagnosis_timeout_s=60,
                state=state,
            )
        # B.7: MergeSearchExecutor for concurrent search fan-in.
        if self._concurrent_search_count > 0 and self._extra_search_execs:
            self._merge_search = MergeSearchExecutor(trace=trace)
        else:
            self._merge_search = None

    def build(self):
        # B.3: CoordinatorAgent runs FIRST to set attack plan, then routes to
        # search or tactic via the switch-case edge group below. Earlier
        # versions also added explicit ``add_edge`` calls from the coordinator
        # to search and tactic — that duplicated edges declared by
        # ``add_switch_case_edge_group`` and tripped EdgeDuplicationError on
        # ``builder.build()``. The switch-case group is the single source of
        # truth for coordinator routing now.
        builder = WorkflowBuilder(start_executor=self._coordinator)

        # B.7: When concurrent search is enabled, set up fan-out/fan-in:
        #   Default routes -> self._search (primary) -> fan-out to extras
        #   all_search -> merge -> tactic
        # Otherwise, single search -> tactic (original path).
        use_concurrent = (
            self._concurrent_search_count > 0
            and self._extra_search_execs
            and self._merge_search is not None
        )

        if use_concurrent:
            all_search = [self._search] + self._extra_search_execs
            # Primary search fans out to all extra search agents concurrently.
            # When a message reaches self._search (via switch-case Default),
            # it also broadcasts to all extra agents.
            builder.add_fan_out_edges(self._search, self._extra_search_execs)
            # Fan-in: all search agents -> merge -> tactic
            builder.add_fan_in_edges(all_search, self._merge_search)
            builder.add_edge(self._merge_search, self._tactic)
        else:
            # Original single-search path
            builder.add_edge(self._search, self._tactic)

        _verify_node = self._diagnosis_executor or self._verify
        builder.add_edge(self._tactic, _verify_node)

        # Director -> tactic (director suggests tactics, TacticAgent applies)
        if self._director:
            builder.add_edge(self._director, self._tactic)

        # Verify routes via switch-case so the "tactic" backedge and the
        # default critic path don't collide as duplicate edges either. F1
        # (2026-05-11) adds the "coordinator" branch so the deterministic
        # escalation in VerifyExecutor can bypass the Critic entirely.
        # F7 (2026-05-15) adds the "director" branch — when F1 fires and
        # the Director lane is wired with budget remaining, the message is
        # sent straight to the frontier model instead of looping through
        # Coordinator. The Director Case is only added when Director exists,
        # otherwise the conditional target would be unreachable.
        verify_cases = [
            Case(
                condition=lambda msg: (
                    msg.next_agent == "tactic" and not msg.proof_found
                ),
                target=self._tactic,
            ),
            Case(
                condition=lambda msg: msg.next_agent == "coordinator",
                target=self._coordinator,
            ),
        ]
        if self._director:
            verify_cases.append(
                Case(
                    condition=lambda msg: (
                        msg.next_agent == "director"
                        and msg.director_calls < self._director_max_calls
                    ),
                    target=self._director,
                )
            )
        verify_cases.append(Default(target=self._critic))
        builder.add_switch_case_edge_group(
            source=_verify_node,
            cases=verify_cases,
        )

        # Critic conditional routing. Default -> primary search agent.
        # B.7: fan_out_edges from _search to extras are already registered
        # above; switch-case Default targets _search which triggers broadcast.
        builder.add_switch_case_edge_group(
            source=self._critic,
            cases=[
                Case(
                    condition=lambda msg: msg.next_agent == "tactic",
                    target=self._tactic,
                ),
                Case(
                    condition=lambda msg: msg.next_agent == "coordinator",
                    target=self._coordinator,
                ),
                Default(target=self._search),
            ],
        )

        # Coordinator routing with optional Director escalation.
        if self._director:
            builder.add_switch_case_edge_group(
                source=self._coordinator,
                cases=[
                    Case(
                        condition=lambda msg: (
                            msg.next_agent == "director"
                            and msg.director_calls < self._director_max_calls
                        ),
                        target=self._director,
                    ),
                    Case(
                        condition=lambda msg: msg.next_agent == "tactic",
                        target=self._tactic,
                    ),
                    Default(target=self._search),
                ],
            )
        else:
            builder.add_switch_case_edge_group(
                source=self._coordinator,
                cases=[
                    Case(
                        condition=lambda msg: msg.next_agent == "tactic",
                        target=self._tactic,
                    ),
                    Default(target=self._search),
                ],
            )

        return builder.build()
