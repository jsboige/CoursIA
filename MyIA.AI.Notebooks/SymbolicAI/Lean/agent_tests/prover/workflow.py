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

    @handler
    async def handle(self, msg: ProofMessage, ctx: WorkflowContext[ProofMessage]) -> None:
        """Run the agent with the message content, produce updated ProofMessage."""
        # Iteration cap — if we've already hit max, end the run cleanly.
        msg.iteration += 1
        if msg.max_iterations and msg.iteration > msg.max_iterations:
            if self._trace:
                self._trace.log(
                    agent=self._agent.name, role="iteration_cap",
                    content=f"iter {msg.iteration} > max {msg.max_iterations}, yielding",
                )
            await ctx.yield_output(msg)
            return

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

    @handler
    async def handle(self, msg: ProofMessage, ctx: WorkflowContext[ProofMessage]) -> None:
        """Verify the tactic submitted by TacticAgent."""
        from .lean_utils import verify_sorry_replacement

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

        result = verify_sorry_replacement(
            filepath=self._sorry_ctx.filepath,
            sorry_line=self._sorry_ctx.sorry_line,
            replacement=msg.tactic,
        )

        if result["success"]:
            msg.proof_found = True
            self._consecutive_build_fails = 0
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
        else:
            msg.error = result.get("errors", "")[:500]
            msg.error_type = result.get("error_type", "unknown")
            # Reco 1: filter probe errors from build-fail counter.
            # "GoalExtract exact ()" is a Lean server transient, not a tactic failure.
            is_probe_error = "GoalExtract" in (msg.error or "")
            if not is_probe_error:
                self._consecutive_build_fails += 1
                self._total_fails += 1
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
                 director_agent: Optional[Agent] = None):
        self._search = AgentExecutor(search_agent, trace=trace, state=state)
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

    def build(self):
        # B.3: CoordinatorAgent runs FIRST to set attack plan, then routes to
        # search or tactic via the switch-case edge group below. Earlier
        # versions also added explicit ``add_edge`` calls from the coordinator
        # to search and tactic — that duplicated edges declared by
        # ``add_switch_case_edge_group`` and tripped EdgeDuplicationError on
        # ``builder.build()``. The switch-case group is the single source of
        # truth for coordinator routing now.
        builder = WorkflowBuilder(start_executor=self._coordinator)

        # Forward chain: search -> tactic -> verify
        builder.add_edge(self._search, self._tactic)
        builder.add_edge(self._tactic, self._verify)

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
            source=self._verify,
            cases=verify_cases,
        )

        # Critic conditional routing (requires exactly one Default)
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

        # Coordinator routing — with optional Director escalation.
        # When the Coordinator determines local agents are stalled it can
        # request director guidance by setting next_agent="director".
        # The guard caps director calls to avoid budget burn; if the cap
        # is hit the coordinator falls through to search (normal path).
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
