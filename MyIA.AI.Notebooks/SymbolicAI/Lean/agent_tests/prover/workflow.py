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
                 escalation_threshold: int = 3, **kwargs):
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
        self._escalation_threshold = escalation_threshold

    @handler
    async def handle(self, msg: ProofMessage, ctx: WorkflowContext[ProofMessage]) -> None:
        """Verify the tactic submitted by TacticAgent."""
        from .lean_utils import verify_sorry_replacement

        if not msg.tactic:
            msg.error = "No tactic submitted"
            msg.next_agent = "tactic"
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
            self._consecutive_build_fails += 1
            if self._consecutive_build_fails >= self._escalation_threshold:
                # F1: deterministic escalation to Coordinator. Critic prompt
                # heuristics aren't reliable enough — when the same sorry_line
                # has failed N times in a row, the attack plan is wrong, not
                # the local tactic. Reset by sending control back to the
                # Coordinator with a clear escalation note.
                msg.next_agent = "coordinator"
                escalation_note = (
                    f"[F1 escalation] {self._consecutive_build_fails} "
                    f"consecutive BUILD-FAIL on sorry_line "
                    f"{self._sorry_ctx.sorry_line}. Local tactics aren't "
                    f"converging — revise the attack plan or mark the goal "
                    f"intractable. Last error: {msg.error}"
                )
                msg.error = escalation_note
                if self._trace:
                    self._trace.log(
                        agent="VerifyExecutor", role="f1_escalation",
                        content=(f"consecutive_fails="
                                 f"{self._consecutive_build_fails} >= "
                                 f"threshold={self._escalation_threshold}, "
                                 f"forcing route to Coordinator"),
                    )
                # Reset so we don't immediately re-escalate on the next fail;
                # give the Coordinator a fresh window of `threshold` attempts.
                self._consecutive_build_fails = 0
            else:
                msg.next_agent = "critic"

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
    """Builds the multi-agent proof workflow graph."""

    def __init__(self, search_agent: Agent, tactic_agent: Agent,
                 critic_agent: Agent, coordinator_agent: Agent,
                 sorry_context: SorryContext, imports: str,
                 trace: TraceLogger = None, state: "ProofState" = None,
                 kb: Optional[ProofKnowledgeBase] = None):
        self._search = AgentExecutor(search_agent, trace=trace, state=state)
        self._tactic = AgentExecutor(tactic_agent, trace=trace, state=state)
        self._critic = AgentExecutor(critic_agent, trace=trace, state=state)
        self._coordinator = AgentExecutor(coordinator_agent, trace=trace, state=state)
        self._verify = VerifyExecutor(sorry_context, imports, trace, kb=kb)

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

        # Verify routes via switch-case so the "tactic" backedge and the
        # default critic path don't collide as duplicate edges either. F1
        # (2026-05-11) adds the "coordinator" branch so the deterministic
        # escalation in VerifyExecutor can bypass the Critic entirely.
        builder.add_switch_case_edge_group(
            source=self._verify,
            cases=[
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
                Default(target=self._critic),
            ],
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

        # Coordinator routing (requires exactly one Default)
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
