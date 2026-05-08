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


# Default per-agent LLM timeout. External providers (zai/openrouter) can
# stall — without this the entire workflow blocks forever.
DEFAULT_AGENT_TIMEOUT_S = 90


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

        try:
            response = await asyncio.wait_for(
                self._agent.run(content), timeout=self._timeout_s,
            )
            response_text = ""
            if hasattr(response, 'messages') and response.messages:
                last = response.messages[-1]
                response_text = last.text if hasattr(last, 'text') else str(last)
        except asyncio.TimeoutError:
            response_text = (
                f"[Agent timeout after {self._timeout_s}s — provider stalled]"
            )
            if self._trace:
                self._trace.log(
                    agent=self._agent.name, role="timeout",
                    content=f"timeout after {self._timeout_s}s",
                )
        except Exception as e:
            response_text = f"Agent error: {e}"
            if self._trace:
                self._trace.log(
                    agent=self._agent.name, role="error",
                    content=str(e)[:200],
                )

        # B.3: Propagate plan from ProofState into message after Coordinator runs
        if self._agent.name == "CoordinatorAgent" and self._state and not msg.plan:
            if self._state.plan:
                msg.plan = list(self._state.plan)

        # Agent output becomes the new content
        msg.content = response_text

        if self._trace:
            self._trace.log(
                agent=self._agent.name, role="respond",
                content=response_text[:100],
            )

        await ctx.send_message(msg)


class VerifyExecutor(Executor):
    """Non-LLM executor: verifies tactics via Lean compiler.

    This is NOT an agent — it calls verify_sorry_replacement() directly.
    No LLM call needed to run `lake env lean`.
    """

    def __init__(self, sorry_context: SorryContext, imports: str,
                 trace: TraceLogger = None, **kwargs):
        super().__init__(id="verify_executor", **kwargs)
        self._sorry_ctx = sorry_context
        self._imports = imports
        self._trace = trace

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
            if self._trace:
                self._trace.log(
                    agent="VerifyExecutor", role="verify",
                    content=f"PROOF FOUND: {msg.tactic[:80]}",
                    tool_name="verify_sorry_replacement",
                    tool_result="success=True",
                )
            await ctx.yield_output(msg)
            return

        # Check if decomposition introduced new sorry
        new_sorry_count = self._count_sorry(msg.tactic)
        if msg.is_decomposition and new_sorry_count > msg.sorry_count:
            msg.sorry_count = new_sorry_count
            msg.error = f"Decomposition: {msg.sorry_count} sorry remaining"
            msg.next_agent = "tactic"
        else:
            msg.error = result.get("errors", "")[:500]
            msg.error_type = result.get("error_type", "unknown")
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
                 trace: TraceLogger = None, state: "ProofState" = None):
        self._search = AgentExecutor(search_agent, trace=trace, state=state)
        self._tactic = AgentExecutor(tactic_agent, trace=trace, state=state)
        self._critic = AgentExecutor(critic_agent, trace=trace, state=state)
        self._coordinator = AgentExecutor(coordinator_agent, trace=trace, state=state)
        self._verify = VerifyExecutor(sorry_context, imports, trace)

    def build(self):
        # B.3: CoordinatorAgent runs FIRST to set attack plan, then routes to search
        builder = WorkflowBuilder(start_executor=self._coordinator)

        # Coordinator -> Search (initial plan or re-plan)
        builder.add_edge(
            self._coordinator, self._search,
            condition=lambda msg: msg.next_agent in ("search", "coordinator"),
        )
        # Coordinator -> Tactic (direct tactical guidance)
        builder.add_edge(
            self._coordinator, self._tactic,
            condition=lambda msg: msg.next_agent == "tactic",
        )

        # Forward chain: search -> tactic -> verify
        builder.add_edge(self._search, self._tactic)
        builder.add_edge(self._tactic, self._verify)

        # Verify routes: error -> critic, decomposition -> tactic
        builder.add_edge(self._verify, self._critic)
        builder.add_edge(
            self._verify, self._tactic,
            condition=lambda msg: msg.next_agent == "tactic" and not msg.proof_found,
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
