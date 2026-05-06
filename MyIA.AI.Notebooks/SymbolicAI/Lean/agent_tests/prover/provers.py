"""Provers: MultiAgentSorryProver and AutonomousProver.

MultiAgentSorryProver uses the WorkflowBuilder graph with 4 specialized agents.
AutonomousProver uses a single agent with full editing powers.
"""

import json
import re
import time
from pathlib import Path
from datetime import datetime
from typing import Optional

from .trace import TraceLogger
from .state import ProofState, SorryContext, ProofPhase
from .lean_utils import extract_sorry_block, get_goal_state, verify_sorry_replacement
from .tools import SearchTools, TacticTools, CriticTools, CoordinatorTools
from .agents import (
    create_search_agent,
    create_tactic_agent,
    create_critic_agent,
    create_coordinator_agent,
)
from .workflow import ProofWorkflowBuilder, ProofMessage
from .instructions import AUTONOMOUS_PROVER_INSTRUCTIONS
from .config import create_client


class MultiAgentSorryProver:
    """Multi-agent sorry replacement using WorkflowBuilder graph.

    4 specialized agents with shared state and conditional routing:
    SearchAgent -> TacticAgent -> VerifyExecutor -> CriticAgent
    with CriticAgent routing back to any agent based on error analysis.
    """

    def __init__(self, trace: TraceLogger, provider: str = "zai",
                 local_provider: str = "local"):
        self.trace = trace
        self.provider = provider
        self.local_provider = local_provider

    async def prove_sorry(self, demo: dict, max_iterations: int = 10) -> dict:
        filepath = demo["file"]
        sorry_line = demo["line"]

        # Read original content
        original_content = Path(filepath).read_text(encoding="utf-8")
        original_sorry_count = original_content.count("sorry")

        # Auto-detect actual sorry line
        actual_sorry_lines = [
            i + 1 for i, line in enumerate(original_content.split("\n"))
            if "sorry" in line
        ]
        if actual_sorry_lines and sorry_line not in actual_sorry_lines:
            sorry_line = actual_sorry_lines[0]
            print(f"  [AutoFix] Configured line {demo['line']} has no sorry. "
                  f"Using actual sorry at line {sorry_line}")

        print(f"\n{'='*70}")
        print(f"MULTI-AGENT PROVER: {demo['name']}")
        print(f"File: {filepath}:{sorry_line}")
        print(f"Original sorry count: {original_sorry_count}")
        print(f"{'='*70}")

        # Extract sorry context
        ctx_data = extract_sorry_block(filepath, sorry_line)
        goal_state = get_goal_state(filepath, sorry_line)

        sorry_ctx = SorryContext(
            filepath=filepath,
            sorry_line=sorry_line,
            goal_state=goal_state,
            context_before=ctx_data.get("context_before", ""),
            context_after=ctx_data.get("context_after", ""),
            indentation=ctx_data.get("indentation", 0),
            indent_str=ctx_data.get("indent_str", ""),
            full_file=ctx_data.get("full_file", original_content),
        )

        # Create shared proof state
        state = ProofState(
            theorem_statement=demo.get("theorem", demo["name"]),
            theorem_name=demo.get("theorem_name", demo["name"]),
            imports=demo.get("imports"),
            current_goal=goal_state or "",
            max_iterations=max_iterations,
        )

        # Create per-agent tools
        search_tools = SearchTools(state, filepath, self.trace)
        tactic_tools = TacticTools(state, filepath, sorry_ctx,
                                   demo.get("imports", ""), self.trace)
        critic_tools = CriticTools(state, self.trace)
        coordinator_tools = CoordinatorTools(state, filepath, self.trace)

        # Create 4 specialized agents
        search_agent = create_search_agent(search_tools, provider=self.local_provider)
        tactic_agent = create_tactic_agent(tactic_tools, provider=self.provider)
        critic_agent = create_critic_agent(critic_tools, provider=self.provider)
        coordinator_agent = create_coordinator_agent(coordinator_tools, provider=self.provider)

        # Build workflow graph
        workflow_builder = ProofWorkflowBuilder(
            search_agent, tactic_agent, critic_agent, coordinator_agent,
            sorry_ctx, demo.get("imports", ""), self.trace,
        )
        workflow = workflow_builder.build()

        # Build initial context message
        context_msg = self._build_context_message(demo, ctx_data, goal_state,
                                                   original_sorry_count, sorry_line)

        initial_msg = ProofMessage(
            content=context_msg,
            sorry_count=original_sorry_count,
        )

        # Run workflow
        session_start = time.time()
        try:
            result = await workflow.run(initial_msg)

            if hasattr(result, 'output') and result.output:
                final_msg = result.output
            else:
                final_msg = initial_msg

            proof_found = getattr(final_msg, 'proof_found', False)
        except Exception as e:
            print(f"  Workflow error: {e}")
            proof_found = False

        total_s = time.time() - session_start

        # Read final state
        final_sorry = Path(filepath).read_text(encoding="utf-8").count("sorry")

        # Restore best state if worse
        if tactic_tools.best_content and tactic_tools.best_sorry_count < final_sorry:
            print(f"  Restoring best ({tactic_tools.best_sorry_count} sorry vs {final_sorry})")
            Path(filepath).write_text(tactic_tools.best_content, encoding="utf-8")
            final_sorry = tactic_tools.best_sorry_count

        success = proof_found or final_sorry == 0 or final_sorry < original_sorry_count

        print(f"\n{'='*60}")
        print(f"RESULT: {'SUCCESS' if success else 'FAILED'}")
        print(f"  Sorry: {original_sorry_count} -> {final_sorry}")
        print(f"  Total time: {total_s:.1f}s")
        print(f"{'='*60}")

        trace_name = f"multi_{demo['name']}_{self.provider}"
        self.trace.save(trace_name)

        return {
            "success": success,
            "proof": state.final_proof,
            "iterations": state.iteration,
            "attempts": len(state.tactic_history),
            "total_s": round(total_s, 1),
            "config": f"multi-{self.provider}",
            "sorry_evolution": f"{original_sorry_count} -> {final_sorry}",
            "best_sorry": tactic_tools.best_sorry_count,
        }

    def _build_context_message(self, demo: dict, ctx_data: dict,
                                goal_state: Optional[str],
                                sorry_count: int, sorry_line: int) -> str:
        parts = [f"Prouve le sorry a la ligne {sorry_line} du fichier {Path(demo['file']).name}."]

        if demo.get("description"):
            parts.append(f"\nDESCRIPTION:\n{demo['description']}")

        if goal_state:
            parts.append(f"\nBUT LEAN (ligne {sorry_line}):\n```\n{goal_state}\n```")

        if ctx_data.get("context_before"):
            parts.append(f"\nCONTEXTE AVANT:\n```\n{ctx_data['context_before'][-500:]}\n```")
        if ctx_data.get("context_after"):
            parts.append(f"\nCONTEXTE APRES:\n```\n{ctx_data['context_after'][:300]}\n```")

        # Auto-discover proven helpers
        try:
            file_text = Path(demo["file"]).read_text(encoding="utf-8")
            proven_helpers = re.findall(r'^(?:theorem|lemma|def)\s+(\w+)', file_text, re.MULTILINE)
            sorry_lines_set = {i + 1 for i, l in enumerate(file_text.split("\n")) if "sorry" in l}
            clean_helpers = []
            for h in proven_helpers[:30]:
                pattern = re.compile(rf'(?:theorem|lemma|def)\s+{re.escape(h)}\b', re.MULTILINE)
                match = pattern.search(file_text)
                if match:
                    start_line = file_text[:match.start()].count("\n") + 1
                    if start_line not in sorry_lines_set:
                        clean_helpers.append(h)
            if clean_helpers:
                parts.append(f"\nHELPERS PROUVES: {', '.join(clean_helpers[:20])}")
        except Exception:
            pass

        parts.append(f"\nSORRY COUNT INITIAL: {sorry_count}")
        parts.append("OBJECTIF: reduire le sorry count ou prouver completement.")

        return "\n".join(parts)


class AutonomousProver:
    """Single-agent prover with full file editing powers.

    Uses one Agent with all tools (file editing, compile, search).
    The orchestrator loop: agent acts -> auto-compile -> feedback -> repeat.
    """

    def __init__(self, trace: TraceLogger, provider: str = "zai"):
        self.trace = trace
        self.provider = provider
        self.config_label = f"auto-{provider}"

    def prove_sorry(self, demo: dict, max_iterations: int = 10,
                    strategic_hints: str = "", agent_timeout_s: int = 300) -> dict:
        filepath = demo["file"]
        sorry_line = demo["line"]

        import asyncio
        from agent_framework import Agent

        original_content = Path(filepath).read_text(encoding="utf-8")
        original_sorry_count = original_content.count("sorry")

        # Auto-detect actual sorry line
        actual_sorry_lines = [
            i + 1 for i, line in enumerate(original_content.split("\n"))
            if "sorry" in line
        ]
        if actual_sorry_lines and sorry_line not in actual_sorry_lines:
            sorry_line = actual_sorry_lines[0]
            print(f"  [AutoFix] Using actual sorry at line {sorry_line}")

        print(f"\n{'='*70}")
        print(f"AUTONOMOUS PROVER: {demo['name']}")
        print(f"File: {filepath}:{sorry_line}")
        print(f"Config: {self.config_label}")
        print(f"Original sorry count: {original_sorry_count}")
        print(f"Agent timeout: {agent_timeout_s}s")
        print(f"{'='*70}")

        # Create shared state and tactic tools (has all file ops)
        state = ProofState(
            theorem_statement=demo.get("theorem", demo["name"]),
            imports=demo.get("imports"),
            max_iterations=max_iterations,
        )

        sorry_ctx_data = extract_sorry_block(filepath, sorry_line)
        goal_state = get_goal_state(filepath, sorry_line)

        sorry_ctx = SorryContext(
            filepath=filepath,
            sorry_line=sorry_line,
            goal_state=goal_state,
            indentation=sorry_ctx_data.get("indentation", 0),
            indent_str=sorry_ctx_data.get("indent_str", ""),
            full_file=sorry_ctx_data.get("full_file", original_content),
        )

        tactic_tools = TacticTools(
            state, filepath, sorry_ctx,
            demo.get("imports", ""), self.trace,
        )

        client = create_client(self.provider, model_key="reasoning")

        agent = Agent(
            client=client,
            instructions=AUTONOMOUS_PROVER_INSTRUCTIONS,
            tools=[
                tactic_tools.file_find_sorry_lines,
                tactic_tools.file_read_lines,
                tactic_tools.file_replace_sorry,
                tactic_tools.file_replace_lines,
                tactic_tools.compile_probe_goal,
                tactic_tools.compile,
                tactic_tools.generate_tactics,
                tactic_tools.submit_tactic,
                tactic_tools.submit_decomposition,
            ],
            name="AutonomousProver",
        )

        # Build initial context
        context_msg = f"Prouve le sorry a la ligne {sorry_line} du fichier {Path(filepath).name}.\n\n"
        if demo.get("description"):
            context_msg += f"DESCRIPTION:\n{demo['description']}\n\n"
        if goal_state:
            context_msg += f"BUT LEAN (ligne {sorry_line}):\n```\n{goal_state}\n```\n\n"

        if strategic_hints:
            context_msg += f"CONSEILS STRATEGIQUES:\n{strategic_hints}\n\n"
        context_msg += (
            f"SORRY COUNT INITIAL: {original_sorry_count}\n"
            f"OBJECTIF: reduire le sorry count.\n"
            f"Commence par find_sorry_lines() puis propose une tactique."
        )

        # Main loop — single event loop for the entire session
        session_start = time.time()
        compile_data = {}

        async def _run_session():
            nonlocal compile_data, context_msg
            loop = asyncio.get_event_loop()

            for iteration in range(1, max_iterations + 1):
                state.iteration = iteration
                iter_start = time.time()
                print(f"\n--- Iteration {iteration}/{max_iterations} ---", flush=True)

                try:
                    response = await asyncio.wait_for(
                        agent.run(context_msg),
                        timeout=agent_timeout_s,
                    )
                    response_text = ""
                    if hasattr(response, 'messages') and response.messages:
                        last = response.messages[-1]
                        response_text = last.text if hasattr(last, 'text') else str(last)
                except asyncio.TimeoutError:
                    print(f"  Agent timeout ({agent_timeout_s}s)", flush=True)
                    response_text = f"TIMEOUT after {agent_timeout_s}s"
                except Exception as e:
                    print(f"  Agent error: {e}", flush=True)
                    response_text = str(e)

                # Auto-compile after each iteration
                current_sorry = Path(filepath).read_text(encoding="utf-8").count("sorry")
                compile_str = tactic_tools.compile()
                try:
                    compile_data = json.loads(compile_str)
                except json.JSONDecodeError:
                    compile_data = {}
                current_sorry = compile_data.get("sorry_count", current_sorry)

                self.trace.log(
                    agent="AutonomousProver", role="iteration",
                    content=f"iter={iteration}, sorry={current_sorry}",
                    duration_s=time.time() - iter_start,
                )

                print(f"  Sorry: {current_sorry}/{original_sorry_count} "
                      f"({time.time() - iter_start:.1f}s)", flush=True)

                # Check termination
                if current_sorry == 0 and compile_data.get("success"):
                    print(f"  ALL SORRY ELIMINATED!", flush=True)
                    state.set_proof_complete("full_file_proof")
                    break

                if current_sorry < original_sorry_count:
                    print(f"  PROGRESS: sorry {original_sorry_count} -> {current_sorry}")

                # Build feedback
                feedback_parts = []
                if compile_data.get("success"):
                    feedback_parts.append("COMPILATION: SUCCES")
                else:
                    errors = compile_data.get("errors", [])
                    if errors:
                        err_summary = "\n".join(
                            f"  L{e['line']}: {e['message'][:120]}" for e in errors[:5]
                        )
                        feedback_parts.append(f"COMPILATION: {len(errors)} ERREURS:\n{err_summary}")

                feedback_parts.append(f"Sorry count: {current_sorry}/{original_sorry_count}")
                context_msg = "\n".join(feedback_parts)

        try:
            asyncio.run(_run_session())
        except RuntimeError:
            # Fallback: reuse existing event loop if nested call
            loop = asyncio.get_event_loop()
            loop.run_until_complete(_run_session())

        total_s = (datetime.now() - state.start_time).total_seconds()
        final_sorry = Path(filepath).read_text(encoding="utf-8").count("sorry")

        # Restore best state if worse
        if tactic_tools.best_content and tactic_tools.best_sorry_count < final_sorry:
            print(f"  Restoring best ({tactic_tools.best_sorry_count} vs {final_sorry})")
            Path(filepath).write_text(tactic_tools.best_content, encoding="utf-8")
            final_sorry = tactic_tools.best_sorry_count

        success = final_sorry == 0 or final_sorry < original_sorry_count

        print(f"\n{'='*60}")
        print(f"RESULT: {'SUCCESS' if success else 'FAILED'}")
        print(f"  Sorry: {original_sorry_count} -> {final_sorry}")
        print(f"  Total time: {total_s:.1f}s")
        print(f"{'='*60}")

        trace_name = f"auto_{demo['name']}_{self.provider}"
        self.trace.save(trace_name)

        return {
            "success": success,
            "proof": state.final_proof,
            "iterations": state.iteration,
            "attempts": len(state.tactic_history),
            "total_s": round(total_s, 1),
            "config": self.config_label,
            "sorry_evolution": f"{original_sorry_count} -> {final_sorry}",
            "best_sorry": tactic_tools.best_sorry_count,
        }
