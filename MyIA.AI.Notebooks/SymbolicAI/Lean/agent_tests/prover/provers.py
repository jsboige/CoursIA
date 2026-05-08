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
from .state import ProofState, SorryContext, ProofPhase, PHASE_TRANSITIONS, TacticAttempt
from .lean_utils import (
    extract_sorry_block, get_goal_state, verify_sorry_replacement,
    extract_hypotheses, extract_local_lemmas, build_def_type_warnings,
)
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
        tactic_tools._original_sorry_count = original_sorry_count
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
        self.trace.start_session_span(demo["name"], "multi")
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
        self.trace.end_session_span(success, f"{original_sorry_count}->{final_sorry}")

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

    def __init__(self, trace: TraceLogger, provider: str = "zai",
                 hitl_enabled: bool = True, hitl_threshold: int = 5):
        self.trace = trace
        self.provider = provider
        self.hitl_enabled = hitl_enabled
        self.hitl_threshold = hitl_threshold
        self.config_label = f"auto-{provider}"

    def prove_sorry(self, demo: dict, max_iterations: int = 10,
                    strategic_hints: str = "", agent_timeout_s: int = 0) -> dict:
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
        print(f"Agent timeout: {'none' if agent_timeout_s == 0 else f'{agent_timeout_s}s'}")
        print(f"{'='*70}")

        # Extract sorry context — includes proof_block and goal_hints
        sorry_ctx_data = extract_sorry_block(filepath, sorry_line)
        goal_state = get_goal_state(filepath, sorry_line)
        indent = sorry_ctx_data.get("indentation", 0)
        goal_hints = sorry_ctx_data.get("goal_hints", "")
        proof_block = sorry_ctx_data.get("proof_block", "")

        # Log goal extraction result
        if goal_state:
            print(f"  Goal extracted: {goal_state[:100]}")
        else:
            print(f"  Goal extraction FAILED (indent={indent}). "
                  f"Using proof block context ({len(proof_block)} chars).")
            if goal_hints:
                print(f"  Goal hints from comments: {goal_hints[:100]}")

        # Create shared state and tactic tools
        state = ProofState(
            theorem_statement=demo.get("theorem", demo["name"]),
            imports=demo.get("imports"),
            max_iterations=max_iterations,
        )

        sorry_ctx = SorryContext(
            filepath=filepath,
            sorry_line=sorry_line,
            goal_state=goal_state,
            indentation=indent,
            indent_str=sorry_ctx_data.get("indent_str", ""),
            full_file=sorry_ctx_data.get("full_file", original_content),
        )

        tactic_tools = TacticTools(
            state, filepath, sorry_ctx,
            demo.get("imports", ""), self.trace,
        )
        tactic_tools._original_sorry_count = original_sorry_count

        # Pre-populate rich state
        hypotheses = extract_hypotheses(filepath, sorry_line)
        sorry_line_set = {i + 1 for i, l in enumerate(original_content.split("\n")) if "sorry" in l}
        local_lemmas = extract_local_lemmas(filepath, sorry_line_set)

        state.available_hypotheses = hypotheses
        state.local_lemmas = local_lemmas
        state.best_sorry_count = original_sorry_count

        if goal_state:
            state.sorry_goals[sorry_line] = goal_state
        state.phase = ProofPhase.SEARCH

        # Decide tools — exclude compile_probe_goal when goal extraction failed
        # (probe takes ~40s per call and always fails, agent has proof block in context)
        skip_goal_probe = goal_state is None

        agent_tools = [
            tactic_tools.file_find_sorry_lines,
            tactic_tools.file_read_lines,
            tactic_tools.file_replace_sorry,
            tactic_tools.file_replace_lines,
            tactic_tools.compile,
            tactic_tools.generate_tactics,
            tactic_tools.submit_tactic,
            tactic_tools.submit_decomposition,
            tactic_tools.get_proof_state,
            tactic_tools.get_available_hypotheses,
        ]
        if not skip_goal_probe:
            agent_tools.append(tactic_tools.compile_probe_goal)

        client = create_client(self.provider, model_key="reasoning")

        agent = Agent(
            client=client,
            instructions=AUTONOMOUS_PROVER_INSTRUCTIONS,
            tools=agent_tools,
            name="AutonomousProver",
        )

        # Build rich initial context — from Lean-9 notebook pattern
        context_msg = self._build_autonomous_context(
            demo, sorry_line, filepath, goal_state, sorry_ctx_data,
            hypotheses, local_lemmas, original_sorry_count, strategic_hints,
        )

        # Main loop — single event loop for the entire session
        session_start = time.time()
        original_file_content = Path(filepath).read_text(encoding="utf-8")
        compile_data = {}
        context_history = [context_msg]  # ACCUMULATE instead of replace
        proof_tactics_found = []  # Lean-9 _proof_tactics_found tracking
        self.trace.start_session_span(demo["name"], self.config_label)

        async def _run_session():
            nonlocal compile_data, context_history, proof_tactics_found
            loop = asyncio.get_event_loop()

            for iteration in range(1, max_iterations + 1):
                state.iteration = iteration
                iter_start = time.time()
                print(f"\n--- Iteration {iteration}/{max_iterations} ---", flush=True)

                # Build rich context from state + history — Lean-9 get_context_summary
                state_header = (
                    f"[ETAT SESSION] Phase: {state.phase.value} | "
                    f"Iteration: {iteration}/{max_iterations} | "
                    f"Echecs consecutifs: {state.consecutive_failures}\n"
                    f"Hypotheses: {', '.join(state.available_hypotheses[-10:]) or 'aucune'}\n"
                    f"Lemmes locaux: {', '.join(state.local_lemmas[-15:]) or 'aucun'}\n"
                    f"Best sorry: {state.best_sorry_count}"
                )

                # Feed the FULL accumulated context
                full_context = state_header + "\n\n" + "\n---\n".join(context_history[-3:])

                # Retry with exponential backoff for rate limits (429)
                max_retries = 3
                response = None
                response_text = ""
                for retry in range(max_retries + 1):
                    try:
                        response = await agent.run(full_context)
                        break  # Success — exit retry loop
                    except asyncio.TimeoutError:
                        print(f"  Agent timeout ({agent_timeout_s}s)", flush=True)
                        response_text = f"TIMEOUT after {agent_timeout_s}s"
                        break
                    except Exception as e:
                        err_str = str(e)
                        is_rate_limit = "429" in err_str or "Rate limit" in err_str
                        if is_rate_limit and retry < max_retries:
                            wait_s = 30 * (2 ** retry)  # 30s, 60s, 120s
                            print(f"  [RATE LIMIT] 429 — waiting {wait_s}s "
                                  f"(retry {retry+1}/{max_retries})...", flush=True)
                            await asyncio.sleep(wait_s)
                            continue
                        print(f"  Agent error: {e}", flush=True)
                        response_text = err_str
                        break

                if response is not None:
                    has_msgs = hasattr(response, 'messages')
                    n_msgs = len(response.messages) if has_msgs and response.messages else 0
                    response_text = ""
                    if has_msgs and n_msgs > 0:
                        last = response.messages[-1]
                        response_text = last.text if hasattr(last, 'text') else str(last)
                    self.trace.log_agent_response(
                        agent="AutonomousProver", response=response,
                        duration_s=time.time() - iter_start,
                        iteration=iteration,
                    )

                # Update state from LLM response — Lean-9 _update_state_from_response
                self._update_state_from_response(state, response_text, proof_tactics_found)

                # Auto-compile after each iteration
                current_sorry = Path(filepath).read_text(encoding="utf-8").count("sorry")
                compile_str = tactic_tools.compile()
                try:
                    compile_data = json.loads(compile_str)
                except json.JSONDecodeError:
                    compile_data = {}
                current_sorry = compile_data.get("sorry_count", current_sorry)

                # Auto-restore: if sorry regressed from best, restore best content
                if (tactic_tools.best_content
                        and current_sorry > tactic_tools.best_sorry_count
                        and tactic_tools.best_sorry_count <= original_sorry_count):
                    print(f"  AUTO-RESTORE: {current_sorry} sorry > best {tactic_tools.best_sorry_count}. "
                          f"Restoring.", flush=True)
                    Path(filepath).write_text(tactic_tools.best_content, encoding="utf-8")
                    current_sorry = tactic_tools.best_sorry_count

                # Update state — from Lean-9 _update_state_from_response pattern
                if current_sorry < state.best_sorry_count:
                    state.best_sorry_count = current_sorry
                    state.consecutive_failures = 0
                elif current_sorry > state.best_sorry_count:
                    state.consecutive_failures += 1
                else:
                    state.consecutive_failures += 1

                state.last_compile_errors = compile_data.get("errors", [])

                # Re-extract hypotheses if file changed
                if current_sorry != original_sorry_count:
                    new_hyps = extract_hypotheses(filepath, sorry_line)
                    if new_hyps:
                        state.available_hypotheses = new_hyps

                # Re-extract sorry goals for all remaining sorry lines
                sorry_line_set_new = {i + 1 for i, l in enumerate(
                    Path(filepath).read_text(encoding="utf-8").split("\n")) if "sorry" in l}
                state.local_lemmas = extract_local_lemmas(filepath, sorry_line_set_new)

                # Cumulative file size guard — detect multi-edit rewrites that bypass per-edit guard
                current_content = Path(filepath).read_text(encoding="utf-8")
                original_len = len(original_file_content)
                current_len = len(current_content)
                if original_len > 0:
                    cumulative_ratio = abs(current_len - original_len) / original_len
                    if cumulative_ratio > 0.5:
                        print(f"  CUMULATIVE SIZE GUARD: file changed {cumulative_ratio:.0%} "
                              f"({current_len} vs {original_len} chars). RESTORING original.", flush=True)
                        Path(filepath).write_text(original_file_content, encoding="utf-8")
                        current_sorry = original_sorry_count
                        state.best_sorry_count = min(state.best_sorry_count, original_sorry_count)

                # Phase transitions — from Lean-9 ProofPhase routing
                if compile_data.get("success") and current_sorry == 0:
                    state.phase = ProofPhase.COMPLETE
                elif compile_data.get("success") and current_sorry < original_sorry_count:
                    state.phase = ProofPhase.TACTIC_GEN  # Keep attacking
                elif not compile_data.get("success"):
                    if state.consecutive_failures >= 3:
                        state.phase = ProofPhase.REFINEMENT
                    else:
                        next_phase = PHASE_TRANSITIONS.get(state.phase, ProofPhase.TACTIC_GEN)
                        state.phase = next_phase

                # B.9: HITL — ask for human hint when stuck
                if self.hitl_enabled and state.consecutive_failures >= self.hitl_threshold:
                    print(f"\n  [HITL] {state.consecutive_failures} echecs consecutifs. "
                          f"Demande d'aide humaine...", flush=True)
                    self.trace.log(
                        agent="AutonomousProver", role="hitl",
                        content=f"consecutive_failures={state.consecutive_failures}, asking human",
                    )
                    try:
                        hint = input(
                            f"  [HITL] Indice ou direction ? "
                            f"(Entrée=continuer, 'stop'=arrêter) : "
                        ).strip()
                    except (EOFError, KeyboardInterrupt):
                        hint = ""

                    if hint.lower() == "stop":
                        print("  [HITL] Arrêt demandé par l'utilisateur.", flush=True)
                        break
                    if hint:
                        context_history.append(
                            f"INDICE HUMAIN (priorité maximale):\n{hint}"
                        )
                        state.consecutive_failures = 0
                        print(f"  [HITL] Indice injecté. Reset consecutive_failures.", flush=True)

                self.trace.log(
                    agent="AutonomousProver", role="iteration",
                    content=f"iter={iteration}, sorry={current_sorry}, phase={state.phase.value}",
                    duration_s=time.time() - iter_start,
                )

                print(f"  Sorry: {current_sorry}/{original_sorry_count} "
                      f"Phase: {state.phase.value} "
                      f"({time.time() - iter_start:.1f}s)", flush=True)

                # Check termination
                if current_sorry == 0 and compile_data.get("success"):
                    print(f"  ALL SORRY ELIMINATED!", flush=True)
                    state.set_proof_complete("full_file_proof")
                    break

                if current_sorry < original_sorry_count:
                    print(f"  PROGRESS: sorry {original_sorry_count} -> {current_sorry}")

                # Build ACCUMULATED feedback — never lose history
                feedback_parts = []

                if compile_data.get("success"):
                    feedback_parts.append("COMPILATION: SUCCES")
                else:
                    errors = compile_data.get("errors", [])
                    if errors:
                        err_summary = "\n".join(
                            f"  L{e['line']}: {e['message'][:150]}" for e in errors[:8]
                        )
                        feedback_parts.append(f"COMPILATION: {len(errors)} ERREURS:\n{err_summary}")

                feedback_parts.append(f"Sorry count: {current_sorry}/{original_sorry_count}")
                feedback_parts.append(f"Phase: {state.phase.value}")

                # Append tactic history context — full history with backtracking
                if state.tactic_history:
                    failed = [a for a in state.tactic_history if not a.success]
                    succeeded = [a for a in state.tactic_history if a.success]

                    # Failed tactics: what to AVOID (full list)
                    if failed:
                        fail_log = "\n".join(
                            f"  FAIL: {a.tactic[:100]}"
                            + (f" → {a.error[:80]}" if a.error else "")
                            for a in failed[-10:]
                        )
                        feedback_parts.append(
                            f"TENTATIVES ECHOUEES (ne PAS reessayer ces tactiques):\n{fail_log}"
                        )

                    # Succeeded tactics: what WORKED
                    if succeeded:
                        ok_log = "\n".join(
                            f"  OK: {a.tactic[:100]}" for a in succeeded[-5:]
                        )
                        feedback_parts.append(f"Tactiques reussies:\n{ok_log}")

                    # Summary
                    feedback_parts.append(
                        f"Bilan: {len(succeeded)} reussites, {len(failed)} echecs "
                        f"sur {len(state.tactic_history)} tentatives"
                    )

                # Append to history (don't replace)
                context_history.append("\n".join(feedback_parts))

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
        self.trace.end_session_span(success, f"{original_sorry_count}->{final_sorry}")

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

    def _build_autonomous_context(self, demo: dict, sorry_line: int,
                                  filepath: str, goal_state: Optional[str],
                                  ctx_data: dict, hypotheses: list,
                                  local_lemmas: list, sorry_count: int,
                                  strategic_hints: str) -> str:
        """Build rich initial context for the autonomous prover agent.

        Includes goal state, proof block, hypotheses, local lemmas, and
        goal hints from comments — from Lean-9 notebook rich context pattern.
        """
        parts = [f"Prouve le sorry a la ligne {sorry_line} du fichier {Path(filepath).name}."]

        if demo.get("description"):
            parts.append(f"\nDESCRIPTION:\n{demo['description']}")

        # Goal state — extracted or heuristic
        if goal_state:
            parts.append(f"\nBUT LEAN (ligne {sorry_line}):\n```\n{goal_state}\n```")
        else:
            # No goal extracted — use proof block + comments as context
            goal_hints = ctx_data.get("goal_hints", "")
            proof_block = ctx_data.get("proof_block", "")
            if goal_hints:
                parts.append(f"\nINDICES DE BUT (commentaires au-dessus du sorry):\n{goal_hints}")
            if proof_block:
                # Show the enclosing proof block so agent can reason about the goal
                block_lines = proof_block.split("\n")
                if len(block_lines) > 40:
                    block_lines = block_lines[:20] + ["  ... (tronqué) ..."] + block_lines[-20:]
                parts.append(f"\nBLOC DE PREUVE (contexte du sorry):\n```\n" + "\n".join(block_lines) + "\n```")
                parts.append("NOTE: Le but Lean exact n'a pas pu etre extrait (sorry profondement imbrique). "
                             "Utilise le bloc de preuve et les commentaires pour deduire le but.")

        # Context before/after
        if ctx_data.get("context_before"):
            parts.append(f"\nCONTEXTE AVANT:\n```\n{ctx_data['context_before'][-500:]}\n```")
        if ctx_data.get("context_after"):
            parts.append(f"\nCONTEXTE APRES:\n```\n{ctx_data['context_after'][:300]}\n```")

        # Available hypotheses
        if hypotheses:
            parts.append(f"\nHYPOTHESES DISPONIBLES: {', '.join(hypotheses[-15:])}")

        # Local lemmas (proven in same file, no sorry)
        if local_lemmas:
            parts.append(f"\nLEMMES LOCAUX PROUVES: {', '.join(local_lemmas[:20])}")

        # Definition lookup — extract definitions of types/functions in the goal
        try:
            file_text = Path(filepath).read_text(encoding="utf-8")
            goal_text = goal_state or ""
            # Find identifiers in goal that look like custom definitions
            for name in re.findall(r'\b([a-z_]\w*)\b', goal_text):
                if name in ("by", "exact", "sorry", "have", "obtain", "intro",
                            "fun", "lambda", "forall", "exists", "and", "or",
                            "not", "true", "false", "unit", "prop", "type"):
                    continue
                # Check if it's defined in the file
                def_match = re.search(
                    rf'^(def {re.escape(name)}\b.+?(?=^def |^theorem |^lemma |^end |\Z))',
                    file_text, re.MULTILINE | re.DOTALL,
                )
                if def_match:
                    defn = def_match.group(1).strip()
                    if len(defn) > 500:
                        defn = defn[:500] + "\n  ..."
                    parts.append(f"\nDEFINITION de {name}:\n```\n{defn}\n```")
        except Exception:
            pass

        # Def type warnings — guide prover to avoid unfold/anonymous constructor issues
        try:
            def_warnings = build_def_type_warnings(filepath, goal_state or "")
            if def_warnings:
                parts.append(f"\n{def_warnings}")
        except Exception:
            pass

        if strategic_hints:
            parts.append(f"\nCONSEILS STRATEGIQUES:\n{strategic_hints}")

        # B.4: Top-down decomposition hints for complex goals
        try:
            from .lean_utils import suggest_decomposition
            decomps = suggest_decomposition(goal_state or "")
            if decomps:
                decomp_hints = "\n".join(
                    f"  - {d['name']}: {d['hint']}" for d in decomps
                )
                parts.append(
                    f"\nDECOMPOSITION RECOMMANDÉE (objectif complexe détecté):\n"
                    f"{decomp_hints}\n"
                    f"Utilise submit_decomposition() ou have-Steps pour décomposer AVANT d'essayer une preuve directe."
                )
        except Exception:
            pass

        parts.append(f"\nSORRY COUNT INITIAL: {sorry_count}")
        parts.append("OBJECTIF: reduire le sorry count ou prouver completement.")
        parts.append("Commence par find_sorry_lines() puis propose une tactique.")

        return "\n".join(parts)

    @staticmethod
    def _update_state_from_response(state: ProofState, response: str,
                                    proof_tactics_found: list):
        """Parse LLM response to auto-update shared state.

        From Lean-9 notebook _update_state_from_response pattern:
        - Detect discovered lemmas
        - Track proof tactics found
        - Detect proof completion signals
        """
        if not response:
            return

        response_lower = response.lower()

        # Track proof tactics mentioned — Lean-9 proof_patterns
        proof_patterns = [
            (r'\bsimp\b', 'simp'),
            (r'\brfl\b', 'rfl'),
            (r'\bomega\b', 'omega'),
            (r'\bring\b', 'ring'),
            (r'\blinarith\b', 'linarith'),
            (r'\bexact\b', 'exact'),
            (r'\brw\b', 'rw'),
            (r'\binduction\b', 'induction'),
            (r'\bcases\b', 'cases'),
            (r'\bconstructor\b', 'constructor'),
            (r'\bnorm_cast\b', 'norm_cast'),
            (r'\bpush_cast\b', 'push_cast'),
            (r'\bdecide\b', 'decide'),
        ]

        for pattern, tactic_name in proof_patterns:
            if re.search(pattern, response, re.IGNORECASE):
                if tactic_name not in proof_tactics_found:
                    proof_tactics_found.append(tactic_name)
                    state.tactic_history.append(TacticAttempt(
                        tactic=f"[mentioned] {tactic_name}",
                        success=False,
                        explanation=response[:100],
                    ))

        # Detect proof completion signals — Lean-9 proof_complete_signals
        proof_complete_signals = [
            "proof complete", "proof is complete", "proof found",
            "qed", "verified", "goals accomplished",
            "la preuve est terminee", "la preuve est cloturee",
            "preuve reussie", "all sorry eliminated",
        ]
        if any(signal in response_lower for signal in proof_complete_signals):
            if proof_tactics_found and not state.final_proof:
                state.final_proof = proof_tactics_found[0]

        # Detect Lean-style proof block in response
        code_block_match = re.search(r'```lean\n(.*?)```', response, re.DOTALL)
        if code_block_match:
            code_content = code_block_match.group(1)
            if ":= by" in code_content or ":= rfl" in code_content:
                for pattern, tactic_name in proof_patterns:
                    if re.search(pattern, code_content, re.IGNORECASE):
                        if not state.final_proof:
                            state.final_proof = code_content.strip()[:200]
                        break
