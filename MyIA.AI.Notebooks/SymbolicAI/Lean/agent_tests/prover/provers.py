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

from agent_framework import ToolResultCompactionStrategy

from .trace import TraceLogger
from .state import ProofState, SorryContext, ProofPhase, PHASE_TRANSITIONS, TacticAttempt
from .lean_utils import (
    extract_sorry_block, get_goal_state, verify_sorry_replacement,
    extract_hypotheses, extract_local_lemmas, build_def_type_warnings,
    is_honest_sorry,
)
from .tools import SearchTools, TacticTools, CriticTools, CoordinatorTools, DiagnosisTools
from .agents import (
    create_search_agent,
    create_tactic_agent,
    create_critic_agent,
    create_coordinator_agent,
    create_director_agent,
    create_diagnosis_agent,
)
from .workflow import ProofWorkflowBuilder, ProofMessage
from .instructions import AUTONOMOUS_PROVER_INSTRUCTIONS, augment_instructions
from .config import create_client, HONEST_SORRIES
from . import attempt_history
from .knowledge import ProofKnowledgeBase
from .otel_setup import enable_prover_otel

_PROVER_DIR = Path(__file__).resolve().parent

# P5 (Epic #1453 forensic, 2026-05-29): version-controlled KB of documented
# INTRACTABLE targets. Loaded once, lazily, from baselines/intractable_targets.json.
_INTRACTABLE_KB_PATH = _PROVER_DIR / "baselines" / "intractable_targets.json"
_intractable_kb_cache: Optional[list] = None


def _load_intractable_kb() -> list:
    """Load the documented-intractable targets KB (cached, best-effort).

    Returns the list under the ``targets`` key, or [] if the file is missing
    or malformed. A missing/broken KB must never crash the prover — it simply
    means no pre-screen entries (degrade to the prior behaviour).
    """
    global _intractable_kb_cache
    if _intractable_kb_cache is not None:
        return _intractable_kb_cache
    try:
        data = json.loads(_INTRACTABLE_KB_PATH.read_text(encoding="utf-8"))
        targets = data.get("targets", [])
        _intractable_kb_cache = targets if isinstance(targets, list) else []
    except (OSError, json.JSONDecodeError, ValueError):
        _intractable_kb_cache = []
    return _intractable_kb_cache


def _match_intractable_kb(filepath: str, sorry_line: int) -> Optional[dict]:
    """Return the matching KB entry for (filepath, sorry_line), else None.

    Matching is filename-based (NOT absolute-path-based) so the KB is portable
    across machines — config.py resolves machine-specific absolute paths. An
    entry matches when its ``file`` basename equals the target basename AND
    either (a) ``match_by_file_only`` is true (any sorry in that file), or
    (b) its ``line`` equals ``sorry_line``.
    """
    try:
        target_name = Path(filepath).name
    except (TypeError, ValueError):
        return None
    for entry in _load_intractable_kb():
        if not isinstance(entry, dict):
            continue
        if entry.get("file") != target_name:
            continue
        if entry.get("match_by_file_only"):
            return entry
        if entry.get("line") == sorry_line:
            return entry
    return None


def _refuse_intractable(filepath: str, sorry_line: int,
                        demo_name: str) -> Optional[dict]:
    """Return an early-skip result dict if the target is documented INTRACTABLE.

    P5 (Epic #1453). Mirrors the shape of ``_refuse_honest_sorry``: checks the
    version-controlled KB (baselines/intractable_targets.json) and, on a match,
    returns a result dict the caller returns immediately — BEFORE any agent is
    spawned. Otherwise returns None.

    Distinct from ``_refuse_honest_sorry`` (genuinely-unprovable sorrys): these
    targets are provable in principle but blocked behind ~200-300 lines of new
    formalization the prover cannot invent. Looping agents on them only burns
    the iteration budget (forensic: 9/13 director-less runs, ~8.2h wasted).
    """
    entry = _match_intractable_kb(filepath, sorry_line)
    if entry is None:
        return None
    reason = entry.get("reason", "documented intractable")
    source = entry.get("source", "")
    msg = (
        f"SKIPPED: sorry at {Path(filepath).name}:{sorry_line} is DOCUMENTED "
        f"INTRACTABLE (KB baselines/intractable_targets.json). "
        f"Identifier: {entry.get('identifier', '?')}. Reason: {reason}. "
        f"Source: {source}. Looping agents here only burns the budget — "
        f"the missing piece is new formalization, not search depth. "
        f"Remove the KB entry to re-enable once the formalization exists."
    )
    print(f"\n{'!'*70}\n{msg}\n{'!'*70}\n")
    return {
        "success": False,
        "skipped": True,
        "reason": "documented_intractable",
        "detail": reason,
        "identifier": entry.get("identifier"),
        "source": source,
        "demo": demo_name,
        "sorry_line": sorry_line,
        "filepath": filepath,
    }


def _refuse_honest_sorry(filepath: str, sorry_line: int,
                         demo_name: str) -> Optional[dict]:
    """Return an early-fail result dict if the target sorry is HONEST.

    Checks both the static HONEST_SORRIES registry and the dynamic
    `is_honest_sorry()` comment scan. If matched, returns a result dict
    that the caller should return immediately. Otherwise returns None.
    """
    static = HONEST_SORRIES.get(filepath, {})
    if sorry_line in static:
        reason = static[sorry_line]
        msg = (
            f"REFUSED: sorry at {filepath}:{sorry_line} is registered as HONEST "
            f"(intentionally unprovable). Reason: {reason}"
        )
        print(f"\n{'!'*70}\n{msg}\n{'!'*70}\n")
        return {
            "success": False,
            "skipped": True,
            "reason": "honest_sorry_static",
            "detail": reason,
            "demo": demo_name,
            "sorry_line": sorry_line,
            "filepath": filepath,
        }

    is_honest, comment_block = is_honest_sorry(filepath, sorry_line)
    if is_honest:
        msg = (
            f"REFUSED: sorry at {filepath}:{sorry_line} is documented as HONEST. "
            f"Comment block immediately above:\n{comment_block}\n"
            "If this is wrong, edit the comment to remove the impossibility "
            "marker (FIXME / cannot be proved / counter-example / etc.)."
        )
        print(f"\n{'!'*70}\n{msg}\n{'!'*70}\n")
        return {
            "success": False,
            "skipped": True,
            "reason": "honest_sorry_dynamic",
            "detail": comment_block,
            "demo": demo_name,
            "sorry_line": sorry_line,
            "filepath": filepath,
        }
    return None


def _autonomous_success_gate(final_sorry: int, original_sorry_count: int,
                             final_build_ok: bool) -> tuple[bool, bool]:
    """Decide AutonomousProver session success from the post-verify counts (P4).

    Pure decision behind the increase-case gate (#1483). A file that BUILDS
    (``final_build_ok``) is a success when the sorry count DECREASED, or when it
    stayed/INCREASED through strategic decomposition (structural progress) while
    still > 0. A build failure is never a success. The increase-case is the
    point P4 targets: a decomposition that raises the sorry count but still
    compiles 0 errors must report success and must NOT be reverted — the revert
    branch upstream is keyed on ``final_build_ok`` (``level_1_build``) alone, so
    a sorry increase never reaches it as long as the build passes.

    Returns ``(success, structural_progress)``.
    """
    structural_progress = (
        final_sorry >= original_sorry_count
        and final_build_ok
        and final_sorry > 0
    )
    success = (
        (final_sorry < original_sorry_count or structural_progress)
        and final_build_ok
    )
    return success, structural_progress


def _multi_success_verdict(
    proof_found: bool,
    final_sorry: int,
    original_sorry_count: int,
    structural_progress: bool,
    final_build_ok: bool,
    attempts: int,
    final_proof: Optional[str],
) -> bool:
    """Decide MultiAgentSorryProver session success with the statement-mutation
    guard (FX-6, Epic #1453).

    Pure decision extracted from ``run()`` so the guard is unit-testable. The
    sorry-count disjuncts (``final_sorry == 0`` / ``< original`` /
    ``structural_progress``) stay as in #1453, BUT a sorry-count change alone is
    never a proof: it must come with >=1 verified tactic. The Reidemeister L545
    run (trace ``multi_custom_Reidemeister_L545_openrouter_result.json``) filled
    an in-statement ``sorry`` placeholder with the goal RHS, making the theorem
    reflexive; the build passed and sorry 2->0, yet ``attempts == 0`` and
    ``final_proof is None`` because the in-place latch (workflow.py) sets
    ``proof_found`` without any tactic ever being verified. The guard therefore
    keys on ``attempts`` / ``final_proof`` — NOT on ``proof_found``, which the
    latch taints — so a pure statement mutation cannot report success,
    independently of the sorry delta. (#4075 persists on "build OK + sorry count
    dropped"; this completes it by requiring the drop to be backed by a real
    tactic.)

    Returns ``success``.
    """
    # No verified tactic => any sorry-count change is a statement mutation, not
    # a proof. Block regardless of the delta (Reidemeister had sorry 2->0).
    no_verified_tactic = attempts == 0 or final_proof is None
    if no_verified_tactic:
        return False
    return (
        (proof_found
         or final_sorry == 0
         or final_sorry < original_sorry_count
         or structural_progress)
        and final_build_ok
    )


class MultiAgentSorryProver:
    """Multi-agent sorry replacement using WorkflowBuilder graph.

    4 specialized agents with shared state and conditional routing:
    SearchAgent -> TacticAgent -> VerifyExecutor -> CriticAgent
    with CriticAgent routing back to any agent based on error analysis.
    """

    def __init__(self, trace: TraceLogger, provider: str = "openrouter",
                 local_provider: str = "local",
                 director_provider: Optional[str] = None,
                 coordinator_provider: Optional[str] = None,
                 tactic_provider: Optional[str] = None):
        self.trace = trace
        self.provider = provider
        self.local_provider = local_provider
        self.director_provider = director_provider
        # #1289: CoordinatorAgent needs a fast, capable model for tool-use
        # orchestration. GLM-5.1 (zai) times out on complex Lean contexts.
        # Default to "openrouter" (GPT-5.5 via OPENAI_CHAT_MODEL_ID) which
        # handles Coordinator tasks in <2min vs 12+ min with GLM-5.1.
        self.coordinator_provider = coordinator_provider or "openrouter"
        # #1289 (TacticAgent): Same root cause — GLM-5.1 (zai) times out at
        # 1680s on complex Lean tactic generation (Lattice contexts).
        # BG DEMO 30 forensic showed Coordinator (60s) + Director (8s) fine,
        # but TacticAgent z.ai hung for 1680s. Default to "openrouter" so
        # GPT-5.5 handles tactic generation in ~60-120s instead.
        self.tactic_provider = tactic_provider or "openrouter"

    async def prove_sorry(self, demo: dict, max_iterations: int = 10,
                          workflow_timeout_s: Optional[int] = None,
                          use_diagnosis_agent: bool = False,
                          concurrent_search_count: int = 0) -> dict:
        # Enable MS Agent Framework OTel + JSONL exporter so every agent run,
        # tool call, and LLM completion lands in baselines/traces/<name>.spans.jsonl
        # alongside the higher-level TraceLogger entries.
        otel_session = f"multi_{demo['name']}_{self.provider}_{int(time.time())}"
        otel_path = enable_prover_otel(otel_session)
        print(f"  [OTEL] spans -> {otel_path}")

        filepath = demo["file"]
        sorry_line = demo["line"]

        # Read original content
        original_content = Path(filepath).read_text(encoding="utf-8")
        original_sorry_count = original_content.count("sorry")

        # Auto-detect actual sorry line — exclude lines where "sorry" appears
        # only inside comments. A line is "sorry inside comment" when:
        #   - it starts with `--` (line comment), OR
        #   - the `--` token appears BEFORE the first occurrence of `sorry`.
        # Real sorry tactics are bare tokens, possibly followed by a trailing
        # `-- comment`.
        def _is_real_sorry(line: str) -> bool:
            idx = line.find("sorry")
            if idx < 0:
                return False
            comment_idx = line.find("--")
            return comment_idx < 0 or comment_idx > idx

        actual_sorry_lines = [
            i + 1 for i, line in enumerate(original_content.split("\n"))
            if _is_real_sorry(line)
        ]
        if actual_sorry_lines and sorry_line not in actual_sorry_lines:
            sorry_line = min(actual_sorry_lines, key=lambda l: abs(l - sorry_line))
            print(f"  [AutoFix] Configured line {demo['line']} has no sorry. "
                  f"Using closest sorry at line {sorry_line}")

        # F6 (2026-05-15): already-solved fast-path. If the file has no real
        # sorry token at all, the target is already proven — yield immediately
        # instead of looping agents and running a ~300s compile. Mirrors the
        # F5 intractable fast-path. Forensic finding from the DEMO 9 run
        # (Voting.lean L355, sorry already 0): the prover burned a full agent
        # loop + compile on a no-op target.
        if not actual_sorry_lines:
            print(f"\n{'='*70}")
            print(f"ALREADY SOLVED: {demo['name']} — no real sorry in {filepath}")
            print(f"{'='*70}")
            self.trace.log(
                agent="ProverSetup", role="already_solved",
                content=f"{filepath} has 0 real sorry tokens — target already "
                        f"proven, yielding without agent loop or compile",
            )
            return {
                "success": True,
                "proof": None,
                "iterations": 0,
                "attempts": 0,
                "total_s": 0.0,
                "config": f"multi-{self.provider}",
                "sorry_evolution": f"{original_sorry_count} -> {original_sorry_count}",
                "best_sorry": original_sorry_count,
                "already_solved": True,
            }

        # Refuse honest/unprovable sorrys BEFORE spinning up agents.
        refusal = _refuse_honest_sorry(filepath, sorry_line, demo["name"])
        if refusal is not None:
            return refusal

        # P5 (#1453): pre-screen documented-INTRACTABLE targets BEFORE spinning
        # up agents. A KB match skips immediately instead of looping to the cap.
        intractable = _refuse_intractable(filepath, sorry_line, demo["name"])
        if intractable is not None:
            return intractable

        print(f"\n{'='*70}")
        print(f"MULTI-AGENT PROVER: {demo['name']}")
        print(f"File: {filepath}:{sorry_line}")
        print(f"Original sorry count: {original_sorry_count}")
        print(f"{'='*70}")

        # Extract sorry context
        ctx_data = extract_sorry_block(filepath, sorry_line)
        # Allow DEMO config to override goal (bypass unreliable GoalExtract)
        if demo.get("goal"):
            goal_state = demo["goal"]
            print(f"  Goal OVERRIDE from config: {goal_state[:100]}")
        else:
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

        # Feature 1: Auto-load sibling .lean files at session start.
        # Agents reference files by short name (e.g. "Lemmas.lean"), never by path.
        target_path = Path(filepath).resolve()
        state.target_filepath = str(target_path)
        state.target_filename = target_path.name
        state.remaining_iterations = max_iterations
        parent_dir = target_path.parent
        for sibling in sorted(parent_dir.glob("*.lean")):
            short_name = sibling.name
            try:
                content = sibling.read_text(encoding="utf-8")
                state.loaded_files[short_name] = content
            except OSError:
                pass
        loaded_names = list(state.loaded_files.keys())
        if loaded_names:
            print(f"  [Feature1] Loaded {len(loaded_names)} sibling files: {', '.join(loaded_names)}")

        # Shared KB instance so SearchAgent reads what VerifyExecutor wrote
        # in the same session (otherwise each side instantiates its own and
        # only sees prior-session entries via the JSON file).
        kb = ProofKnowledgeBase()

        # Create per-agent tools
        search_tools = SearchTools(state, filepath, self.trace, kb=kb)
        tactic_tools = TacticTools(state, filepath, sorry_ctx,
                                   demo.get("imports", ""), self.trace)
        tactic_tools._original_sorry_count = original_sorry_count
        critic_tools = CriticTools(state, self.trace)
        coordinator_tools = CoordinatorTools(state, filepath, self.trace)

        # Create 4 specialized agents (with KB context from goal)
        search_agent = create_search_agent(
            search_tools, provider=self.local_provider, goal=goal_state or "")
        tactic_agent = create_tactic_agent(
            tactic_tools, provider=self.tactic_provider, goal=goal_state or "")
        critic_agent = create_critic_agent(critic_tools, provider=self.provider)
        coordinator_agent = create_coordinator_agent(coordinator_tools, provider=self.coordinator_provider)

        # B.7: Create additional SearchAgents for concurrent lemma discovery.
        # Each gets its own SearchTools (independent Mathlib search) but shares
        # the same ProofState so discoveries are visible to all agents.
        extra_search_agents = []
        if concurrent_search_count > 0:
            for i in range(concurrent_search_count):
                extra_tools = SearchTools(state, filepath, self.trace, kb=kb)
                extra_agent = create_search_agent(
                    extra_tools, provider=self.local_provider,
                    goal=goal_state or "",
                    name=f"SearchAgent_{i+2}")
                extra_search_agents.append(extra_agent)
            print(f"  [B.7] {concurrent_search_count} concurrent SearchAgents created")

        # Create optional DirectorAgent (external LLM for strategic guidance)
        director_agent = None
        if self.director_provider:
            try:
                director_agent = create_director_agent(provider=self.director_provider,
                                                        target_file=filepath)
                state._has_director = True  # F12: signal to workflow force-invocation
                print(f"  [DIRECTOR] enabled provider={self.director_provider}")
            except Exception as e:
                print(f"  [DIRECTOR] FAILED to create: {e}")
                director_agent = None

        # F9 (2026-05-17): if no Director is wired, pre-mark the state as
        # "consulted" so the intractable gate degrades gracefully. Without
        # this, sessions launched without --director-provider would loop
        # forever because mark_sorry_intractable would always be refused.
        # The gate only enforces consultation when a Director actually
        # exists to consult.
        if director_agent is None:
            # P4 (#1453): the blanket auto-bypass below satisfies the F9 gate
            # but leaves the abandon decision to the (z.ai) agents — which, on a
            # documented-intractable target, never call mark_sorry_intractable
            # and loop to the iteration cap (forensic: 9/13 director-less runs,
            # ~8.2h wasted). The top-of-function pre-screen already returns early
            # on an exact KB line match; this is the defense-in-depth fallback
            # for the director-less path (catches file-only KB entries and line
            # drift) — apply the SAME KB skip rather than relying on agent
            # self-abandonment. Non-KB targets keep the graceful degradation.
            kb_skip = _refuse_intractable(filepath, sorry_line, demo["name"])
            if kb_skip is not None:
                return kb_skip
            state.director_consulted = True
            print("  [DIRECTOR] not wired - F9 gate auto-bypassed")

        # Feature 3: optional DiagnosisAgent (LLM-powered qualitative
        # verification replacing mechanical VerifyExecutor).
        diagnosis_agent = None
        if use_diagnosis_agent:
            try:
                diagnosis_tools = DiagnosisTools(state, filepath, self.trace)
                diagnosis_agent = create_diagnosis_agent(
                    diagnosis_tools, provider=self.local_provider)
                print(f"  [DIAGNOSIS] enabled provider={self.local_provider}")
            except Exception as e:
                print(f"  [DIAGNOSIS] FAILED to create: {e}")
                diagnosis_agent = None

        # Build workflow graph (kb shared with SearchTools)
        workflow_builder = ProofWorkflowBuilder(
            search_agent, tactic_agent, critic_agent, coordinator_agent,
            sorry_ctx, demo.get("imports", ""), self.trace, state=state, kb=kb,
            director_agent=director_agent,
            diagnosis_agent=diagnosis_agent,
            concurrent_search_count=concurrent_search_count,
            extra_search_agents=extra_search_agents if extra_search_agents else None,
            tactic_tools=tactic_tools,
        )
        workflow = workflow_builder.build()

        # Build initial context message
        context_msg = self._build_context_message(demo, ctx_data, goal_state,
                                                   original_sorry_count, sorry_line)

        # F4 (2026-05-11): KB warm-start. Surface up to 5 prior successful
        # proofs whose goal signature overlaps the current goal so the
        # CoordinatorAgent can incorporate them into the attack plan instead
        # of re-deriving familiar shapes from scratch.
        if goal_state:
            try:
                similar = kb.search_similar(goal_state, max_results=5)
                if similar:
                    lines = ["\nPREUVES SIMILAIRES (KB warm-start, "
                             f"{len(similar)} resultats):"]
                    for hit in similar:
                        rel = hit.get("relevance", 0.0)
                        tac = (hit.get("tactic") or "")[:160].replace("\n", " ")
                        f = hit.get("file", "")
                        lines.append(f"  - [{rel:.2f}] {f} -> {tac}")
                    context_msg = context_msg + "\n" + "\n".join(lines)
                    self.trace.log(
                        agent="ProverSetup", role="kb_warm_start",
                        content=f"injected {len(similar)} similar entries "
                                f"(kb_size={kb.size})",
                    )
            except Exception as e:
                self.trace.log(
                    agent="ProverSetup", role="kb_warm_start_error",
                    content=f"warm-start lookup failed: {e}",
                )

        initial_msg = ProofMessage(
            content=context_msg,
            sorry_count=original_sorry_count,
            max_iterations=max_iterations,
            next_agent="coordinator",  # B.3: coordinator sets attack plan first
        )

        # Run workflow with a wall-clock timeout — caps the total session at
        # `max_iterations * 90s` (per-agent timeout) by default, but caller
        # can override.
        import asyncio as _asyncio
        if workflow_timeout_s is None:
            # User mandate 2026-06-21: hard single-sorry nuts (e.g. the
            # Bondareva cone-closed lemma) were STARVED by the old 600s/sorry
            # cap. On demo-55 the agents spent ~90s planning + ~240s on the
            # Director consult, so the FIRST Lean compile only landed at ~615s
            # — past the 600s cap. The session timed out with 0 actual
            # iterations and lost its traces. Long sessions are needed,
            # especially on hard nuts. Crons fire at >= 1h, so a 45-min ceiling
            # leaves comfortable margin for one BG run per cron tick.
            PER_UNIT_S = 2700   # ~45 min (was 600) — room for planning + Director + several compile loops
            CEILING_S = 2700    # hard cap, safe under the >=1h cron cadence
            iteration_cap = max_iterations * PER_UNIT_S
            # P2 (#1453 forensic): per-sorry wall-clock cap still scales with
            # problem size; the CEILING keeps any single BG run under the cron.
            sorry_cap = max(original_sorry_count * PER_UNIT_S, PER_UNIT_S)
            workflow_timeout_s = min(iteration_cap, sorry_cap, CEILING_S)
        # Surface the (build-credited) budget to the agents' time tool so they
        # pace to the real ceiling instead of the 1800s default.
        try:
            state.max_session_seconds = float(workflow_timeout_s)
        except Exception:
            pass
        session_start = time.time()
        self.trace.start_session_span(demo["name"], "multi")
        proof_found = False
        try:
            # Build-credited wall-clock supervisor (user mandate 2026-06-21:
            # "mettre en pause le timer de mesure pendant les builds"). A single
            # `asyncio.wait_for` would count `lake build` time against the cap,
            # starving the reasoning the agents need on hard nuts. Instead we
            # poll: the effective deadline EXTENDS by the seconds spent compiling
            # since this session started, so `workflow_timeout_s` measures
            # reasoning time, not compile time. Caching (content-hash + olean
            # incremental `-R`) keeps the credited build time small; the credit
            # covers the irreducible compiles that remain.
            # Resolve the SAME LeanVerifier class the tools build through (the
            # package uses a spec-based loader, not a normal import — see
            # verifier.py), so we read the class-level build accumulator instances
            # actually write to.
            from .verifier import _load_lean_verifier_class
            _LeanVerifier = _load_lean_verifier_class()
            _build_at_start = _LeanVerifier._total_build_seconds
            _POLL_S = 30
            _wf_task = _asyncio.ensure_future(workflow.run(initial_msg))
            result = None
            while True:
                try:
                    result = await _asyncio.wait_for(
                        _asyncio.shield(_wf_task), timeout=_POLL_S,
                    )
                    break  # workflow finished on its own
                except _asyncio.TimeoutError:
                    build_s = _LeanVerifier._total_build_seconds - _build_at_start
                    reasoning_s = (time.time() - session_start) - build_s
                    if reasoning_s > workflow_timeout_s:
                        _wf_task.cancel()
                        try:
                            await _wf_task
                        except (_asyncio.CancelledError, Exception):
                            pass
                        raise _asyncio.TimeoutError
                    # else: still within reasoning budget — keep waiting.

            if hasattr(result, 'output') and result.output:
                final_msg = result.output
            else:
                final_msg = initial_msg

            proof_found = getattr(final_msg, 'proof_found', False)
        except _asyncio.TimeoutError:
            try:
                _bs = _LeanVerifier._total_build_seconds - _build_at_start
                _credit = f"; {_bs:.0f}s build credited"
            except NameError:
                _credit = ""
            print(f"  Workflow reasoning-budget timeout ({workflow_timeout_s}s "
                  f"reasoning{_credit}) — aborting")
            proof_found = False
        except Exception as e:
            print(f"  Workflow error: {e}")
        finally:
            # Pick the best snapshot to commit, in this priority order:
            #   1. tactic_tools.best_content       (lowest sorry count seen)
            #   2. tactic_tools._last_build_ok_content (latest build-passing edit)
            #   3. original_content                (untouched fallback)
            # The middle option lets us KEEP partial structural progress: even
            # if final sorry count >= original (e.g., decomposition broke 1
            # sorry into 3 sub-sorries that all compile), we want to commit
            # that work instead of throwing it away. The agent is then free
            # to resume from that partial state in a future run.
            total_s = time.time() - session_start
            final_sorry = Path(filepath).read_text(encoding="utf-8").count("sorry")
            structural_progress = False
            # Default value so the success check after finally always has it,
            # even if an exception is raised mid-block before the verify runs.
            final_build_ok = False

            best_content = getattr(tactic_tools, "best_content", None)
            best_sorry = getattr(tactic_tools, "best_sorry_count",
                                 original_sorry_count)
            last_ok_content = getattr(tactic_tools, "_last_build_ok_content", None)
            last_ok_sorry = getattr(tactic_tools, "_last_build_ok_sorry_count", None)

            if best_content and best_sorry < final_sorry:
                print(f"  Restoring best ({best_sorry} sorry vs {final_sorry})")
                Path(filepath).write_text(best_content, encoding="utf-8")
                final_sorry = best_sorry

            if (final_sorry >= original_sorry_count and not proof_found):
                if last_ok_content and last_ok_content != original_content:
                    print(
                        f"  Keeping last build-passing snapshot "
                        f"({last_ok_sorry} sorry, decomposition progress preserved)"
                    )
                    Path(filepath).write_text(last_ok_content, encoding="utf-8")
                    final_sorry = last_ok_sorry if last_ok_sorry is not None else final_sorry
                    structural_progress = True

            # MANDATORY final build verification on the committed file. This
            # catches false positives where the snapshot's build_check was
            # bypassed (build_check=False) or stale-cached. Iter 2 of demo 9
            # promoted a `show ?a ≦ ?b -- PROBE` snapshot to best because the
            # agent passed build_check=False; the snapshot guard in tools.py
            # now prevents that, but this verify is the workflow-level safety
            # net the user requested ("les verifs via build devraient faire
            # partie integrante du workflow du prouveur").
            from .verifier import get_verifier
            _gv = get_verifier()
            if _gv is not None:
                type(_gv).invalidate(filepath)
            try:
                final_verify_raw = tactic_tools.compile()
                final_verify = json.loads(final_verify_raw)
            except Exception as _e:
                final_verify = {"overall": False, "level_1_build": False,
                                "errors": [{"message": f"final-verify crashed: {_e}"}]}

            final_build_ok = bool(final_verify.get("level_1_build", False))
            if not final_build_ok:
                _errs = final_verify.get("errors", [])[:5]
                print(
                    f"  FINAL VERIFY FAILED ({len(_errs)} compile errors). "
                    f"Reverting to original to avoid leaving the file broken."
                )
                Path(filepath).write_text(original_content, encoding="utf-8")
                final_sorry = original_sorry_count
                structural_progress = False
                # Force-clear best snapshot so callers don't claim spurious progress
                tactic_tools._best_content = None
                tactic_tools._best_sorry_count = original_sorry_count
            else:
                # Build passed — but a passing build can still hide an IMPLICIT
                # sorry: when the agent replaces an explicit `sorry` with a search
                # tactic (apply?/exact?/solve_by_elim) that finds nothing, Lean
                # emits a "declaration uses sorry" WARNING (not an error), so the
                # build succeeds while the text no longer contains "sorry" (#1500).
                # compile() already folds that warning into
                # final_verify["sorry_count"] (build-aware: max of text + warning
                # counts); the text-only final_sorry read above misses it. Adopt
                # the build-aware count whenever it is higher so the success gate
                # below cannot fire on a vanished-text / implicit sorry.
                _verify_sorry = final_verify.get("sorry_count")
                if isinstance(_verify_sorry, int) and _verify_sorry > final_sorry:
                    print(
                        f"  Build-aware sorry count {_verify_sorry} > text count "
                        f"{final_sorry}: {_verify_sorry - final_sorry} implicit "
                        f"sorry (apply?/exact?/solve_by_elim). Using build-aware "
                        f"count for the success gate (#1500)."
                    )
                    final_sorry = _verify_sorry
                    structural_progress = False

        # Success now also covers structural progress: file changed but
        # compiles, even if sorry count didn't decrease. Provers.py used to
        # treat that as a failure and restore original, which threw away the
        # decomposition the agent had just done.
        # IMPORTANT: success ALSO requires final_build_ok — a sorry-count drop
        # without a real build is the iter 2 false positive we are guarding
        # against. final_build_ok is set above in the mandatory verify.
        # FX-6 (Epic #1453, statement-mutation guard): a sorry-count drop with
        # NO verified tactic is a statement mutation, not a proof (Reidemeister
        # L545 trace). Delegate to the pure verifier so the guard is testable.
        attempts_count = len(state.tactic_history)
        success = _multi_success_verdict(
            proof_found=proof_found,
            final_sorry=final_sorry,
            original_sorry_count=original_sorry_count,
            structural_progress=structural_progress,
            final_build_ok=final_build_ok,
            attempts=attempts_count,
            final_proof=state.final_proof,
        )
        # FX-6 restore: when the build passed and sorry dropped but NO tactic
        # was attempted (attempts == 0, the unambiguous statement-mutation
        # signal), the on-disk file holds the mutation (e.g. an in-statement
        # sorry filled with the goal RHS). Restore the original so the mutation
        # cannot persist as a silent "success". Conservative: only fires on
        # attempts == 0 so a legitimate decomposition snapshot (attempts > 0)
        # is never undone here.
        if (not success and final_build_ok and attempts_count == 0
                and final_sorry < original_sorry_count):
            print(
                f"  STATEMENT-MUTATION GUARD (FX-6): build OK + sorry "
                f"{original_sorry_count}->{final_sorry} with no verified tactic "
                f"(attempts=0, proof={'set' if state.final_proof else 'null'}). "
                f"Restoring original — not a proof."
            )
            try:
                Path(filepath).write_text(original_content, encoding="utf-8")
                final_sorry = original_sorry_count
            except OSError:
                pass
        self.trace.end_session_span(success, f"{original_sorry_count}->{final_sorry}")

        # Persist outcome to cross-session history (best-effort)
        try:
            outcome = "success" if success else "build_fail"
            recent_attempts = [a for a in state.tactic_history[-5:] if a.tactic]
            for att in recent_attempts:
                attempt_history.record_attempt(
                    _PROVER_DIR, filepath, sorry_line,
                    tactic=att.tactic,
                    outcome="success" if att.success else outcome,
                    error_category=getattr(att, "error", None),
                    error_excerpt=(att.error or "")[:200] if att.error else None,
                    session_id=state.session_id,
                )
        except Exception:
            pass

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
            # P6 (#1453 forensic): surface the structural-progress flag so a
            # build-OK / sorry_delta==0 outcome ("proof restructured", e.g. one
            # sorry decomposed into N compiling sub-sorries) is distinguishable
            # from an actual sorry reduction. Without this, both report
            # success=True and consumers cannot tell them apart.
            "structural_progress": structural_progress,
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

        # Proof scaffolding: pre-written proof attempt from DEMO config
        if demo.get("proof_scaffolding"):
            scaffold = demo["proof_scaffolding"]
            parts.append(
                f"\nPREUVE ECHAFAUDAGE A ESSAYER EN PRIORITE:\n"
                f"Le code suivant est une tentative de preuve pre-ecrite. "
                f"Essaie de l'utiliser en premier avec submit_tactic(). "
                f"Si elle ne compile pas, utilise les erreurs pour adapter.\n"
                f"```\n{scaffold}\n```"
            )

        # Cross-session memory: surface previously failed tactics
        try:
            history = attempt_history.load_history(
                _PROVER_DIR, demo["file"], sorry_line)
            history_block = attempt_history.format_for_agent(history)
            if history_block:
                parts.append("\n" + history_block)
        except Exception:
            pass

        return "\n".join(parts)


class AutonomousProver:
    """Single-agent prover with full file editing powers.

    Uses one Agent with all tools (file editing, compile, search).
    The orchestrator loop: agent acts -> auto-compile -> feedback -> repeat.
    """

    def __init__(self, trace: TraceLogger, provider: str = "openrouter",
                 hitl_enabled: bool = True, hitl_threshold: int = 5):
        self.trace = trace
        self.provider = provider
        self.hitl_enabled = hitl_enabled
        self.hitl_threshold = hitl_threshold
        self.config_label = f"auto-{provider}"

    def prove_sorry(self, demo: dict, max_iterations: int = 10,
                    # agent_timeout_s default was 0 (no timeout), letting a
                    # stuck provider hang indefinitely on a bare prove_sorry()
                    # call (observed: TacticAgent z.ai 1680s, GLM single-call
                    # 1200s+). Normal single-agent call is ~60-120s, so a 900s
                    # hard cap kills pathological hangs with generous headroom.
                    # Routes through the ContextVar-safe asyncio.wait branch
                    # below. Pass agent_timeout_s=0 explicitly to disable.
                    strategic_hints: str = "", agent_timeout_s: int = 900) -> dict:
        # Same OTel wiring as MultiAgentSorryProver — single-agent runs benefit
        # just as much from a durable span log of LLM-tool interactions.
        otel_session = f"auto_{demo['name']}_{self.provider}_{int(time.time())}"
        otel_path = enable_prover_otel(otel_session)
        print(f"  [OTEL] spans -> {otel_path}")

        filepath = demo["file"]
        sorry_line = demo["line"]

        import asyncio
        from agent_framework import Agent

        original_content = Path(filepath).read_text(encoding="utf-8")
        original_sorry_count = original_content.count("sorry")

        # Auto-detect actual sorry line — pick NEAREST to configured line
        actual_sorry_lines = [
            i + 1 for i, line in enumerate(original_content.split("\n"))
            if "sorry" in line
        ]
        if actual_sorry_lines and sorry_line not in actual_sorry_lines:
            # Pick the sorry CLOSEST to the configured line, not the first one
            sorry_line = min(actual_sorry_lines, key=lambda l: abs(l - sorry_line))
            print(f"  [AutoFix] Configured line has no sorry. "
                  f"Using closest sorry at line {sorry_line}")

        # F6 (2026-05-15): already-solved fast-path — see MultiAgentSorryProver.
        # No sorry anywhere in the file => target already proven, yield now.
        if not actual_sorry_lines:
            print(f"\n{'='*70}")
            print(f"ALREADY SOLVED: {demo['name']} — no sorry in {filepath}")
            print(f"{'='*70}")
            self.trace.log(
                agent="ProverSetup", role="already_solved",
                content=f"{filepath} has 0 sorry tokens — target already "
                        f"proven, yielding without agent loop or compile",
            )
            return {
                "success": True,
                "proof": None,
                "iterations": 0,
                "attempts": 0,
                "total_s": 0.0,
                "config": self.config_label,
                "sorry_evolution": f"{original_sorry_count} -> {original_sorry_count}",
                "best_sorry": original_sorry_count,
                "already_solved": True,
            }

        # Refuse honest/unprovable sorrys BEFORE spinning up the agent.
        refusal = _refuse_honest_sorry(filepath, sorry_line, demo["name"])
        if refusal is not None:
            return refusal

        # P5 (#1453): pre-screen documented-INTRACTABLE targets BEFORE spinning
        # up the agent. A KB match skips immediately instead of looping to the cap.
        intractable = _refuse_intractable(filepath, sorry_line, demo["name"])
        if intractable is not None:
            return intractable

        print(f"\n{'='*70}")
        print(f"AUTONOMOUS PROVER: {demo['name']}")
        print(f"File: {filepath}:{sorry_line}")
        print(f"Config: {self.config_label}")
        print(f"Original sorry count: {original_sorry_count}")
        print(f"Agent timeout: {'none' if agent_timeout_s == 0 else f'{agent_timeout_s}s'}")
        print(f"{'='*70}")

        # Extract sorry context — includes proof_block and goal_hints
        sorry_ctx_data = extract_sorry_block(filepath, sorry_line)
        # Allow DEMO config to override goal (bypass unreliable GoalExtract)
        if demo.get("goal"):
            goal_state = demo["goal"]
            print(f"  Goal OVERRIDE from config: {goal_state[:100]}")
        else:
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
            instructions=augment_instructions(
                AUTONOMOUS_PROVER_INSTRUCTIONS, goal=goal_state or ""
            ),
            tools=agent_tools,
            name="AutonomousProver",
            compaction_strategy=ToolResultCompactionStrategy(
                keep_last_tool_call_groups=3,
            ),
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
        final_build_ok = False  # Track build success across iterations
        context_history = [context_msg]  # ACCUMULATE instead of replace
        proof_tactics_found = []  # Lean-9 _proof_tactics_found tracking
        self.trace.start_session_span(demo["name"], self.config_label)

        async def _run_session():
            nonlocal compile_data, context_history, proof_tactics_found, final_build_ok
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
                        if agent_timeout_s > 0:
                            # ContextVar-safe timeout: do NOT use `asyncio.wait_for`
                            # because the framework's AgentTelemetryLayer sets a
                            # ContextVar Token inside `agent.run`. `wait_for`
                            # spawns a child task with a child Context, and on
                            # timeout the Token.reset propagates through the
                            # outer Context, raising
                            # `ValueError: <Token> was created in a different
                            # Context` (verified via OTel trace
                            # multi_SMOKE_ZERO_ADD_local_*.spans.jsonl,
                            # 2026-05-11, cf. workflow.py L116 NOTE).
                            #
                            # Fix: spawn the task explicitly and use
                            # `asyncio.wait` (which never auto-cancels) + manual
                            # cancel + `await task` so the Token reset runs
                            # inside the task's own Context.
                            agent_task = asyncio.create_task(
                                agent.run(full_context))
                            done, _pending = await asyncio.wait(
                                {agent_task}, timeout=agent_timeout_s)
                            if agent_task in done:
                                response = agent_task.result()
                            else:
                                agent_task.cancel()
                                try:
                                    await agent_task
                                except (asyncio.CancelledError, Exception):
                                    # Cancellation/teardown errors are
                                    # expected — Token reset happens inside
                                    # the task's own Context.
                                    pass
                                raise asyncio.TimeoutError(
                                    f"agent.run exceeded {agent_timeout_s}s")
                        else:
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

                # Build-success gate: sorry reduction only counts if build passes
                build_ok = compile_data.get("success", False)
                final_build_ok = build_ok

                # Auto-restore: if sorry regressed from best, restore best content
                if (tactic_tools.best_content
                        and current_sorry > tactic_tools.best_sorry_count
                        and tactic_tools.best_sorry_count <= original_sorry_count):
                    print(f"  AUTO-RESTORE: {current_sorry} sorry > best {tactic_tools.best_sorry_count}. "
                          f"Restoring.", flush=True)
                    Path(filepath).write_text(tactic_tools.best_content, encoding="utf-8")
                    current_sorry = tactic_tools.best_sorry_count

                # Auto-restore: if sorry decreased but build FAILS, revert the edit
                if not build_ok and current_sorry < original_sorry_count:
                    print(f"  BUILD-FAIL RESTORE: sorry {original_sorry_count}->{current_sorry} "
                          f"but build failed. Reverting.", flush=True)
                    Path(filepath).write_text(original_file_content, encoding="utf-8")
                    current_sorry = original_sorry_count
                    state.consecutive_failures += 1

                # Update state — only count progress if build passes
                elif build_ok and current_sorry < state.best_sorry_count:
                    # Force-save best_content from file (in case tool-level save
                    # was skipped due to build_check=False or other code path)
                    tactic_tools._best_content = Path(filepath).read_text(encoding="utf-8")
                    tactic_tools._best_sorry_count = current_sorry
                    state.best_sorry_count = current_sorry
                    state.consecutive_failures = 0
                    print(f"  PROGRESS SAVED: sorry {original_sorry_count}->{current_sorry} "
                          f"(best_content captured, {len(tactic_tools._best_content)} chars)",
                          flush=True)
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

                # Delta-0 stagnation guard (P2, #1453 forensic):
                # The multi-agent path has DELTA0_STAGNATION_HARDCAP=6 in
                # workflow.py:223-237, but the autonomous loop had no equivalent.
                # Forensic: custom_Basic_L308 burned 5.9h with 7 identical
                # compiles. A hardcap at 6 stops pathological burners.
                DELTA0_HARDCAP = 6
                if tactic_tools._consecutive_delta0 >= DELTA0_HARDCAP:
                    print(f"  DELTA0 STAGNATION: {tactic_tools._consecutive_delta0} "
                          f"compiles without progress (hardcap={DELTA0_HARDCAP}). "
                          f"Stopping to preserve budget.", flush=True)
                    break

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
                    # Early stop: if sorry decreased and build passes, stop to
                    # preserve progress. The caller can re-invoke for next sorry.
                    if build_ok and current_sorry < original_sorry_count:
                        print(f"  EARLY STOP: progress made (sorry {original_sorry_count}->{current_sorry}). "
                              f"Stopping to preserve.", flush=True)
                        break

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
        except Exception as e:
            print(f"  Autonomous session error: {e}")

        total_s = (datetime.now() - state.start_time).total_seconds()
        final_sorry = Path(filepath).read_text(encoding="utf-8").count("sorry")

        # Restore best state if worse — but validate first (P2, V5).
        # best_content was captured when sorry decreased AND build passed,
        # but intermediate edits or merge artifacts can corrupt it. Without
        # validation, we restore a non-compiling file and the final verify
        # may not catch it (only runs when final_sorry < original).
        # Forensic: Demo16 CYCLE78, best_state restore produced 2→2 but
        # build FAILED — the 2-sorry state was an earlier broken snapshot.
        if tactic_tools.best_content and tactic_tools.best_sorry_count < final_sorry:
            print(f"  Validating best state ({tactic_tools.best_sorry_count} vs {final_sorry})...",
                  flush=True)
            Path(filepath).write_text(tactic_tools.best_content, encoding="utf-8")
            _validate_result = json.loads(tactic_tools.compile())
            if _validate_result.get("success", False):
                final_sorry = tactic_tools.best_sorry_count
                print(f"  Best state validated (build OK, sorry={final_sorry})", flush=True)
            else:
                _v_errs = _validate_result.get("error_count", "?")
                print(f"  Best state FAILED build ({_v_errs} errors). "
                      f"Falling back to original.", flush=True)
                Path(filepath).write_text(original_file_content, encoding="utf-8")
                final_sorry = original_sorry_count

        # P4 fix (2026-05-23): NEVER revert a file solely because sorry_count
        # increased. Strategic decomposition (1 sorry → 2 sub-sorries) is valid
        # when the file compiles. Only revert on BUILD FAILURE (compile errors).
        # Forensic: Director L147 run reverted a compiling file (0 errors, sorry
        # 4→5) losing strategic decomposition progress.

        # Final verification build — catch false positives (0 sorry but unsolved goals)
        # P4: Run on ALL files, not just sorry-reduced ones.
        final_verify_ok = False
        print("  Final verification build...", flush=True)
        verify_result = json.loads(tactic_tools.compile())
        # P4: Gate on build success only (level_1_build), NOT overall "success"
        # which includes sorry_delta check (level_2). A sorry increase from
        # strategic decomposition must NOT trigger revert if the build passes.
        final_verify_ok = verify_result.get("level_1_build", False)
        final_build_ok = final_verify_ok
        # Update final_sorry from compile result (includes implicit sorry detection)
        final_sorry = verify_result.get("sorry_count", final_sorry)
        if not final_verify_ok:
            errors = verify_result.get("errors", [])
            unsolved = [e for e in errors if "unsolved" in e.get("message", "")]
            if unsolved:
                print(f"  FALSE POSITIVE: {len(unsolved)} unsolved goals despite "
                      f"{final_sorry} sorry. Reverting to original.", flush=True)
                Path(filepath).write_text(original_file_content, encoding="utf-8")
                final_sorry = original_sorry_count
            else:
                print(f"  Build failed ({verify_result.get('error_count', '?')} errors), "
                      f"reverting.", flush=True)
                Path(filepath).write_text(original_file_content, encoding="utf-8")
                final_sorry = original_sorry_count
            print("  Final verification build (post-revert)...", flush=True)
            verify_result = json.loads(tactic_tools.compile())
            final_verify_ok = verify_result.get("level_1_build", False)
            final_sorry = verify_result.get("sorry_count", final_sorry)
            if not final_verify_ok:
                errors = verify_result.get("errors", [])
                unsolved = [e for e in errors if "unsolved" in e.get("message", "")]
                if unsolved:
                    print(f"  FALSE POSITIVE: {len(unsolved)} unsolved goals despite "
                          f"{final_sorry} sorry. Reverting to original.", flush=True)
                    # BUGFIX (2026-05-12 ai-01): previous version did
                    # `Path(filepath).write_text(Path(filepath).read_text(...), ...)`
                    # which is a no-op (reads then writes the SAME file content),
                    # so the broken/unsolved-goal file was committed to disk
                    # despite the "Reverting" message. Restore from
                    # `original_file_content` captured at session start.
                    Path(filepath).write_text(original_file_content, encoding="utf-8")
                    final_sorry = original_sorry_count
                else:
                    print(f"  Build failed ({verify_result.get('error_count', '?')} errors), "
                          f"reverting.", flush=True)

        # P4: success also covers structural progress (sorry increase from
        # strategic decomposition) as long as the file builds. Decision is
        # extracted to a pure helper so the increase-case is unit-testable
        # (#1483). final_build_ok == final_verify_ok here (set at line ~1102).
        success, structural_progress_autonomous = _autonomous_success_gate(
            final_sorry, original_sorry_count, final_build_ok
        )
        self.trace.end_session_span(success, f"{original_sorry_count}->{final_sorry}")

        # Persist outcome to cross-session history (best-effort, never raises)
        try:
            outcome = "success" if success else (
                "build_fail" if not final_build_ok else "no_progress"
            )
            recent_attempts = [a for a in state.tactic_history[-5:] if a.tactic]
            for att in recent_attempts:
                attempt_history.record_attempt(
                    _PROVER_DIR, filepath, sorry_line,
                    tactic=att.tactic,
                    outcome="success" if att.success else outcome,
                    error_category=getattr(att, "error", None),
                    error_excerpt=(att.error or "")[:200] if att.error else None,
                    session_id=state.session_id,
                )
        except Exception:
            pass

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
            # P6 (#1453 forensic): same flag as MultiAgentSorryProver — already
            # computed by _autonomous_success_gate, now surfaced so a build-OK /
            # sorry_delta>=0 "proof restructured" outcome is distinguishable
            # from a real sorry reduction in the result JSON.
            "structural_progress": structural_progress_autonomous,
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

        # Proof scaffolding: pre-written proof attempt from DEMO config
        if demo.get("proof_scaffolding"):
            scaffold = demo["proof_scaffolding"]
            parts.append(
                f"\nPREUVE ECHAFAUDAGE A ESSAYER EN PRIORITE:\n"
                f"Le code suivant est une tentative de preuve pre-ecrite. "
                f"Essaie de l'utiliser en premier avec file_replace_sorry(). "
                f"Si elle ne compile pas, utilise les erreurs pour adapter.\n"
                f"```\n{scaffold}\n```"
            )

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

        # Cross-session memory: surface previously failed tactics
        try:
            history = attempt_history.load_history(
                _PROVER_DIR, filepath, sorry_line)
            history_block = attempt_history.format_for_agent(history)
            if history_block:
                parts.append("\n" + history_block)
        except Exception:
            pass

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
