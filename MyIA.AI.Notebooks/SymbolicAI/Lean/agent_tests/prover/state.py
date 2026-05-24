"""Proof state data structures shared between agents."""

import uuid
from datetime import datetime
from typing import Optional, Dict, Any, List
from dataclasses import dataclass, field
from enum import Enum


class ProofStrategy(Enum):
    EXPLORATION = "exploration"
    REFINEMENT = "refinement"
    VALIDATION = "validation"
    RECOVERY = "recovery"


class ProofPhase(Enum):
    INIT = "init"
    SEARCH = "search"
    TACTIC_GEN = "tactic_gen"
    VERIFICATION = "verification"
    REFINEMENT = "refinement"
    COMPLETE = "complete"
    FAILED = "failed"


PHASE_AGENT_MAP = {
    ProofPhase.INIT: "CoordinatorAgent",
    ProofPhase.SEARCH: "SearchAgent",
    ProofPhase.TACTIC_GEN: "TacticAgent",
    ProofPhase.VERIFICATION: "VerifierAgent",
    ProofPhase.REFINEMENT: "CriticAgent",
    ProofPhase.COMPLETE: None,
    ProofPhase.FAILED: None,
}

PHASE_TRANSITIONS = {
    ProofPhase.INIT: ProofPhase.SEARCH,
    ProofPhase.SEARCH: ProofPhase.TACTIC_GEN,
    ProofPhase.TACTIC_GEN: ProofPhase.VERIFICATION,
    ProofPhase.VERIFICATION: ProofPhase.REFINEMENT,
    ProofPhase.REFINEMENT: ProofPhase.TACTIC_GEN,
}


@dataclass
class TacticAttempt:
    tactic: str
    success: bool
    error: Optional[str] = None
    timestamp: datetime = field(default_factory=datetime.now)
    state_before: Optional[str] = None
    confidence: Optional[float] = None
    explanation: Optional[str] = None
    is_decomposition: bool = False  # True for `have h : ... := by ...; <main>` blocks


@dataclass
class ProofState:
    """Shared state for multi-agent proof sessions."""
    session_id: str = field(default_factory=lambda: str(uuid.uuid4())[:8])
    theorem_name: str = ""
    theorem_statement: str = ""
    imports: Optional[str] = None

    current_goal: str = ""
    current_proof: List[str] = field(default_factory=list)
    phase: ProofPhase = ProofPhase.INIT
    strategy: ProofStrategy = ProofStrategy.EXPLORATION

    discovered_lemmas: List[str] = field(default_factory=list)
    tactic_history: List[TacticAttempt] = field(default_factory=list)

    iteration: int = 0
    max_iterations: int = 10
    start_time: datetime = field(default_factory=datetime.now)

    last_error: Optional[str] = None
    final_proof: Optional[str] = None
    error_count: int = 0

    verification_results: List[Dict[str, Any]] = field(default_factory=list)
    total_lean_time_ms: float = 0.0

    _next_agent: Optional[str] = field(default=None, repr=False)
    sorry_context: Optional["SorryContext"] = field(default=None, repr=False)
    strategy_mode: str = "direct"  # "direct" | "decompose" | "search_first"
    decomposition_depth: int = 0

    # Rich state from Lean-9 notebook patterns
    available_hypotheses: List[str] = field(default_factory=list)
    local_lemmas: List[str] = field(default_factory=list)
    sorry_goals: Dict[int, str] = field(default_factory=dict)
    consecutive_failures: int = 0
    last_compile_errors: List[Dict[str, Any]] = field(default_factory=list)
    best_sorry_count: int = 999
    # P2 (#1453): mirrored from TacticTools.compile() — consecutive successful
    # compiles that did not reach a new sorry-count low (Delta0-stagnation).
    # Lets workflow executors force-route a stuck session without re-deriving it.
    consecutive_delta0_compiles: int = 0

    # B.3: Explicit attack plan set by CoordinatorAgent
    plan: List[str] = field(default_factory=list)
    plan_phase: int = 0  # Current step in the plan

    # F5 (2026-05-11): Coordinator can explicitly abandon a goal so the
    # session ends cleanly instead of burning max_iterations on an
    # unprovable sorry. Set via CoordinatorTools.mark_sorry_intractable.
    intractable: bool = False
    intractable_reason: Optional[str] = None

    # F9 (2026-05-17, C37 forensic): Director consultation gate. The
    # Coordinator MUST call request_director_guidance() at least once
    # before mark_sorry_intractable is allowed to terminate the session.
    # C37 DEMO 15/16/17 confirmed Coordinator abandoned in <140s with 0
    # Director invocations because intractable had no preconditions.
    director_consulted: bool = False
    director_consulted_count: int = 0

    # F12 (2026-05-19, Sprint C): Set by provers.py when a DirectorAgent
    # is successfully created. Read by workflow.py AgentExecutor to decide
    # whether to force Director invocation at iteration 4.
    _has_director: bool = False

    # Feature 1: Multi-file loading. Orchestrator pre-loads sibling .lean files.
    # Agents reference files by short name (e.g. "Lemmas.lean"), never by path.
    loaded_files: Dict[str, str] = field(default_factory=dict)
    target_filepath: str = ""   # absolute path of primary target
    target_filename: str = ""   # short name (e.g. "Lattice.lean")

    # Feature 2: Resource awareness for iterative deepening.
    # Agents check these to decide wrap-up vs continue.
    decomposition_budget: int = 5
    decomposition_budget_used: int = 0
    elapsed_seconds: float = 0.0
    max_session_seconds: float = 1800.0
    remaining_iterations: int = 0

    # Feature 2+3: Qualitative opinions circulating between agents.
    # Each agent writes its diagnostic here for subsequent agents to read.
    agent_opinions: Dict[str, str] = field(default_factory=dict)

    # B2 (issue #1224): SearchAgent consultation gate. The Coordinator
    # MUST have had SearchAgent explore reference_docs/ before
    # mark_sorry_intractable can terminate the session. C37 forensic showed
    # Coordinator decided intractable in 139.7s with 0 SearchAgent payload.
    search_agent_consulted: bool = False

    # B.8: Checkpoint support — save/restore state between phases
    _checkpoints: Dict[str, dict] = field(default_factory=dict, repr=False)

    def save_checkpoint(self, label: str = "") -> str:
        """Serialize current proof state as a checkpoint for later restore (B.8).

        Returns the checkpoint ID for restore.
        """
        import json as _json
        if not label:
            label = f"cp_{self.phase.value}_{self.iteration}"

        checkpoint = {
            "label": label,
            "phase": self.phase.value,
            "iteration": self.iteration,
            "current_goal": self.current_goal,
            "current_proof": list(self.current_proof),
            "tactic_history_count": len(self.tactic_history),
            "consecutive_failures": self.consecutive_failures,
            "error_count": self.error_count,
            "best_sorry_count": self.best_sorry_count,
            "consecutive_delta0_compiles": self.consecutive_delta0_compiles,
            "discovered_lemmas": list(self.discovered_lemmas),
            "plan": list(self.plan),
            "plan_phase": self.plan_phase,
            "sorry_goals": dict(self.sorry_goals),
            "timestamp": datetime.now().isoformat(),
        }
        self._checkpoints[label] = checkpoint
        return label

    def restore_checkpoint(self, label: str) -> bool:
        """Restore state from a named checkpoint (B.8). Returns True if found."""
        cp = self._checkpoints.get(label)
        if not cp:
            return False

        self.phase = ProofPhase(cp["phase"])
        self.iteration = cp["iteration"]
        self.current_goal = cp["current_goal"]
        self.current_proof = cp["current_proof"]
        self.consecutive_failures = cp["consecutive_failures"]
        self.error_count = cp["error_count"]
        self.best_sorry_count = cp["best_sorry_count"]
        self.consecutive_delta0_compiles = cp.get("consecutive_delta0_compiles", 0)
        self.discovered_lemmas = cp["discovered_lemmas"]
        self.plan = cp["plan"]
        self.plan_phase = cp["plan_phase"]
        self.sorry_goals = cp["sorry_goals"]
        return True

    def list_checkpoints(self) -> List[str]:
        """List available checkpoint labels."""
        return list(self._checkpoints.keys())

    def add_tactic_attempt(self, tactic: str, state_before: Optional[str] = None,
                           confidence: Optional[float] = None, explanation: Optional[str] = None,
                           success: bool = False, error: Optional[str] = None,
                           is_decomposition: bool = False) -> str:
        attempt_id = f"attempt_{len(self.tactic_history) + 1}"
        self.tactic_history.append(TacticAttempt(
            tactic=tactic, success=success, error=error,
            state_before=state_before, confidence=confidence,
            explanation=explanation, is_decomposition=is_decomposition,
        ))
        if success:
            self.current_proof.append(tactic)
        else:
            self.error_count += 1
            self.last_error = error
        return attempt_id

    def add_lemma(self, name: str, statement: str = "", namespace: str = "",
                  relevance: float = 0.5) -> str:
        lemma_id = f"{namespace}.{name}" if namespace else name
        lemma_info = f"{lemma_id}: {statement} (relevance: {relevance})"
        if lemma_info not in self.discovered_lemmas:
            self.discovered_lemmas.append(lemma_info)
        return lemma_id

    def add_verification(self, attempt_id: str, success: bool, output: str,
                         errors: str, exec_time_ms: float = 0.0) -> str:
        verif_id = f"verif_{len(self.verification_results) + 1}"
        self.verification_results.append({
            "id": verif_id, "attempt_id": attempt_id,
            "success": success, "output": output, "errors": errors,
            "exec_time_ms": exec_time_ms,
            "timestamp": datetime.now().isoformat(),
        })
        return verif_id

    def set_proof_complete(self, proof: str):
        self.final_proof = proof
        self.phase = ProofPhase.COMPLETE

    def increment_iteration(self):
        self.iteration += 1

    def designate_next_agent(self, agent_name: str):
        self._next_agent = agent_name

    def consume_next_agent_designation(self) -> Optional[str]:
        agent = self._next_agent
        self._next_agent = None
        return agent

    def get_state_snapshot(self, summarize: bool = True) -> Dict[str, Any]:
        if summarize:
            return {
                "session_id": self.session_id,
                "theorem": self.theorem_statement,
                "goal": self.current_goal,
                "phase": self.phase.value,
                "strategy": self.strategy.value,
                "iteration": f"{self.iteration}/{self.max_iterations}",
                "proof_steps": len(self.current_proof),
                "discovered_lemmas": len(self.discovered_lemmas),
                "errors": self.error_count,
                "last_error": self.last_error,
                "previous_tactics": [a.tactic for a in self.tactic_history[-3:]],
            }
        return self.to_dict()

    def get_context_summary(self) -> str:
        """Rich context summary for agents — from Lean-9 notebook pattern."""
        parts = []
        parts.append(f"Enonce: {self.theorem_statement}")
        if self.current_goal:
            parts.append(f"But courant: {self.current_goal}")
        parts.append(f"Phase: {self.phase.value} | Strategie: {self.strategy.value}")
        parts.append(f"Iteration: {self.iteration}/{self.max_iterations}")

        if self.discovered_lemmas:
            lemmas_str = "\n  ".join(self.discovered_lemmas[-10:])
            parts.append(f"Lemmes decouverts:\n  {lemmas_str}")

        if self.available_hypotheses:
            hyp_str = "\n  ".join(self.available_hypotheses[-15:])
            parts.append(f"Hypotheses disponibles:\n  {hyp_str}")

        if self.local_lemmas:
            parts.append(f"Lemmes locaux: {', '.join(self.local_lemmas[-20:])}")

        if self.tactic_history:
            recent = self.tactic_history[-5:]
            hist = "\n  ".join(
                f"{'OK' if a.success else 'FAIL'}: {a.tactic[:80]}"
                for a in recent
            )
            parts.append(f"Historique tactiques (derniers {len(recent)}):\n  {hist}")

        if self.last_error:
            parts.append(f"Derniere erreur: {self.last_error[:200]}")

        if self.sorry_goals:
            goals_str = "\n  ".join(
                f"L{l}: {g[:100]}" for l, g in self.sorry_goals.items()
            )
            parts.append(f"Buts sorry:\n  {goals_str}")

        parts.append(f"Echecs consecutifs: {self.consecutive_failures}")

        if self.plan:
            plan_str = "\n  ".join(
                f"{'>> ' if i == self.plan_phase else '   '}{i+1}. {step}"
                for i, step in enumerate(self.plan)
            )
            parts.append(f"Plan d'attaque (etape {self.plan_phase + 1}/{len(self.plan)}):\n{plan_str}")

        return "\n".join(parts)

    def select_next_agent(self) -> str:
        """Select next agent based on current phase — from Lean-9 ProofPhase routing."""
        if self._next_agent:
            return self.consume_next_agent_designation()

        if self.consecutive_failures >= 3:
            return "CoordinatorAgent"

        agent = PHASE_AGENT_MAP.get(self.phase)
        if agent:
            return agent

        return "TacticAgent"

    @property
    def proof_complete(self) -> bool:
        return self.phase == ProofPhase.COMPLETE

    @property
    def is_done(self) -> bool:
        return self.phase in (ProofPhase.COMPLETE, ProofPhase.FAILED)

    def snapshot(self) -> dict:
        return self.get_state_snapshot(summarize=True)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "session_id": self.session_id,
            "theorem_name": self.theorem_name,
            "theorem_statement": self.theorem_statement,
            "current_goal": self.current_goal,
            "current_proof": self.current_proof,
            "phase": self.phase.value,
            "strategy": self.strategy.value,
            "discovered_lemmas": self.discovered_lemmas,
            "iteration": self.iteration,
            "max_iterations": self.max_iterations,
            "error_count": self.error_count,
            "last_error": self.last_error,
        }


@dataclass
class SorryContext:
    """Context for sorry replacement in a .lean file."""
    filepath: str
    sorry_line: int
    goal_state: Optional[str] = None
    context_before: str = ""
    context_after: str = ""
    indentation: int = 0
    indent_str: str = ""
    full_file: str = ""
    sorry_count_before: int = 0
