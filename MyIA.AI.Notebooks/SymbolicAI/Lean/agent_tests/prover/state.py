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
    GENERATE = "generate"
    VERIFY = "verify"
    ANALYZE = "analyze"
    COMPLETE = "complete"
    FAILED = "failed"


@dataclass
class TacticAttempt:
    tactic: str
    success: bool
    error: Optional[str] = None
    timestamp: datetime = field(default_factory=datetime.now)
    state_before: Optional[str] = None
    confidence: Optional[float] = None
    explanation: Optional[str] = None


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

    def add_tactic_attempt(self, tactic: str, state_before: Optional[str] = None,
                           confidence: Optional[float] = None, explanation: Optional[str] = None,
                           success: bool = False, error: Optional[str] = None) -> str:
        attempt_id = f"attempt_{len(self.tactic_history) + 1}"
        self.tactic_history.append(TacticAttempt(
            tactic=tactic, success=success, error=error,
            state_before=state_before, confidence=confidence,
            explanation=explanation,
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
