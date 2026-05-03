"""
Multi-Agent Lean 4 Proof System
================================
Standalone script for testing multi-agent proof strategies.

Architecture:
  - ProofState: shared state between agents
  - 3 Agent roles: Coordinator, Tactic, Critic
  - Lean verification plugin (reuses lean_runner + WSL backend)
  - Turn-taking orchestration based on proof state
  - Full trace instrumentation with timings

Usage:
    cd MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests
    python multi_agent_proof.py --demo 1
    python multi_agent_proof.py --demo 5 --verbose
    python multi_agent_proof.py --batch --demos 1,2,3,4,5
    python multi_agent_proof.py --demo 3 --coordinator zai --tactic local --critic zai
"""

import os
import sys
import json
import time
import re
import argparse
from pathlib import Path
from datetime import datetime
from typing import Optional, Dict, Any, List
from dataclasses import dataclass, field
from enum import Enum

# ── Bootstrap: load .env and imports ──────────────────────────────────────────

_parent = Path(__file__).resolve().parent.parent
if str(_parent) not in sys.path:
    sys.path.insert(0, str(_parent))

from dotenv import load_dotenv
load_dotenv(_parent / ".env")

# ── Configuration ─────────────────────────────────────────────────────────────

LEAN_PROJECT_DIR = os.getenv("LEAN_PROJECT_DIR")

PROVIDERS = {
    "zai": {
        "base_url": os.getenv("ZAI_BASE_URL", "https://api.z.ai/api/coding/paas/v4"),
        "api_key": os.getenv("ZAI_API_KEY", ""),
        "models": {
            "reasoning": os.getenv("ZAI_CHAT_MODEL_ID", "glm-5.1"),
            "fast": os.getenv("ZAI_FAST_MODEL_ID", "glm-4.7"),
        }
    },
    "local": {
        "base_url": os.getenv("LOCAL_LLM_BASE_URL", ""),
        "api_key": os.getenv("LOCAL_LLM_API_KEY", ""),
        "models": {
            "reasoning": os.getenv("LOCAL_LLM_MODEL_ID", "qwen3.6-35b-a3b"),
            "fast": os.getenv("LOCAL_LLM_MODEL_ID", "qwen3.6-35b-a3b"),
        }
    },
}

SHAPLEY_IMPORTS = """import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import CooperativeGames.Basic
"""


# ── Demo Theorems ─────────────────────────────────────────────────────────────

DEMOS = {
    1: {
        "name": "DEMO_1_REFLEXIVITY",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "proof": "rfl",
        "imports": None,
        "description": "Trivial - rfl suffit",
        "difficulty": "trivial",
    },
    2: {
        "name": "DEMO_2_ZERO_ADD",
        "theorem": "theorem demo_zero_add (n : Nat) : 0 + n = n",
        "proof": "omega",
        "imports": None,
        "description": "Simple - omega or Nat.zero_add",
        "difficulty": "simple",
    },
    3: {
        "name": "DEMO_3_DISTRIBUTIVITY",
        "theorem": "theorem demo_dist (a b c : Nat) : a * c + b * c = (a + b) * c",
        "proof": "omega",
        "imports": None,
        "description": "Intermediate - distributivity reversed",
        "difficulty": "intermediate",
    },
    4: {
        "name": "DEMO_4_SHAPLEY_SIMPLE",
        "theorem": "theorem test_coef_shift (n s : Nat) (h : s + 2 <= n) : (s + 1) * 1 = s + 1",
        "proof": "omega",
        "imports": SHAPLEY_IMPORTS,
        "description": "Shapley-style Nat arithmetic with Mathlib",
        "difficulty": "intermediate",
    },
    5: {
        "name": "DEMO_5_FINSET_SUM_REAL",
        "theorem": "theorem demo_finset_sum_erase {α : Type*} [DecidableEq α] [Fintype α] (s : Finset α) (a : α) (f : α → Real) (ha : a ∈ s) : ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x - f a",
        "proof": "have h := Finset.sum_erase_add s f ha; linarith",
        "imports": SHAPLEY_IMPORTS,
        "description": "Finset sum with erase + Real subtraction (Shapley-style)",
        "difficulty": "advanced",
    },
}


# ══════════════════════════════════════════════════════════════════════════════
# TRACE LOGGER - Full instrumentation
# ══════════════════════════════════════════════════════════════════════════════

class TraceLogger:
    """Captures full multi-agent conversation traces with timing."""

    def __init__(self, output_dir: str = "traces"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.entries = []
        self.session_start = time.time()
        self.phase_timings: Dict[str, float] = {}

    def log(self, agent: str, role: str, content: str, duration_s: float = 0,
            tool_name: str = None, tool_args: dict = None, tool_result: str = None,
            model: str = None, tokens: dict = None, phase: str = None,
            state_snapshot: dict = None):
        entry = {
            "timestamp": round(time.time() - self.session_start, 3),
            "agent": agent,
            "role": role,
            "content": content,
            "duration_s": round(duration_s, 3),
        }
        if tool_name:
            entry["tool_call"] = tool_name
            entry["tool_args"] = tool_args
            entry["tool_result"] = (tool_result or "")[:500]
        if model:
            entry["model"] = model
        if tokens:
            entry["tokens"] = tokens
        if phase:
            entry["phase"] = phase
        if state_snapshot:
            entry["state"] = state_snapshot
        self.entries.append(entry)

        # Track phase timings
        if phase:
            self.phase_timings[phase] = self.phase_timings.get(phase, 0) + duration_s

        # Console output
        ts = f"[+{entry['timestamp']:.1f}s]"
        if tool_name:
            print(f"  {ts} {agent} -> {tool_name}({json.dumps(tool_args or {})[:80]}) -> {duration_s:.2f}s")
        else:
            preview = (content or "")[:120].replace("\n", " ")
            print(f"  {ts} {agent} [{role}]: {preview}...")

    def save(self, name: str = None):
        if not name:
            name = f"trace_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        path = self.output_dir / f"{name}.json"
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.entries, f, indent=2, ensure_ascii=False)
        print(f"Trace saved: {path} ({len(self.entries)} entries)")
        return str(path)

    def summary(self):
        agents = {}
        for e in self.entries:
            a = e["agent"]
            if a not in agents:
                agents[a] = {"calls": 0, "tool_calls": 0, "total_s": 0, "tokens": 0}
            agents[a]["calls"] += 1
            if e.get("tool_call"):
                agents[a]["tool_calls"] += 1
            agents[a]["total_s"] += e.get("duration_s", 0)
            if e.get("tokens"):
                agents[a]["tokens"] += e["tokens"].get("total", 0)
        return agents


# ══════════════════════════════════════════════════════════════════════════════
# PROOF STATE - Shared state between agents
# ══════════════════════════════════════════════════════════════════════════════

class ProofPhase(Enum):
    INIT = "init"
    ANALYZE = "analyze"
    GENERATE = "generate"
    VERIFY = "verify"
    CRITIQUE = "critique"
    COMPLETE = "complete"
    FAILED = "failed"

@dataclass
class TacticAttempt:
    tactic: str
    success: bool
    error: Optional[str] = None
    agent: Optional[str] = None
    timestamp: float = 0
    lean_time_s: float = 0

@dataclass
class ProofState:
    """Shared state for multi-agent proof sessions."""
    theorem_name: str = ""
    theorem_statement: str = ""
    imports: Optional[str] = None

    phase: ProofPhase = ProofPhase.INIT
    iteration: int = 0
    max_iterations: int = 6

    current_tactic: Optional[str] = None
    tactic_history: List[TacticAttempt] = field(default_factory=list)
    discovered_lemmas: List[str] = field(default_factory=list)

    last_error: Optional[str] = None
    error_count: int = 0
    final_proof: Optional[str] = None

    # Agent communication
    coordinator_directive: Optional[str] = None
    critic_feedback: Optional[str] = None

    # Timing
    start_time: float = 0
    total_llm_s: float = 0
    total_lean_s: float = 0

    def add_attempt(self, tactic: str, success: bool, error: str = None,
                    agent: str = None, lean_time: float = 0):
        self.tactic_history.append(TacticAttempt(
            tactic=tactic, success=success, error=error,
            agent=agent, timestamp=time.time(), lean_time_s=lean_time,
        ))
        if success:
            self.final_proof = tactic
            self.phase = ProofPhase.COMPLETE
        else:
            self.error_count += 1
            self.last_error = error

    def snapshot(self) -> dict:
        """Lightweight state snapshot for agent context."""
        return {
            "theorem": self.theorem_statement,
            "iteration": f"{self.iteration}/{self.max_iterations}",
            "phase": self.phase.value,
            "attempts": len(self.tactic_history),
            "errors": self.error_count,
            "last_error": (self.last_error or "")[:300],
            "discovered_lemmas": self.discovered_lemmas[-5:],
            "coordinator_directive": self.coordinator_directive,
            "critic_feedback": (self.critic_feedback or "")[:300],
            "previous_tactics": [a.tactic for a in self.tactic_history[-3:]],
        }

    @property
    def is_done(self) -> bool:
        return self.phase in (ProofPhase.COMPLETE, ProofPhase.FAILED)


# ══════════════════════════════════════════════════════════════════════════════
# LEAN VERIFICATION PLUGIN
# ══════════════════════════════════════════════════════════════════════════════

# Global LeanVerifier instance (shared across all verifications in a session)
_lsp_server = None
_verifier = None


def start_lsp_server(project_dir: str, warmup: bool = True,
                     verbose: bool = False) -> bool:
    """Start the persistent LSP server. Returns True if successful."""
    global _lsp_server
    from lean_server import LeanLSPServer

    _lsp_server = LeanLSPServer(project_dir=project_dir, verbose=verbose)
    print("  [LSP] Starting persistent lake serve server...")
    t0 = time.time()
    if not _lsp_server.start(timeout=60):
        print("  [LSP] FAILED to start server")
        _lsp_server = None
        return False
    print(f"  [LSP] Server initialized in {time.time()-t0:.1f}s")

    if warmup:
        print("  [LSP] Warming up (loading Mathlib)...")
        t1 = time.time()
        ok = _lsp_server.warmup(timeout=300)
        print(f"  [LSP] Warmup {'OK' if ok else 'FAILED'} in {time.time()-t1:.1f}s")
        if not ok:
            print("  [LSP] Continuing without warmup...")

    return True


def stop_lsp_server():
    """Stop the persistent LSP server."""
    global _lsp_server
    if _lsp_server:
        _lsp_server.stop()
        _lsp_server = None


def verify_with_lean(theorem: str, tactic: str, imports: Optional[str],
                     project_dir: Optional[str], trace: TraceLogger,
                     agent_name: str = "LeanVerifier") -> dict:
    """Verify a Lean proof using LeanVerifier with LEAN_PATH.

    Strategy:
      - No imports → fast LEAN_PATH (~5-6s)
      - With imports → full LEAN_PATH with Mathlib deps (~130-150s)
      - Uses persistent LeanVerifier instance for session reuse

    Returns {success, errors, time_s, backend}.
    """
    global _lsp_server, _verifier

    if imports:
        code = f"{imports}\n{theorem} := by {tactic}"
    else:
        code = f"{theorem} := by {tactic}"

    # Use LSP server wrapper if available (--lsp mode)
    if _lsp_server is not None:
        use_lake_env = imports is not None
        start = time.time()
        result = _lsp_server.verify(code, timeout=300, use_lake_env=use_lake_env)
        duration = time.time() - start

        if result is not None:
            success = result["success"]
            backend = result.get("backend", "lean_path")
            trace.log(
                agent=agent_name, role="verification",
                content=f"{theorem[:60]} := by {tactic[:60]}",
                duration_s=duration, tool_name="verify_proof",
                tool_args={"theorem": theorem[:80], "proof": tactic[:80]},
                tool_result=f"success={success}, backend={backend}, "
                            f"errors={result['errors'][:200]}",
                phase="verify",
            )
            return {
                "success": success,
                "errors": result["errors"],
                "time_s": duration,
                "backend": backend,
            }

    # Use LeanVerifier directly (fast_path for no imports, full_path for Mathlib)
    if project_dir:
        if _verifier is None:
            from lean_server import LeanVerifier
            _verifier = LeanVerifier(project_dir=project_dir, verbose=False)

        start = time.time()
        result = _verifier.verify(code)
        duration = time.time() - start

        success = result["success"]
        backend = result.get("backend", "lean_verifier")
        errors = result.get("errors", "")

        trace.log(
            agent=agent_name, role="verification",
            content=f"{theorem[:60]} := by {tactic[:60]}",
            duration_s=duration, tool_name="verify_proof",
            tool_args={"theorem": theorem[:80], "proof": tactic[:80]},
            tool_result=f"success={success}, backend={backend}, "
                        f"errors={errors[:200]}",
            phase="verify",
        )

        return {
            "success": success,
            "errors": errors,
            "time_s": duration,
            "backend": backend,
        }

    # Last resort fallback: lean_runner subprocess
    from lean_runner import LeanRunner
    runner = LeanRunner(backend="auto", timeout=300)
    start = time.time()
    result = runner.run(code, project_dir=project_dir)
    duration = time.time() - start

    success = result.success and "error" not in (result.errors or "").lower()

    trace.log(
        agent=agent_name, role="verification",
        content=f"{theorem[:60]} := by {tactic[:60]}",
        duration_s=duration, tool_name="verify_proof",
        tool_args={"theorem": theorem[:80], "proof": tactic[:80]},
        tool_result=f"success={success}, errors={(result.errors or '')[:200]}",
        phase="verify",
    )

    return {
        "success": success,
        "errors": result.errors or "",
        "time_s": duration,
        "backend": "subprocess",
    }


# ══════════════════════════════════════════════════════════════════════════════
# LLM CLIENT (shared across agents)
# ══════════════════════════════════════════════════════════════════════════════

class LLMClient:
    """Unified LLM client with per-call model override for agent heterogeneity."""

    def __init__(self, provider: str = "zai", trace: TraceLogger = None):
        self.provider = provider
        self.trace = trace
        cfg = PROVIDERS.get(provider, PROVIDERS["zai"])

        from openai import OpenAI
        self.client = OpenAI(api_key=cfg["api_key"], base_url=cfg["base_url"])
        self.model_reasoning = cfg["models"]["reasoning"]
        self.model_fast = cfg["models"]["fast"]

    def chat(self, messages: list, model: str = None, thinking: bool = True,
             agent_name: str = "LLM", max_tokens: int = 4096,
             temperature: float = 0.3) -> tuple:
        """Returns (content, reasoning, tokens_dict)."""
        model_id = model or (self.model_reasoning if thinking else self.model_fast)
        start = time.time()

        kwargs = {
            "model": model_id,
            "messages": messages,
            "max_tokens": max(max_tokens, 4096),
            "temperature": temperature,
        }

        try:
            response = self.client.chat.completions.create(**kwargs)
            duration = time.time() - start
            msg = response.choices[0].message
            content = msg.content or ""
            reasoning = getattr(msg, "reasoning_content", None) or ""

            # Extract from reasoning if content is empty
            if not content.strip() and reasoning.strip():
                m = re.search(r'```\w*\n(.*?)```', reasoning, re.DOTALL)
                if m:
                    content = m.group(1).strip()
                else:
                    lines = [l.strip() for l in reasoning.strip().split('\n') if l.strip()]
                    if lines:
                        content = lines[-1]

            tokens = {
                "prompt": response.usage.prompt_tokens if response.usage else 0,
                "completion": response.usage.completion_tokens if response.usage else 0,
                "total": response.usage.total_tokens if response.usage else 0,
            }

            if self.trace:
                self.trace.log(agent=agent_name, role="assistant", content=content,
                               duration_s=duration, model=model_id, tokens=tokens)
                if reasoning:
                    self.trace.log(agent=agent_name, role="thinking", content=reasoning,
                                   duration_s=0, model=model_id)

            return content, reasoning, tokens

        except Exception as e:
            duration = time.time() - start
            if self.trace:
                self.trace.log(agent=agent_name, role="error", content=str(e), duration_s=duration)
            return f"ERROR: {e}", "", {}


# ══════════════════════════════════════════════════════════════════════════════
# AGENT SYSTEM PROMPTS
# ══════════════════════════════════════════════════════════════════════════════

COORDINATOR_PROMPT = """You are a Lean 4 proof coordinator. Analyze the proof state and direct the next tactic.

Output EXACTLY ONE of:
- STRATEGY: <approach> -- what tactic pattern to try
- LEMMA: <name> -- a specific lemma to use
- GIVE_UP -- if too many failures

Keep your response under 3 lines. No markdown."""

TACTIC_PROMPT = """You are a Lean 4 tactic generator. Given a theorem statement and context, provide ONLY the tactic sequence.

The theorem already has `:= by` so provide ONLY the tactic(s) after `by`.

Rules:
- Reply with ONLY the tactic(s), no explanation, no markdown, no code fences
- DO NOT prefix with `by` - it is already present
- Chain tactics with `;` or use `<;>` for branching
- Use `<;> try` for optional subgoals after branching tactics

Tactic priority:
1. omega / linarith - linear arithmetic (Nat/Int/Real)
2. simp - simplification engine
3. rfl - ONLY for definitional equality (a = a)
4. exact <term> - provide a proof term
5. rw [lemma] - rewrite with a lemma
6. ring - ring equalities
7. field_simp / ring_nf - field/ring normalization
8. aesop - automated search
9. exact? - let Mathlib suggest

Common pitfalls:
- `rfl` fails on `0 + n = n`: use omega or simp
- `omega` only works for Nat/Int linear goals. Use `linarith` for Real
- `simp` can close many goals if given the right lemmas: simp [lemma1, lemma2]
- If `rw [lemma]` solves the goal completely, do NOT add `rfl` after it
- If error says "No goals to be solved", your previous tactic already closed the goal — remove the trailing tactic
- If error says "made no progress", the tactic didn't change the goal — try a different approach
- For distributivity: use `ring` or `omega` for linear cases, `Nat.mul_add` / `Nat.add_mul` for rewriting"""

CRITIC_PROMPT = """You are a Lean 4 proof critic. Analyze why a tactic failed and suggest what to try differently.

Given the theorem, the failed tactic, and the Lean error, output:
- DIAGNOSIS: <1-line root cause>
- SUGGESTION: <tactic or approach to try>

Keep your response under 4 lines. No markdown."""


def extract_tactic(raw_output: str) -> str:
    """Extract a clean tactic from LLM output that may contain prose.

    Strategy:
      1. If the output is already a clean tactic (no prose markers), return as-is
      2. Try to extract from code fences (```...```)
      3. Try to extract the first Lean-like expression
      4. Fall back to the raw output stripped
    """
    text = raw_output.strip()

    # If it starts with common tactic keywords, it's probably clean
    tactic_starters = (
        "rfl", "omega", "linarith", "simp", "exact", "rw [", "rw[",
        "have ", "constructor", "cases ", "induction ", "intro ",
        "apply ", "use ", "conv ", "funext ", "ext ", "field_simp",
        "ring", "aesop", "exact?", "norm_num", "decide", "trivial",
        "by_contra ", "by_cases ", "push_neg ", "itauto", "omega",
        "Nat.", "Finset.", "Mathlib.", "split", "left", "right",
        "tauto", "contradiction", "exfalso", "assumption",
        "rcases ", "obtain ", "choose ", "open ", "set ",
        "show ", "suffices ", "refine ", "subst ", "rename ",
        "dsimp", "change ", "replace ", "specialize ",
        "convert ", "symm", "trans ", "calc ", "unfold ",
    )
    first_line = text.split("\n")[0].strip()
    if any(first_line.startswith(s) or first_line == s for s in tactic_starters):
        return first_line

    # Try extracting from code fences
    import re
    code_fence = re.search(r'```(?:lean|lean4)?\s*\n(.*?)```', text, re.DOTALL)
    if code_fence:
        return code_fence.group(1).strip().split("\n")[0].strip()

    # Try extracting after "SUGGESTION:" or "tactic:" prefix
    for prefix in ("SUGGESTION: ", "Tactic: ", "Answer: ", "Proof: "):
        if prefix.lower() in text.lower():
            idx = text.lower().index(prefix.lower())
            remainder = text[idx + len(prefix):].strip()
            line = remainder.split("\n")[0].strip()
            if line:
                return line

    # Try finding the first line that looks like a tactic
    for line in text.split("\n"):
        line = line.strip()
        if not line or line.startswith("#") or line.startswith("//"):
            continue
        if any(line.startswith(s) or line == s for s in tactic_starters):
            return line

    # Last resort: return the first non-empty line
    for line in text.split("\n"):
        line = line.strip()
        if line and not line.startswith("#") and len(line) > 2:
            return line

    return text


# ══════════════════════════════════════════════════════════════════════════════
# MULTI-AGENT ORCHESTRATOR
# ══════════════════════════════════════════════════════════════════════════════

class MultiAgentOrchestrator:
    """
    Orchestrates 3 agents (Coordinator, Tactic, Critic) with turn-taking.

    Turn order per iteration:
      1. Coordinator analyzes state, sets directive
      2. Tactic generates tactic based on directive + state
      3. Lean verifies the tactic
      4. If failed: Critic analyzes error, feeds back to Coordinator

    Agent model configuration:
      - All agents can use different providers/models
      - Start with GLM-5.1 for all, then try downgrading
    """

    def __init__(
        self,
        trace: TraceLogger,
        coordinator_provider: str = "zai",
        coordinator_thinking: bool = True,
        tactic_provider: str = "zai",
        tactic_thinking: bool = True,
        critic_provider: str = "zai",
        critic_thinking: bool = False,  # Critic can use fast model
    ):
        self.trace = trace

        # Create separate LLM clients per agent (allows different providers)
        self.coordinator_llm = LLMClient(provider=coordinator_provider, trace=trace)
        self.tactic_llm = LLMClient(provider=tactic_provider, trace=trace)
        self.critic_llm = LLMClient(provider=critic_provider, trace=trace)

        self.coordinator_thinking = coordinator_thinking
        self.tactic_thinking = tactic_thinking
        self.critic_thinking = critic_thinking

        # Labels for trace
        self.config_label = (
            f"coord={coordinator_provider}"
            f" tactic={tactic_provider}"
            f" critic={critic_provider}"
        )

    def prove(self, theorem: str, imports: Optional[str] = None,
              max_iterations: int = 6) -> dict:
        """Run multi-agent proof attempt. Returns {success, proof, iterations, ...}."""

        state = ProofState(
            theorem_statement=theorem,
            imports=imports,
            max_iterations=max_iterations,
            start_time=time.time(),
        )
        state.phase = ProofPhase.ANALYZE

        print(f"\n{'='*70}")
        print(f"MULTI-AGENT PROOF: {theorem[:80]}...")
        print(f"Config: {self.config_label}")
        print(f"{'='*70}")

        # Conversation histories per agent (for multi-turn within session)
        tactic_history = [{"role": "system", "content": TACTIC_PROMPT}]
        coordinator_history = [{"role": "system", "content": COORDINATOR_PROMPT}]
        critic_history = [{"role": "system", "content": CRITIC_PROMPT}]

        for iteration in range(1, max_iterations + 1):
            state.iteration = iteration
            print(f"\n--- Iteration {iteration}/{max_iterations} ---")

            # ── Turn 1: Coordinator analyzes state ─────────────────────────
            snap = state.snapshot()
            coord_msg = (
                f"Theorem: {theorem}\n"
                f"State: {json.dumps(snap, ensure_ascii=False)}\n"
                f"What strategy should we try?"
            )
            coordinator_history.append({"role": "user", "content": coord_msg})

            coord_content, _, coord_tokens = self.coordinator_llm.chat(
                messages=coordinator_history,
                thinking=self.coordinator_thinking,
                agent_name="Coordinator",
            )
            coordinator_history.append({"role": "assistant", "content": coord_content})

            # Parse coordinator directive
            state.coordinator_directive = coord_content.strip()
            state.total_llm_s += coord_tokens.get("total", 0) / 1000  # rough proxy
            print(f"  Coordinator: {coord_content[:100]}")

            # Check if coordinator says give up
            if "GIVE_UP" in coord_content.upper():
                print("  Coordinator gave up.")
                state.phase = ProofPhase.FAILED
                break

            # ── Turn 2: Tactic agent generates tactic ──────────────────────
            tactic_msg = f"Prove this Lean 4 theorem:\n{theorem}"
            if imports:
                tactic_msg += "\n\nAvailable imports: Mathlib (Finset, Real, BigOperators, Tactic)"
            if state.coordinator_directive:
                tactic_msg += f"\n\nCoordinator suggests: {state.coordinator_directive}"
            if state.critic_feedback:
                tactic_msg += f"\n\nPrevious failure analysis: {state.critic_feedback}"
            if state.tactic_history:
                tried = [a.tactic for a in state.tactic_history[-3:]]
                tactic_msg += f"\n\nAlready tried (DO NOT repeat): {tried}"

            tactic_history.append({"role": "user", "content": tactic_msg})

            tactic_content, _, tactic_tokens = self.tactic_llm.chat(
                messages=tactic_history,
                thinking=self.tactic_thinking,
                agent_name="TacticAgent",
            )
            tactic_history.append({"role": "assistant", "content": tactic_content})

            tactic = extract_tactic(tactic_content)
            state.total_llm_s += tactic_tokens.get("total", 0) / 1000
            print(f"  Tactic: {tactic[:100]}")

            if tactic.startswith("ERROR:"):
                state.critic_feedback = f"LLM error: {tactic}"
                continue

            # ── Turn 3: Lean verification ──────────────────────────────────
            state.phase = ProofPhase.VERIFY
            result = verify_with_lean(
                theorem=theorem, tactic=tactic, imports=imports,
                project_dir=LEAN_PROJECT_DIR, trace=self.trace,
            )
            state.total_lean_s += result["time_s"]

            if result["success"]:
                print(f"  PROOF VALID! ({result['time_s']:.1f}s Lean)")
                state.add_attempt(tactic, success=True, agent="TacticAgent",
                                  lean_time=result["time_s"])
                break
            else:
                raw_error = result["errors"][:500]
                # Add actionable hints for common error patterns
                hints = []
                if "No goals to be solved" in raw_error:
                    hints.append("HINT: Your first tactic already closed the goal. Remove the trailing tactics (like `rfl`).")
                elif "made no progress" in raw_error:
                    hints.append("HINT: The tactic didn't change the goal. Try a different approach.")
                elif "unknown tactic" in raw_error:
                    hints.append("HINT: This tactic requires Mathlib import. Try omega, simp, or rw instead.")
                elif "could not prove the goal" in raw_error:
                    hints.append("HINT: The tactic was applicable but couldn't close the goal. Try a more powerful tactic or split the goal.")
                error = raw_error
                if hints:
                    error = raw_error + "\n" + "\n".join(hints)
                state.add_attempt(tactic, success=False, error=error,
                                  agent="TacticAgent", lean_time=result["time_s"])
                print(f"  FAILED: {error[:200]}")

            # ── Turn 4: Critic analyzes error (only on failure) ────────────
            state.phase = ProofPhase.CRITIQUE
            critic_msg = (
                f"Theorem: {theorem}\n"
                f"Failed tactic: {tactic}\n"
                f"Lean error: {error}\n"
                f"Why did this fail and what should we try next?"
            )
            critic_history.append({"role": "user", "content": critic_msg})

            critic_content, _, critic_tokens = self.critic_llm.chat(
                messages=critic_history,
                thinking=self.critic_thinking,
                agent_name="CriticAgent",
            )
            critic_history.append({"role": "assistant", "content": critic_content})

            state.critic_feedback = critic_content.strip()
            state.total_llm_s += critic_tokens.get("total", 0) / 1000
            print(f"  Critic: {critic_content[:100]}")

            # Loop back to coordinator with updated state

        # ── Final result ───────────────────────────────────────────────────
        total_s = time.time() - state.start_time

        if not state.is_done:
            state.phase = ProofPhase.FAILED

        return {
            "success": state.final_proof is not None,
            "proof": state.final_proof,
            "iterations": state.iteration,
            "attempts": len(state.tactic_history),
            "total_s": round(total_s, 1),
            "lean_s": round(state.total_lean_s, 1),
            "config": self.config_label,
            "state": state.snapshot(),
        }


# ══════════════════════════════════════════════════════════════════════════════
# SINGLE AGENT (baseline comparison)
# ══════════════════════════════════════════════════════════════════════════════

class SingleAgentProver:
    """Single agent baseline (like test_agent_trace.py but compatible interface)."""

    def __init__(self, trace: TraceLogger, provider: str = "zai", thinking: bool = True):
        self.trace = trace
        self.llm = LLMClient(provider=provider, trace=trace)
        self.thinking = thinking
        self.provider = provider
        self.config_label = f"single={provider}_{'thinkON' if thinking else 'thinkOFF'}"

    def prove(self, theorem: str, imports: Optional[str] = None,
              max_iterations: int = 3) -> dict:
        """Single-agent proof with retry loop."""
        state = ProofState(
            theorem_statement=theorem,
            imports=imports,
            max_iterations=max_iterations,
            start_time=time.time(),
        )

        print(f"\n{'='*70}")
        print(f"SINGLE-AGENT: {theorem[:80]}...")
        print(f"Config: {self.config_label}")
        print(f"{'='*70}")

        messages = [{"role": "system", "content": TACTIC_PROMPT}]

        for attempt in range(1, max_iterations + 1):
            state.iteration = attempt
            print(f"\n--- Attempt {attempt}/{max_iterations} ---")

            if attempt == 1:
                user_msg = f"Prove this Lean 4 theorem:\n{theorem}"
                if imports:
                    user_msg += "\n\nAvailable imports: Mathlib (Finset, Real, BigOperators, Tactic)"
            else:
                user_msg = (
                    f"That tactic failed. Lean error:\n{state.last_error}\n\n"
                    f"Try a DIFFERENT tactic to prove:\n{theorem}"
                )
            messages.append({"role": "user", "content": user_msg})

            content, _, tokens = self.llm.chat(
                messages=messages,
                thinking=self.thinking,
                agent_name="TacticAgent",
            )
            messages.append({"role": "assistant", "content": content})
            state.total_llm_s += tokens.get("total", 0) / 1000

            tactic = extract_tactic(content)
            print(f"  Tactic: {tactic[:100]}")

            # Verify
            result = verify_with_lean(
                theorem=theorem, tactic=tactic, imports=imports,
                project_dir=LEAN_PROJECT_DIR, trace=self.trace,
            )
            state.total_lean_s += result["time_s"]

            if result["success"]:
                print(f"  PROOF VALID! ({result['time_s']:.1f}s Lean)")
                state.add_attempt(tactic, success=True, agent="TacticAgent",
                                  lean_time=result["time_s"])
                break
            else:
                raw_error = result["errors"][:500]
                hints = []
                if "No goals to be solved" in raw_error:
                    hints.append("Your first tactic already closed the goal. Remove the trailing tactics (like `rfl`).")
                elif "made no progress" in raw_error:
                    hints.append("The tactic didn't change the goal. Try a different approach.")
                elif "unknown tactic" in raw_error:
                    hints.append("This tactic requires Mathlib import. Try omega, simp, or rw instead.")
                error = raw_error
                if hints:
                    error = raw_error + "\n" + "\n".join(hints)
                state.add_attempt(tactic, success=False, error=error,
                                  agent="TacticAgent", lean_time=result["time_s"])
                print(f"  FAILED: {result['errors'][:200]}")

        total_s = time.time() - state.start_time
        if not state.is_done:
            state.phase = ProofPhase.FAILED

        return {
            "success": state.final_proof is not None,
            "proof": state.final_proof,
            "iterations": state.iteration,
            "attempts": len(state.tactic_history),
            "total_s": round(total_s, 1),
            "lean_s": round(state.total_lean_s, 1),
            "config": self.config_label,
        }


# ══════════════════════════════════════════════════════════════════════════════
# BATCH RUNNER
# ══════════════════════════════════════════════════════════════════════════════

def run_batch(demos: list = None, configs: list = None, max_iterations: int = 3):
    """
    Run multiple demo x config combinations.

    configs format: list of dicts with keys:
        - name: label
        - mode: "multi" or "single"
        - coordinator_provider, tactic_provider, critic_provider (multi)
        - coordinator_thinking, tactic_thinking, critic_thinking (multi)
        - provider, thinking (single)
    """
    if demos is None:
        demos = [1, 2, 3]
    if configs is None:
        configs = [
            {
                "name": "multi-all-zai-thinkON",
                "mode": "multi",
                "coordinator_provider": "zai", "coordinator_thinking": True,
                "tactic_provider": "zai", "tactic_thinking": True,
                "critic_provider": "zai", "critic_thinking": False,
            },
            {
                "name": "single-zai-thinkON",
                "mode": "single",
                "provider": "zai", "thinking": True,
            },
        ]

    results = []
    for demo_num in demos:
        demo = DEMOS.get(demo_num)
        if not demo:
            continue

        for cfg in configs:
            label = f"{demo['name']} | {cfg['name']}"
            print(f"\n{'#'*70}")
            print(f"# BATCH: {label}")
            print(f"{'#'*70}")

            trace = TraceLogger()
            t0 = time.time()

            try:
                if cfg["mode"] == "multi":
                    prover = MultiAgentOrchestrator(
                        trace=trace,
                        coordinator_provider=cfg.get("coordinator_provider", "zai"),
                        coordinator_thinking=cfg.get("coordinator_thinking", True),
                        tactic_provider=cfg.get("tactic_provider", "zai"),
                        tactic_thinking=cfg.get("tactic_thinking", True),
                        critic_provider=cfg.get("critic_provider", "zai"),
                        critic_thinking=cfg.get("critic_thinking", False),
                    )
                else:
                    prover = SingleAgentProver(
                        trace=trace,
                        provider=cfg.get("provider", "zai"),
                        thinking=cfg.get("thinking", True),
                    )

                result = prover.prove(
                    theorem=demo["theorem"],
                    imports=demo.get("imports"),
                    max_iterations=max_iterations,
                )

                trace_name = f"{demo['name']}_{cfg['name']}"
                trace.save(trace_name)

                # Extract LLM time from trace
                llm_time = sum(e["duration_s"] for e in trace.entries
                               if e["role"] in ("assistant", "thinking"))

                results.append({
                    "demo": demo_num,
                    "demo_name": demo["name"],
                    "config": cfg["name"],
                    "mode": cfg["mode"],
                    "success": result["success"],
                    "iterations": result["iterations"],
                    "proof": result.get("proof", ""),
                    "total_s": result["total_s"],
                    "llm_s": round(llm_time, 1),
                    "lean_s": result["lean_s"],
                    "trace_file": f"traces/{trace_name}.json",
                })

            except Exception as e:
                total_s = time.time() - t0
                print(f"  ERROR: {e}")
                results.append({
                    "demo": demo_num, "demo_name": demo["name"],
                    "config": cfg["name"], "mode": cfg.get("mode", "?"),
                    "success": False, "iterations": 0, "proof": f"ERROR: {e}",
                    "total_s": round(total_s, 1), "llm_s": 0, "lean_s": 0,
                    "trace_file": None,
                })

    # Print summary table
    print(f"\n{'='*100}")
    print("BATCH SUMMARY")
    print(f"{'='*100}")
    print(f"{'Demo':<28} {'Config':<30} {'OK?':<5} {'Iter':<5} "
          f"{'Total':>7} {'LLM':>6} {'Lean':>6} {'Proof'}")
    print("-" * 110)
    for r in results:
        print(f"{r['demo_name']:<28} {r['config']:<30} "
              f"{'OK' if r['success'] else 'FAIL':<5} {r['iterations']:<5} "
              f"{r['total_s']:>6.1f}s {r['llm_s']:>5.1f}s {r['lean_s']:>5.1f}s "
              f"{(r.get('proof') or '')[:35]}")

    # Save summary
    ts = datetime.now().strftime('%Y%m%d_%H%M%S')
    summary_path = Path("traces") / f"batch_summary_{ts}.json"
    with open(summary_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    print(f"\nBatch summary saved: {summary_path}")

    # Performance analysis
    print(f"\n{'='*60}")
    print("PERFORMANCE ANALYSIS")
    print(f"{'='*60}")
    for r in results:
        if r["success"]:
            lean_pct = (r["lean_s"] / r["total_s"] * 100) if r["total_s"] > 0 else 0
            llm_pct = (r["llm_s"] / r["total_s"] * 100) if r["total_s"] > 0 else 0
            print(f"  {r['demo_name'][:25]:25s} | "
                  f"Lean: {lean_pct:4.0f}% ({r['lean_s']:.1f}s) | "
                  f"LLM: {llm_pct:4.0f}% ({r['llm_s']:.1f}s) | "
                  f"Config: {r['config']}")

    return results


# ══════════════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description="Multi-Agent Lean Proof System")
    parser.add_argument("--demo", type=int, default=1, help="Demo number (1-5)")
    parser.add_argument("--batch", action="store_true", help="Run batch over demos x configs")
    parser.add_argument("--demos", type=str, default="1,2,3,4,5",
                        help="Comma-separated demo numbers for batch")
    parser.add_argument("--max-iterations", type=int, default=3,
                        help="Max proof iterations per attempt")
    parser.add_argument("--mode", choices=["multi", "single", "both"], default="both",
                        help="Agent mode to test")
    parser.add_argument("--coordinator", default="zai", help="Coordinator provider")
    parser.add_argument("--tactic", default="zai", help="Tactic agent provider")
    parser.add_argument("--critic", default="zai", help="Critic agent provider")
    parser.add_argument("--no-thinking", action="store_true", help="Disable thinking for all agents")
    parser.add_argument("--verify-only", action="store_true", help="Just verify known proof")
    parser.add_argument("--lsp", action="store_true",
                        help="Use persistent LSP server for fast verification")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    demo = DEMOS.get(args.demo)
    if not demo:
        print(f"Unknown demo {args.demo}. Available: {list(DEMOS.keys())}")
        sys.exit(1)

    # Start persistent LSP server if requested
    if args.lsp and LEAN_PROJECT_DIR:
        start_lsp_server(LEAN_PROJECT_DIR, warmup=True, verbose=args.verbose)

    try:
        _run_main(args, demo)
    finally:
        stop_lsp_server()


def _run_main(args, demo):
    """Main logic, separated for LSP cleanup wrapping."""
    # Verify-only mode
    if args.verify_only:
        trace = TraceLogger()
        result = verify_with_lean(
            theorem=demo["theorem"], tactic=demo["proof"],
            imports=demo.get("imports"), project_dir=LEAN_PROJECT_DIR,
            trace=trace,
        )
        backend = result.get("backend", "subprocess")
        print(f"Known proof '{demo['proof']}': {'VALID' if result['success'] else 'INVALID'} "
              f"({result['time_s']:.1f}s via {backend})")
        if result["errors"]:
            print(f"Errors: {result['errors'][:300]}")
        return

    thinking = not args.no_thinking

    if args.batch:
        demo_nums = [int(x.strip()) for x in args.demos.split(",")]
        configs = []

        if args.mode in ("multi", "both"):
            configs.append({
                "name": f"multi-c={args.coordinator}_t={args.tactic}_cr={args.critic}",
                "mode": "multi",
                "coordinator_provider": args.coordinator,
                "coordinator_thinking": thinking,
                "tactic_provider": args.tactic,
                "tactic_thinking": thinking,
                "critic_provider": args.critic,
                "critic_thinking": False,  # critic uses fast model
            })
        if args.mode in ("single", "both"):
            configs.append({
                "name": f"single={args.tactic}_{'thinkON' if thinking else 'thinkOFF'}",
                "mode": "single",
                "provider": args.tactic,
                "thinking": thinking,
            })

        run_batch(demos=demo_nums, configs=configs, max_iterations=args.max_iterations)
        return

    # Single demo run
    trace = TraceLogger()

    if args.mode == "multi":
        prover = MultiAgentOrchestrator(
            trace=trace,
            coordinator_provider=args.coordinator,
            coordinator_thinking=thinking,
            tactic_provider=args.tactic,
            tactic_thinking=thinking,
            critic_provider=args.critic,
            critic_thinking=False,
        )
    elif args.mode == "single":
        prover = SingleAgentProver(trace=trace, provider=args.tactic, thinking=thinking)
    else:  # both
        print("\n>>> Running MULTI-AGENT first...")
        multi_prover = MultiAgentOrchestrator(
            trace=trace,
            coordinator_provider=args.coordinator,
            coordinator_thinking=thinking,
            tactic_provider=args.tactic,
            tactic_thinking=thinking,
            critic_provider=args.critic,
            critic_thinking=False,
        )
        multi_result = multi_prover.prove(
            theorem=demo["theorem"], imports=demo.get("imports"),
            max_iterations=args.max_iterations,
        )

        print("\n>>> Running SINGLE-AGENT baseline...")
        trace2 = TraceLogger()
        single_prover = SingleAgentProver(trace=trace2, provider=args.tactic, thinking=thinking)
        single_result = single_prover.prove(
            theorem=demo["theorem"], imports=demo.get("imports"),
            max_iterations=args.max_iterations,
        )

        print(f"\n{'='*60}")
        print("COMPARISON")
        print(f"{'='*60}")
        print(f"  Multi:  {'OK' if multi_result['success'] else 'FAIL'} "
              f"({multi_result['iterations']} iter, {multi_result['total_s']}s)")
        print(f"  Single: {'OK' if single_result['success'] else 'FAIL'} "
              f"({single_result['iterations']} iter, {single_result['total_s']}s)")
        trace.save(f"comparison_{demo['name']}")
        return

    result = prover.prove(
        theorem=demo["theorem"], imports=demo.get("imports"),
        max_iterations=args.max_iterations,
    )
    trace.save(f"{args.mode}_{demo['name']}")

    print(f"\n{'='*60}")
    print(f"RESULT: {'SUCCESS' if result['success'] else 'FAILED'}")
    if result["success"]:
        print(f"  Proof: {result['proof']}")
        print(f"  Iterations: {result['iterations']}")
        print(f"  Time: {result['total_s']}s (LLM: {result.get('llm_s', 0):.1f}s, Lean: {result['lean_s']}s)")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()
