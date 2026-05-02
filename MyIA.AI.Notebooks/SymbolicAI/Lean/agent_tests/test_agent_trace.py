"""
Standalone test script for Lean multi-agent proof system.
Runs outside the notebook for quick iteration with full trace logging.

Usage:
    cd MyIA.AI.Notebooks/SymbolicAI/Lean
    python test_agent_trace.py [--demo 1] [--no-thinking] [--verbose]

Models tested:
    - z.ai GLM-5.1 (reasoning) / GLM-4.7 (fast)
    - Local Qwen 3.6-35B-A3B
    - OpenRouter fallback
"""

import os
import sys
import json
import time
import argparse
from pathlib import Path
from datetime import datetime
from typing import Optional, Dict, Any

# Load .env from parent directory
from dotenv import load_dotenv
_parent = Path(__file__).resolve().parent.parent
load_dotenv(_parent / ".env")
# Add parent to sys.path so lean_runner is importable
if str(_parent) not in sys.path:
    sys.path.insert(0, str(_parent))

# ── Configuration ──────────────────────────────────────────────────────────────

LEAN_PROJECT_DIR = os.getenv("LEAN_PROJECT_DIR")

# Model endpoints
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
    "openrouter": {
        "base_url": os.getenv("OPENROUTER_BASE_URL", "https://openrouter.ai/api/v1"),
        "api_key": os.getenv("OPENROUTER_API_KEY", ""),
        "models": {
            "reasoning": os.getenv("OPENAI_CHAT_MODEL_ID", "gpt-5.5"),
            "fast": os.getenv("OPENAI_CHAT_MODEL_ID", "gpt-5.5"),
        }
    },
}

# Default Shapley imports for Lake-aware verification
SHAPLEY_IMPORTS = """import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
"""

# ── Trace Logger ───────────────────────────────────────────────────────────────

class TraceLogger:
    """Captures full agent conversation traces for debugging."""

    def __init__(self, output_dir: str = "traces"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.entries = []
        self.session_start = time.time()

    def log(self, agent: str, role: str, content: str, duration_s: float = 0,
            tool_name: str = None, tool_args: dict = None, tool_result: str = None,
            model: str = None, tokens: dict = None):
        entry = {
            "timestamp": time.time() - self.session_start,
            "agent": agent,
            "role": role,
            "content": content,  # full content for trace analysis
            "duration_s": round(duration_s, 3),
        }
        if tool_name:
            entry["tool_call"] = tool_name
            entry["tool_args"] = tool_args
            entry["tool_result"] = tool_result[:500] if tool_result else None
        if model:
            entry["model"] = model
        if tokens:
            entry["tokens"] = tokens
        self.entries.append(entry)

        # Console output
        ts = f"[+{entry['timestamp']:.1f}s]"
        if tool_name:
            print(f"  {ts} {agent} → {tool_name}({json.dumps(tool_args or {})[:80]}) → {duration_s:.2f}s")
        else:
            preview = (content or "")[:120].replace("\n", " ")
            print(f"  {ts} {agent} [{role}]: {preview}...")

    def save(self, name: str = None):
        if not name:
            name = f"trace_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        path = self.output_dir / f"{name}.json"
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.entries, f, indent=2, ensure_ascii=False)
        print(f"\nTrace saved: {path} ({len(self.entries)} entries)")
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


# ── Lean Runner Wrapper ────────────────────────────────────────────────────────

def run_lean(code: str, project_dir: str = None, timeout: int = 300) -> dict:
    """Run Lean code via lean_runner.LeanRunner."""
    from lean_runner import LeanRunner
    runner = LeanRunner(backend="auto", timeout=timeout)
    result = runner.run(code, project_dir=project_dir)
    return {
        "success": result.success,
        "output": result.output,
        "errors": result.errors,
        "exit_code": result.exit_code,
        "backend": result.backend,
    }


def verify_proof(theorem: str, proof: str, imports: str = None,
                 project_dir: str = None, trace: TraceLogger = None) -> dict:
    """Verify a Lean proof with full trace logging."""
    if imports:
        code = f"{imports}\n{theorem} := by {proof}"
    else:
        code = f"{theorem} := by {proof}"

    start = time.time()
    result = run_lean(code, project_dir=project_dir)
    duration = time.time() - start

    if trace:
        trace.log(
            agent="LeanVerifier",
            role="verification",
            content=f"{theorem} := by {proof}",
            duration_s=duration,
            tool_name="verify_proof",
            tool_args={"theorem": theorem[:80], "proof": proof[:80]},
            tool_result=f"success={result['success']}, errors={result.get('errors', '')[:200]}",
        )

    return result


# ── LLM Client ─────────────────────────────────────────────────────────────────

class LLMClient:
    """Unified LLM client supporting z.ai, local, and OpenRouter."""

    def __init__(self, provider: str = "zai", thinking: bool = True, trace: TraceLogger = None):
        self.provider = provider
        self.thinking = thinking
        self.trace = trace
        cfg = PROVIDERS.get(provider, PROVIDERS["zai"])

        from openai import OpenAI
        self.client = OpenAI(
            api_key=cfg["api_key"],
            base_url=cfg["base_url"],
        )
        self.base_url = cfg["base_url"]
        self.model_reasoning = cfg["models"]["reasoning"]
        self.model_fast = cfg["models"]["fast"]

    def chat(self, messages: list, model: str = None, agent_name: str = "LLM",
             max_tokens: int = 4096, temperature: float = 0.3) -> str:
        model_id = model or self.model_reasoning
        start = time.time()

        kwargs = {
            "model": model_id,
            "messages": messages,
            "max_tokens": max_tokens,
            "temperature": temperature,
        }

        # For reasoning models, use higher max_tokens to accommodate thinking
        if "glm-5" in model_id or "glm-4.7" in model_id:
            kwargs["max_tokens"] = max(max_tokens, 4096)

        try:
            response = self.client.chat.completions.create(**kwargs)
            duration = time.time() - start
            msg = response.choices[0].message
            content = msg.content or ""
            reasoning = getattr(msg, "reasoning_content", None) or getattr(msg, "reasoning", None) or ""
            # Some models put everything in reasoning with empty content — extract tactic
            if not content.strip() and reasoning.strip():
                import re
                # Try to extract from code fences first
                m = re.search(r'```\w*\n(.*?)```', reasoning, re.DOTALL)
                if m:
                    content = m.group(1).strip()
                else:
                    # Take last non-empty line as tactic (often the final answer)
                    lines = [l.strip() for l in reasoning.strip().split('\n') if l.strip()]
                    if lines:
                        content = lines[-1]
            tokens = {
                "prompt": response.usage.prompt_tokens if response.usage else 0,
                "completion": response.usage.completion_tokens if response.usage else 0,
                "total": response.usage.total_tokens if response.usage else 0,
            }

            if self.trace:
                self.trace.log(
                    agent=agent_name,
                    role="assistant",
                    content=content,
                    duration_s=duration,
                    model=model_id,
                    tokens=tokens,
                )
                if reasoning:
                    self.trace.log(
                        agent=agent_name,
                        role="thinking",
                        content=reasoning,  # full thinking trace for analysis
                        duration_s=0,
                        model=model_id,
                    )

            return content

        except Exception as e:
            duration = time.time() - start
            if self.trace:
                self.trace.log(agent=agent_name, role="error", content=str(e), duration_s=duration)
            return f"ERROR: {e}"


# ── Demo Theorems ──────────────────────────────────────────────────────────────

DEMOS = {
    1: {
        "name": "DEMO_1_REFLEXIVITY",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "proof": "rfl",
        "imports": None,
        "description": "Trivial - rfl suffit",
    },
    2: {
        "name": "DEMO_2_ZERO_ADD",
        "theorem": "theorem demo_zero_add (n : Nat) : 0 + n = n",
        "proof": "omega",
        "imports": None,
        "description": "Simple - omega or Nat.zero_add",
    },
    3: {
        "name": "DEMO_3_DISTRIBUTIVITY",
        "theorem": "theorem demo_dist (a b c : Nat) : a * c + b * c = (a + b) * c",
        "proof": "omega",
        "imports": None,
        "description": "Intermediate - distributivity reversed",
    },
    4: {
        "name": "DEMO_4_SHAPLEY_SIMPLE",
        "theorem": "theorem test_coef_shift (n s : Nat) (h : s + 2 <= n) : (s + 1) * 1 = s + 1",
        "proof": "omega",
        "imports": SHAPLEY_IMPORTS,
        "description": "Shapley-style Nat arithmetic with Mathlib",
    },
    5: {
        "name": "DEMO_5_FINSET_SUM_REAL",
        "theorem": "theorem demo_finset_sum_erase {α : Type*} [DecidableEq α] [Fintype α] (s : Finset α) (a : α) (f : α → Real) (ha : a ∈ s) : ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x - f a",
        "proof": "have h := Finset.sum_erase_add s f ha; linarith",
        "imports": SHAPLEY_IMPORTS,
        "description": "Finset sum with erase + Real subtraction (Shapley-style)",
    },
}


# ── Single Agent Test ──────────────────────────────────────────────────────────

def test_single_agent_tactic(
    theorem: str,
    agent_name: str = "TacticAgent",
    provider: str = "zai",
    thinking: bool = True,
    imports: str = None,
    max_attempts: int = 3,
):
    """
    Test: give a theorem to the LLM, ask for a tactic, verify with Lean.
    This is the inner loop of the multi-agent system.
    """
    trace = TraceLogger()
    llm = LLMClient(provider=provider, thinking=thinking, trace=trace)

    system_prompt = f"""You are a Lean 4 theorem proving agent. Given a theorem statement, provide the tactic proof.

The theorem already has `:= by` so provide ONLY the tactic sequence after `by`.

Rules:
- Reply with ONLY the tactic(s), no explanation, no markdown, no code fences
- DO NOT prefix with `by` — it is already present
- Chain tactics with `;` (e.g., "simp; omega") or use `<;>` for branching

Tactic priority for Nat goals:
1. omega — linear arithmetic (addition, subtraction, inequalities)
2. simp — simplification engine (knows Nat algebra)
3. rfl — ONLY for definitional equality (a = a), NOT for (0 + n = n) or computed values
4. exact <term> — provide a proof term directly (e.g., exact (Nat.add_mul a b c).symm)
5. rw [lemma] — rewrite with a lemma (no trailing rfl needed)

Tactic priority for Finset/BigOperator goals:
1. simp [Finset.sum_erase_add, Finset.sum_insert] — automates common sum identities
2. have h := Finset.sum_erase_add s f ha; linarith — introduce sum lemma then solve arithmetic
3. exact? — let Mathlib suggest the right lemma name
4. rw [Finset.sum_erase_add s f ha] — explicit rewrite (note: s and f are explicit args)

Common pitfalls:
- `rfl` fails on `0 + n = n`: Nat.add is defined by recursion, use omega or simp
- `ring` is NOT available unless Mathlib.Tactic is imported — use omega or simp instead
- `rw [add_mul]` rewrites LHS → may leave unsolved goals. Use `rw [Nat.add_mul]` or `simp [Nat.add_mul]`
- If omega fails on nonlinear goals (with *), try simp [Nat.mul_add, Nat.add_mul] or exact"""

    print(f"\n{'='*70}")
    print(f"TEST: {theorem}")
    print(f"Agent: {agent_name} | Provider: {provider} | Thinking: {thinking}")
    print(f"{'='*70}")

    # Conversation history for multi-turn retry with error feedback
    messages = [{"role": "system", "content": system_prompt}]

    for attempt in range(1, max_attempts + 1):
        print(f"\n--- Attempt {attempt}/{max_attempts} ---")

        # Build user message
        if attempt == 1:
            user_msg = f"Prove this Lean 4 theorem:\n{theorem}"
            if imports:
                user_msg += f"\n\nAvailable imports: Mathlib (Finset, Real, BigOperators, Tactic)"
        else:
            user_msg = (
                f"That tactic failed. Lean error:\n{last_error}\n\n"
                f"Try a DIFFERENT tactic to prove:\n{theorem}"
            )
        messages.append({"role": "user", "content": user_msg})

        response = llm.chat(
            messages=messages,
            model=llm.model_fast if not thinking else llm.model_reasoning,
            agent_name=agent_name,
        )
        messages.append({"role": "assistant", "content": response})

        tactic = response.strip()
        print(f"  Tactic proposed: {tactic[:100]}")

        # Verify with Lean
        result = verify_proof(
            theorem=theorem,
            proof=tactic,
            imports=imports,
            project_dir=LEAN_PROJECT_DIR,
            trace=trace,
        )

        if result["success"] and "error" not in (result.get("errors") or "").lower():
            print(f"  PROOF VALID!")
            trace.save(f"success_{theorem.split()[1] if len(theorem.split()) > 1 else 'test'}")
            return {"success": True, "tactic": tactic, "attempts": attempt, "trace": trace}
        else:
            last_error = (result.get("errors") or "unknown")[:300]
            print(f"  FAILED: {last_error[:200]}")

            if attempt < max_attempts:
                print(f"  Retrying with error context...")

    trace.save("failed")
    return {"success": False, "attempts": max_attempts, "trace": trace}


# ── Batch Test ──────────────────────────────────────────────────────────────────

def run_batch(demo_nums: list = None, providers: list = None, max_attempts: int = 3):
    """Run all provider x thinking combinations for given demos."""
    if demo_nums is None:
        demo_nums = [1, 2, 3]
    if providers is None:
        providers = ["zai", "local"]

    results = []
    for demo_num in demo_nums:
        demo = DEMOS.get(demo_num)
        if not demo:
            continue
        for provider in providers:
            for thinking in [False, True]:
                label = f"{demo['name']} | {provider} | thinking={'ON' if thinking else 'OFF'}"
                print(f"\n{'#'*70}")
                print(f"# BATCH: {label}")
                print(f"{'#'*70}")
                t0 = time.time()
                try:
                    result = test_single_agent_tactic(
                        theorem=demo["theorem"],
                        provider=provider,
                        thinking=thinking,
                        imports=demo.get("imports"),
                        max_attempts=max_attempts,
                    )
                    total_s = time.time() - t0
                    # Extract timing from trace
                    llm_time = sum(e["duration_s"] for e in result["trace"].entries
                                   if e["role"] in ("assistant", "thinking"))
                    lean_time = sum(e["duration_s"] for e in result["trace"].entries
                                    if e.get("tool_call") == "verify_proof")
                    thinking_trace = [e["content"] for e in result["trace"].entries
                                      if e["role"] == "thinking"]

                    # Save trace with unique name
                    trace_name = f"{demo['name']}_{provider}_{'thinkON' if thinking else 'thinkOFF'}"
                    result["trace"].save(trace_name)

                    results.append({
                        "demo": demo_num, "provider": provider,
                        "thinking": thinking, "success": result["success"],
                        "attempts": result["attempts"],
                        "tactic": result.get("tactic", ""),
                        "total_s": round(total_s, 1),
                        "llm_s": round(llm_time, 1),
                        "lean_s": round(lean_time, 1),
                        "thinking_trace": thinking_trace,
                        "trace_file": f"traces/{trace_name}.json",
                    })
                except Exception as e:
                    total_s = time.time() - t0
                    print(f"  ERROR: {e}")
                    results.append({
                        "demo": demo_num, "provider": provider,
                        "thinking": thinking, "success": False,
                        "attempts": 0, "tactic": f"ERROR: {e}",
                        "total_s": round(total_s, 1), "llm_s": 0, "lean_s": 0,
                        "thinking_trace": [], "trace_file": None,
                    })

    # Summary table
    print(f"\n{'='*90}")
    print("BATCH SUMMARY")
    print(f"{'='*90}")
    print(f"{'Demo':<28} {'Prov':<8} {'Think':<7} {'OK?':<5} {'Att':<4} "
          f"{'Total':>6} {'LLM':>5} {'Lean':>5} {'Tactic'}")
    print("-" * 100)
    for r in results:
        demo_name = DEMOS.get(r["demo"], {}).get("name", str(r["demo"]))
        print(f"{demo_name:<28} {r['provider']:<8} {'ON' if r['thinking'] else 'OFF':<7} "
              f"{'OK' if r['success'] else 'FAIL':<5} {r['attempts']:<4} "
              f"{r['total_s']:>5.1f}s {r['llm_s']:>4.1f}s {r['lean_s']:>4.1f}s "
              f"{r['tactic'][:30]}")

    # Save summary
    ts = datetime.now().strftime('%Y%m%d_%H%M%S')
    summary_path = Path("traces") / f"batch_summary_{ts}.json"
    summary_path.parent.mkdir(exist_ok=True)
    with open(summary_path, "w") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    print(f"\nBatch summary saved: {summary_path}")
    return results


# ── Main ───────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Lean agent trace tester")
    parser.add_argument("--demo", type=int, default=1, help="Demo number (1-4)")
    parser.add_argument("--provider", default="zai", choices=["zai", "local", "openrouter"])
    parser.add_argument("--no-thinking", action="store_true", help="Disable thinking (use fast model)")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--verify-only", action="store_true", help="Just verify the known proof, skip LLM")
    parser.add_argument("--max-attempts", type=int, default=3)
    parser.add_argument("--batch", action="store_true",
                        help="Run all providers x thinking modes for given demos")
    parser.add_argument("--demos", type=str, default="1,2,3",
                        help="Comma-separated demo numbers for batch (default: 1,2,3)")
    args = parser.parse_args()

    if args.batch:
        demo_nums = [int(x.strip()) for x in args.demos.split(",")]
        run_batch(demo_nums=demo_nums, max_attempts=args.max_attempts)
        return

    demo = DEMOS.get(args.demo)
    if not demo:
        print(f"Unknown demo {args.demo}. Available: {list(DEMOS.keys())}")
        sys.exit(1)

    print(f"\nDemo: {demo['name']} - {demo['description']}")
    print(f"Theorem: {demo['theorem']}")
    print(f"Project dir: {LEAN_PROJECT_DIR}")

    if args.verify_only:
        print("\n--- Verify-only mode ---")
        result = verify_proof(
            theorem=demo["theorem"],
            proof=demo["proof"],
            imports=demo.get("imports"),
            project_dir=LEAN_PROJECT_DIR,
        )
        print(f"Success: {result['success']}")
        if result.get("errors"):
            print(f"Errors: {result['errors'][:300]}")
        return

    thinking = not args.no_thinking
    result = test_single_agent_tactic(
        theorem=demo["theorem"],
        provider=args.provider,
        thinking=thinking,
        imports=demo.get("imports"),
        max_attempts=args.max_attempts,
    )

    print(f"\n{'='*70}")
    print(f"RESULT: {'SUCCESS' if result['success'] else 'FAILED'}")
    if result["success"]:
        print(f"  Tactic: {result['tactic']}")
        print(f"  Attempts: {result['attempts']}")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
