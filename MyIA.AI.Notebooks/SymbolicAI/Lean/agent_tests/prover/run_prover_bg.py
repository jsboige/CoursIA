#!/usr/bin/env python3
"""Launch the multi-agent prover on a specific sorry target.

Usage:
    python run_prover_bg.py --demo 9 --mode multi --iterations 10
    python run_prover_bg.py --file path/to.lean --line 563 --mode autonomous --iterations 8

Supports both demo-based (from prover/__init__.py DEMOS) and direct file/line targeting.
"""
import argparse
import asyncio
import json
import sys
import time
from pathlib import Path

sys.stdout.reconfigure(line_buffering=True)
sys.stderr.reconfigure(line_buffering=True)

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from prover import DEMOS, PROVED_DEMOS, TraceLogger
from prover.provers import MultiAgentSorryProver, AutonomousProver
from prover.config import create_client

TRACES_DIR = Path(__file__).parent / "traces"
TRACES_DIR.mkdir(exist_ok=True)


def run_prover(demo_num: int = None, filepath: str = None, line: int = None,
               mode: str = "multi", iterations: int = 8,
               provider: str = "zai", local_provider: str = "local",
               goal: str = "", director_provider: str = None,
               coordinator_provider: str = None,
               tactic_provider: str = None,
               use_diagnosis_agent: bool = False,
               concurrent_search_count: int = 0):
    """Run the prover on a target."""
    if demo_num is not None:
        if demo_num not in DEMOS:
            print(f"Demo {demo_num} not found. Available: {sorted(DEMOS.keys())}")
            sys.exit(1)
        if demo_num in PROVED_DEMOS:
            print(f"Demo {demo_num} ({DEMOS[demo_num]['name']}) is PROVED — skipping.")
            sys.exit(0)
        demo = DEMOS[demo_num]
        filepath = demo["file"]
        line = demo.get("line")
        name = demo["name"]
    elif filepath:
        demo = {"file": filepath, "name": f"custom_{Path(filepath).stem}_L{line}",
                "line": line, "goal": goal}
        name = demo["name"]
    else:
        print("Must specify --demo or --file/--line")
        sys.exit(1)

    original = Path(filepath).read_text(encoding="utf-8")
    original_sorry = original.count("sorry")
    print(f"Target: {name}")
    print(f"  File: {filepath} (line {line})")
    print(f"  Mode: {mode}, Iterations: {iterations}")
    print(f"  Provider: {provider}, Local: {local_provider}, Tactic: {tactic_provider or 'openrouter (default)'}, Coordinator: {coordinator_provider or 'openrouter (default)'}")
    print(f"  Initial sorry count: {original_sorry}")
    print()

    trace = TraceLogger(output_dir=str(TRACES_DIR))

    if mode == "multi":
        prover = MultiAgentSorryProver(
            trace=trace, provider=provider, local_provider=local_provider,
            director_provider=director_provider,
            coordinator_provider=coordinator_provider,
            tactic_provider=tactic_provider)
        if director_provider:
            print(f"  Director: ENABLED (provider={director_provider})")
    else:
        prover = AutonomousProver(trace=trace, provider=provider)

    start = time.time()
    try:
        if mode == "multi":
            result = asyncio.run(
                prover.prove_sorry(demo=demo, max_iterations=iterations,
                                   use_diagnosis_agent=use_diagnosis_agent,
                                   concurrent_search_count=concurrent_search_count)
            )
        else:
            result = prover.prove_sorry(demo=demo, max_iterations=iterations)
    except Exception as e:
        print(f"\nProver crashed: {e}")
        result = {"error": str(e)}
    elapsed = time.time() - start

    final = Path(filepath).read_text(encoding="utf-8")
    final_sorry = final.count("sorry")

    trace_name = f"{mode}_{name.replace(' ', '_')}_{provider}"
    trace_path = trace.save(trace_name)

    print(f"\n{'='*60}")
    print(f"RESULT: {result.get('status', 'unknown')}")
    print(f"  Sorry: {original_sorry} → {final_sorry}")
    print(f"  Time: {elapsed:.1f}s")
    print(f"  Trace: {trace_path}")
    print(f"{'='*60}")

    # Save result summary
    summary = {
        "name": name,
        "mode": mode,
        "provider": provider,
        "coordinator_provider": coordinator_provider or "openrouter (default)",
        "iterations": iterations,
        "original_sorry": original_sorry,
        "final_sorry": final_sorry,
        "sorry_delta": final_sorry - original_sorry,
        "elapsed_s": round(elapsed, 1),
        "result": result,
        "trace_file": trace_path,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
    }
    summary_path = TRACES_DIR / f"{trace_name}_result.json"
    summary_path.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False, default=str),
        encoding="utf-8",
    )
    print(f"Summary: {summary_path}")

    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run Lean prover on a target")
    parser.add_argument("--demo", type=int, help="Demo number from DEMOS dict")
    parser.add_argument("--file", help="Target .lean file path")
    parser.add_argument("--line", type=int, help="Sorry line number")
    parser.add_argument("--goal", default="", help="Goal state override for KB matching")
    parser.add_argument("--mode", default="multi", choices=["multi", "autonomous"])
    parser.add_argument("--iterations", type=int, default=8)
    parser.add_argument("--provider", default="openrouter",
                        help="Provider for AutonomousProver auto-mode agent "
                             "(default: openrouter). #1459: GLM-5.1 (zai) causes "
                             "87.8%% rate-limit errors; GPT-5.5 via openrouter "
                             "eliminates the cascade. Use 'zai' for fallback.")
    parser.add_argument("--local-provider", default="local")
    parser.add_argument("--director-provider", default=None,
                        help="Provider for the frontier DirectorAgent "
                             "(e.g. 'openrouter'). Omit to disable the "
                             "Director lane. Only used in --mode multi.")
    parser.add_argument("--coordinator-provider", default=None,
                        help="Provider for CoordinatorAgent (default: openrouter). "
                             "#1289: GLM-5.1 (zai) times out on complex Lean contexts; "
                             "GPT-5.5 via openrouter is 6x faster. "
                             "Only used in --mode multi.")
    parser.add_argument("--tactic-provider", default=None,
                        help="Provider for TacticAgent (default: openrouter). "
                             "#1289: GLM-5.1 (zai) times out at 1680s on complex "
                             "Lean tactic generation; GPT-5.5 via openrouter "
                             "expected ~60-120s. Only used in --mode multi.")
    parser.add_argument("--use-diagnosis-agent", action="store_true",
                        help="Enable DiagnosisAgent (LLM-powered qualitative "
                             "verification replacing mechanical VerifyExecutor). "
                             "Only used in --mode multi.")
    parser.add_argument("--concurrent-search", type=int, default=0,
                        help="Number of ADDITIONAL SearchAgents to run in "
                             "parallel (B.7). 0 = single search (default). "
                             "E.g. --concurrent-search 2 = 3 total search agents. "
                             "Only used in --mode multi.")
    args = parser.parse_args()

    run_prover(
        demo_num=args.demo,
        filepath=args.file,
        line=args.line,
        mode=args.mode,
        iterations=args.iterations,
        provider=args.provider,
        local_provider=args.local_provider,
        goal=args.goal,
        director_provider=args.director_provider,
        coordinator_provider=args.coordinator_provider,
        tactic_provider=args.tactic_provider,
        use_diagnosis_agent=args.use_diagnosis_agent,
        concurrent_search_count=args.concurrent_search,
    )
