#!/usr/bin/env python3
"""Multi-Agent Lean 4 Proof System -- Microsoft Agent Framework.

Thin CLI that delegates to the prover package.

Usage:
  # Demo theorems (1-5):
  python multi_agent_proof.py --demo 1 --mode autonomous --max-iterations 6

  # Sorry replacement in .lean files:
  python multi_agent_proof.py --lean path/to/File.lean --sorry-line 513 --max-iterations 10

  # Batch:
  python multi_agent_proof.py --batch --demos 1,2,3

  # Multi-agent workflow (4 specialized agents):
  python multi_agent_proof.py --demo 6 --mode multi --max-iterations 10
"""

import argparse
import asyncio
import json
import sys
from pathlib import Path

sys.stdout.reconfigure(line_buffering=True)
sys.stderr.reconfigure(line_buffering=True)

from prover import (
    MultiAgentSorryProver,
    AutonomousProver,
    DEMOS,
    PROVIDERS,
    TraceLogger,
)
from prover.config import LEAN_PROJECT_DIR
from prover.verifier import verify_with_lean
from prover.trace import TraceLogger as _TL


def main():
    parser = argparse.ArgumentParser(
        description="Multi-Agent Lean 4 Proof System (Microsoft Agent Framework)"
    )
    parser.add_argument("--demo", type=int, default=1,
                        help="Demo number (1-9)")
    parser.add_argument("--batch", action="store_true",
                        help="Run batch over demos")
    parser.add_argument("--demos", type=str, default="1,2,3",
                        help="Comma-separated demo numbers for batch")
    parser.add_argument("--max-iterations", type=int, default=6,
                        help="Max proof iterations")
    parser.add_argument("--mode", choices=["multi", "autonomous"], default="autonomous",
                        help="Agent mode: multi (4-agent workflow) or autonomous (single agent)")
    parser.add_argument("--provider", default="zai",
                        help="LLM provider (zai or local)")
    parser.add_argument("--verify-only", action="store_true",
                        help="Just verify known proof (demos 1-5 only)")
    parser.add_argument("--verbose", action="store_true")

    # Direct .lean file mode
    parser.add_argument("--lean", type=str, default=None,
                        help="Path to .lean file (bypasses demos)")
    parser.add_argument("--sorry-line", type=int, default=0,
                        help="Line number of sorry to target (0 = auto-detect)")
    parser.add_argument("--hints", type=str, default="",
                        help="Strategic hints for the prover")

    args = parser.parse_args()

    # ── Direct .lean file mode ──
    if args.lean:
        lean_path = Path(args.lean)
        if not lean_path.exists():
            print(f"File not found: {lean_path}")
            sys.exit(1)

        content = lean_path.read_text(encoding="utf-8")
        sorry_count = content.count("sorry")
        if sorry_count == 0:
            print(f"No sorry found in {lean_path}")
            sys.exit(0)

        sorry_line = args.sorry_line
        if sorry_line == 0:
            for i, line in enumerate(content.split("\n"), 1):
                if "sorry" in line:
                    sorry_line = i
                    break

        demo = {
            "name": lean_path.stem,
            "file": str(lean_path),
            "line": sorry_line,
            "theorem": lean_path.stem,
            "description": f"Proof on {lean_path.name}, {sorry_count} sorry, targeting line {sorry_line}",
        }

        trace = TraceLogger()

        if args.mode == "multi":
            prover = MultiAgentSorryProver(
                trace=trace, provider=args.provider,
            )
            result = asyncio.run(prover.prove_sorry(
                demo=demo, max_iterations=args.max_iterations,
            ))
        else:
            prover = AutonomousProver(
                trace=trace, provider=args.provider,
            )
            result = prover.prove_sorry(
                demo=demo, max_iterations=args.max_iterations,
                strategic_hints=args.hints,
            )

        trace.save(f"auto_{demo['name']}")
        return

    # ── Demo mode ──
    demo = DEMOS.get(args.demo)
    if not demo:
        print(f"Unknown demo {args.demo}. Available: {list(DEMOS.keys())}")
        sys.exit(1)

    is_sorry_mode = demo.get("sorry_type") is not None

    # Verify-only for standard demos
    if args.verify_only and not is_sorry_mode:
        trace = TraceLogger()
        result = verify_with_lean(
            theorem=demo["theorem"], tactic=demo["proof"],
            imports=demo.get("imports"), project_dir=LEAN_PROJECT_DIR, trace=trace,
        )
        print(f"Known proof '{demo['proof']}': "
              f"{'VALID' if result['success'] else 'INVALID'} "
              f"({result['time_s']:.1f}s via {result.get('backend', '?')})")
        if result["errors"]:
            print(f"Errors: {result['errors'][:300]}")
        return

    # Batch mode
    if args.batch:
        demo_nums = [int(x.strip()) for x in args.demos.split(",")]
        _run_batch(demo_nums, provider=args.provider, max_iterations=args.max_iterations)
        return

    # ── Single demo run ──
    trace = TraceLogger()

    if args.mode == "multi" and is_sorry_mode:
        prover = MultiAgentSorryProver(
            trace=trace, provider=args.provider,
        )
        result = asyncio.run(prover.prove_sorry(
            demo=demo, max_iterations=args.max_iterations,
        ))
    else:
        prover = AutonomousProver(
            trace=trace, provider=args.provider,
        )
        if is_sorry_mode:
            result = prover.prove_sorry(
                demo=demo, max_iterations=args.max_iterations,
                strategic_hints=args.hints,
            )
        else:
            # For standard demos, create synthetic sorry-mode demo
            print(f"\n>>> PROVING: {demo['name']} ({demo.get('difficulty', '?')})...")
            # Use verify_with_lean for standard theorem demos
            result = verify_with_lean(
                theorem=demo["theorem"],
                tactic=demo["proof"],
                imports=demo.get("imports"),
                project_dir=LEAN_PROJECT_DIR,
                trace=trace,
            )
            print(f"\n{'='*60}")
            print(f"RESULT: {'VALID' if result['success'] else 'INVALID'}")
            print(f"  Tactic: {demo['proof']}")
            print(f"  Time: {result['time_s']:.1f}s")
            print(f"{'='*60}")
            trace.save(f"demo_{demo['name']}")
            return

    trace.save(f"{'multi' if args.mode == 'multi' else 'auto'}_{demo['name']}")

    print(f"\n{'='*60}")
    print(f"RESULT: {'SUCCESS' if result['success'] else 'FAILED'}")
    if result.get("proof"):
        print(f"  Proof: {result['proof'][:200]}")
    print(f"  Time: {result['total_s']:.1f}s, Iterations: {result['iterations']}")
    if result.get("sorry_evolution"):
        print(f"  Sorry evolution: {result['sorry_evolution']}")
    print(f"{'='*60}")


def _run_batch(demo_nums: list, provider: str = "zai", max_iterations: int = 3):
    """Run batch over demos."""
    results = []
    for demo_num in demo_nums:
        demo = DEMOS.get(demo_num)
        if not demo:
            continue

        label = f"{demo['name']} | {provider}"
        print(f"\n{'#'*70}")
        print(f"# BATCH: {label}")
        print(f"{'#'*70}")

        trace = TraceLogger()
        t0 = __import__("time").time()

        try:
            prover = AutonomousProver(trace=trace, provider=provider)

            if demo.get("sorry_type"):
                result = prover.prove_sorry(demo=demo, max_iterations=max_iterations)
            else:
                result = verify_with_lean(
                    theorem=demo["theorem"], tactic=demo["proof"],
                    imports=demo.get("imports"), project_dir=LEAN_PROJECT_DIR, trace=trace,
                )
                result = {"success": result["success"], "iterations": 1,
                          "total_s": result["time_s"], "proof": demo["proof"]}

            trace.save(f"batch_{demo['name']}")
            total_s = __import__("time").time() - t0
            results.append({
                "demo": demo_num, "demo_name": demo["name"],
                "success": result["success"], "iterations": result.get("iterations", 0),
                "total_s": round(total_s, 1),
            })

        except Exception as e:
            print(f"  ERROR: {e}")
            results.append({
                "demo": demo_num, "demo_name": demo["name"],
                "success": False, "iterations": 0, "total_s": 0,
            })

    # Summary
    print(f"\n{'='*70}")
    print("BATCH SUMMARY")
    print(f"{'='*70}")
    print(f"{'Demo':<30} {'OK?':<6} {'Iter':<6} {'Time':>7}")
    print("-" * 55)
    for r in results:
        print(f"{r['demo_name']:<30} {'OK' if r['success'] else 'FAIL':<6} "
              f"{r['iterations']:<6} {r['total_s']:>6.1f}s")

    return results


if __name__ == "__main__":
    main()
