#!/usr/bin/env python3
"""Run baseline comparisons for Issue #833 P1.

Usage:
    python run_baselines.py --demo 9 --mode multi --iterations 5
    python run_baselines.py --demo 9 --mode autonomous --iterations 5
    python run_baselines.py --all
"""
import argparse
import asyncio
import json
import sys
import time
from pathlib import Path

sys.stdout.reconfigure(line_buffering=True)
sys.stderr.reconfigure(line_buffering=True)

# Add agent_tests/ to path so `from prover import ...` works
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))

from prover import DEMOS, TraceLogger
from prover.provers import MultiAgentSorryProver, AutonomousProver
from prover.config import create_client


BASELINES_DIR = Path(__file__).parent
TRACES_DIR = BASELINES_DIR / "traces"
TRACES_DIR.mkdir(exist_ok=True)


def run_multi_baseline(demo_num: int, max_iterations: int = 5,
                       provider: str = "zai") -> dict:
    demo = DEMOS[demo_num]
    filepath = demo["file"]
    original = Path(filepath).read_text(encoding="utf-8")
    original_sorry = original.count("sorry")

    trace = TraceLogger(output_dir=str(TRACES_DIR))
    prover = MultiAgentSorryProver(trace=trace, provider=provider)

    start = time.time()
    result = asyncio.run(prover.prove_sorry(demo=demo, max_iterations=max_iterations))
    elapsed = time.time() - start

    # Verify file was restored
    final = Path(filepath).read_text(encoding="utf-8")
    final_sorry = final.count("sorry")
    file_ok = final == original or final_sorry < original_sorry

    trace.save(f"multi_demo{demo_num}")

    baseline = {
        "demo": demo_num,
        "name": demo["name"],
        "mode": "multi",
        "provider": provider,
        "iterations": max_iterations,
        "original_sorry": original_sorry,
        "final_sorry": final_sorry,
        "sorry_eliminated": original_sorry - final_sorry,
        "file_restored": file_ok,
        "total_s": round(elapsed, 1),
        "success": result.get("success", False),
        "attempts": result.get("attempts", 0),
    }

    print(f"\n{'='*60}")
    print(f"BASELINE: multi / {demo['name']} / {provider}")
    print(f"  Sorry: {original_sorry} -> {final_sorry} (eliminated: {baseline['sorry_eliminated']})")
    print(f"  File OK: {file_ok}")
    print(f"  Time: {elapsed:.1f}s")
    print(f"{'='*60}")

    return baseline


def run_auto_baseline(demo_num: int, max_iterations: int = 5,
                      provider: str = "zai") -> dict:
    demo = DEMOS[demo_num]
    filepath = demo["file"]
    original = Path(filepath).read_text(encoding="utf-8")
    original_sorry = original.count("sorry")

    trace = TraceLogger(output_dir=str(TRACES_DIR))
    prover = AutonomousProver(trace=trace, provider=provider)

    start = time.time()
    result = prover.prove_sorry(demo=demo, max_iterations=max_iterations)
    elapsed = time.time() - start

    final = Path(filepath).read_text(encoding="utf-8")
    final_sorry = final.count("sorry")
    file_ok = final == original or final_sorry < original_sorry

    trace.save(f"auto_demo{demo_num}")

    baseline = {
        "demo": demo_num,
        "name": demo["name"],
        "mode": "autonomous",
        "provider": provider,
        "iterations": max_iterations,
        "original_sorry": original_sorry,
        "final_sorry": final_sorry,
        "sorry_eliminated": original_sorry - final_sorry,
        "file_restored": file_ok,
        "total_s": round(elapsed, 1),
        "success": result.get("success", False),
        "attempts": result.get("attempts", 0),
    }

    print(f"\n{'='*60}")
    print(f"BASELINE: autonomous / {demo['name']} / {provider}")
    print(f"  Sorry: {original_sorry} -> {final_sorry} (eliminated: {baseline['sorry_eliminated']})")
    print(f"  File OK: {file_ok}")
    print(f"  Time: {elapsed:.1f}s")
    print(f"{'='*60}")

    return baseline


def main():
    parser = argparse.ArgumentParser(description="Run baseline comparisons")
    parser.add_argument("--demo", type=int, default=9)
    parser.add_argument("--mode", choices=["multi", "autonomous", "both"], default="both")
    parser.add_argument("--iterations", type=int, default=5)
    parser.add_argument("--provider", default="zai")
    parser.add_argument("--all", action="store_true",
                        help="Run all sorry demos (9, 13)")
    args = parser.parse_args()

    demos = [9, 13] if args.all else [args.demo]
    results = []

    for d in demos:
        if args.mode in ("multi", "both"):
            r = run_multi_baseline(d, args.iterations, args.provider)
            results.append(r)
        if args.mode in ("autonomous", "both"):
            r = run_auto_baseline(d, args.iterations, args.provider)
            results.append(r)

    # Save results table
    output = BASELINES_DIR / "baseline_results.json"
    output.write_text(json.dumps(results, indent=2, ensure_ascii=False))

    # Print summary table
    print(f"\n{'='*70}")
    print(f"{'Mode':<15} {'Demo':<25} {'Sorry':<15} {'Time':<10} {'File OK':<10}")
    print(f"{'-'*70}")
    for r in results:
        sorry_str = f"{r['original_sorry']}->{r['final_sorry']} ({r['sorry_eliminated']:+d})"
        print(f"{r['mode']:<15} {r['name']:<25} {sorry_str:<15} {r['total_s']:.0f}s{'':<5} {'OK' if r['file_restored'] else 'CORRUPTED'}")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
