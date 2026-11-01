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
from prover.lean_utils import count_real_sorries  # #9402: real-token counter
from prover.baselines.calibration_stub import (  # #1453 / #13907
    calibration_stub,
    flag_false_green,
)


BASELINES_DIR = Path(__file__).parent
TRACES_DIR = BASELINES_DIR / "traces"
TRACES_DIR.mkdir(exist_ok=True)


def run_multi_baseline(demo_num: int, max_iterations: int = 5,
                       provider: str = "zai") -> dict:
    demo = DEMOS[demo_num]
    filepath = demo["file"]
    original = Path(filepath).read_text(encoding="utf-8")
    committed_sorry = count_real_sorries(original)

    trace = TraceLogger(output_dir=str(TRACES_DIR))
    prover = MultiAgentSorryProver(trace=trace, provider=provider)

    start = time.time()
    with calibration_stub(demo) as prepared:
        # Le point de depart est celui que le prouveur voit REELLEMENT : sur une
        # cible de calibration il vaut 1 (scaffolding stubbe), pas 0 (scaffolding
        # committe avec sa preuve approuvee). Mesurer avant le stub rendait
        # `sorry_eliminated` structurellement faux dans l'autre sens.
        original_sorry = count_real_sorries(Path(filepath).read_text(encoding="utf-8"))
        result = asyncio.run(prover.prove_sorry(demo=prepared, max_iterations=max_iterations))
        # L'etat final qui mesure le prouveur est celui qu'il LAISSE, lu a
        # l'interieur du bloc — AVANT la restauration du finally. Le lire apres
        # la sortie mesurait les octets committes (preuve approuvee restauree),
        # donc `sorry_eliminated = +1` constant sur les rangs de calibration,
        # que le prouveur ait travaille ou non (reserve Hermes #23990, 01/11).
        final_sorry = count_real_sorries(Path(filepath).read_text(encoding="utf-8"))
    elapsed = time.time() - start

    # La restauration se verifie SEULE, apres sortie : egalite stricte aux
    # octets committes sur une cible stubbee. L'ancienne disjonction
    # `final_sorry < original_sorry` pardonnait une restauration ratee des
    # que le prouveur avait laisse une preuve (garde unilaterale).
    restored = Path(filepath).read_text(encoding="utf-8")
    if bool(prepared.get("calibration_stubbed")):
        file_ok = restored == original
    else:
        file_ok = restored == original or final_sorry < original_sorry

    false_green = flag_false_green(prepared, result)

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
        "success": result.get("success", False) and not false_green,
        "attempts": result.get("attempts", 0),
        "committed_sorry": committed_sorry,
        "calibration_stubbed": bool(prepared.get("calibration_stubbed")),
        "false_green": false_green,
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
    committed_sorry = count_real_sorries(original)

    trace = TraceLogger(output_dir=str(TRACES_DIR))
    prover = AutonomousProver(trace=trace, provider=provider)

    start = time.time()
    with calibration_stub(demo) as prepared:
        original_sorry = count_real_sorries(Path(filepath).read_text(encoding="utf-8"))
        result = prover.prove_sorry(demo=prepared, max_iterations=max_iterations)
        # Meme regle que le mode multi (reserve Hermes #23990) : l'etat final
        # se lit AVANT la restauration, sinon `sorry_eliminated` est constant.
        final_sorry = count_real_sorries(Path(filepath).read_text(encoding="utf-8"))
    elapsed = time.time() - start

    restored = Path(filepath).read_text(encoding="utf-8")
    if bool(prepared.get("calibration_stubbed")):
        file_ok = restored == original
    else:
        file_ok = restored == original or final_sorry < original_sorry

    false_green = flag_false_green(prepared, result)

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
        "success": result.get("success", False) and not false_green,
        "attempts": result.get("attempts", 0),
        "committed_sorry": committed_sorry,
        "calibration_stubbed": bool(prepared.get("calibration_stubbed")),
        "false_green": false_green,
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
    parser.add_argument("--provider", default="openrouter")
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
        health = "CORRUPTED" if not r["file_restored"] else ("FALSE GREEN" if r.get("false_green") else "OK")
        print(f"{r['mode']:<15} {r['name']:<25} {sorry_str:<15} {r['total_s']:.0f}s{'':<5} {health}")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
