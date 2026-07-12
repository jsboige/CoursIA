"""
CPU diagnostic: compare RRN model configs on PE96 + synthetic puzzles.

Benchmarks h192_s16 vs h256_s24 vs h256_s16 models on:
  1. Project Euler 96 (51 hard puzzles, 17-24 givens)
  2. 1000 synthetic puzzles (mixed difficulty)

Outputs: JSON report + console summary.

Usage:
    python scripts/sudoku/cpu_diagnostic.py [--output-dir sudoku_models/diagnostics]
"""

import sys
import os
import time
import json
import argparse
import numpy as np

import torch
import torch.nn as nn

sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
from core.models import SudokuRRN, count_params
from core.evaluate import evaluate
from core.graph import build_sudoku_edge_index
from core.generation import generate_puzzles
from core.solvers import solve_sudoku

MODELS = {
    "h192_s16_finetune": {
        "path": "sudoku_models/finetuned_h192_s16_strat_v2_best.pt",
        "hidden_dim": 192,
        "msg_dim": 192,
        "n_steps": 16,
        "dropout": 0.1,
        "label": "h192_s16 finetune (83.5% hard)",
    },
    "h256_s16_finetune": {
        "path": "sudoku_models/finetuned_h256_s16_strat_v2_best.pt",
        "hidden_dim": 256,
        "msg_dim": 256,
        "n_steps": 16,
        "dropout": 0.1,
        "label": "h256_s16 finetune (83.5% hard)",
    },
    "h256_s24_track_a": {
        "path": "sudoku_models/track_a_h256_s24/best_model.pt",
        "hidden_dim": 256,
        "msg_dim": 256,
        "n_steps": 24,
        "dropout": 0.1,
        "label": "h256_s24 Track A (easy-overfit)",
    },
    "sweep_h192_s16": {
        "path": "sudoku_models/sweep_h192_s16_best.pt",
        "hidden_dim": 192,
        "msg_dim": 192,
        "n_steps": 16,
        "dropout": 0.1,
        "label": "h192_s16 sweep baseline",
    },
}


def load_model(cfg, device):
    model = SudokuRRN(
        hidden_dim=cfg["hidden_dim"],
        msg_dim=cfg["msg_dim"],
        n_steps=cfg["n_steps"],
        dropout=cfg["dropout"],
    )
    state = torch.load(cfg["path"], map_location=device, weights_only=True)
    # Checkpoints may be dicts with 'model_state_dict' key
    if isinstance(state, dict) and "model_state_dict" in state:
        state = state["model_state_dict"]
    model.load_state_dict(state)
    model.to(device)
    model.eval()
    return model


def get_pe96_puzzles():
    """Project Euler 96: 51 hard Sudoku grids (17-24 givens).

    These are classic minimal-clue puzzles. We generate a representative
    set of 51 hard puzzles since the PE96 file is not in the repo.
    Uses the Norvig solver to verify each puzzle is solvable.
    """
    rng = np.random.RandomState(96)
    puzzles = []
    solutions = []
    attempts = 0
    while len(puzzles) < 51 and attempts < 5000:
        attempts += 1
        grid_flat = np.zeros(81, dtype=np.int64)

        # Generate a complete grid via backtracking
        from core.generation import generate_complete_grid
        grid = generate_complete_grid(rng)
        solution = grid.flatten().copy()

        # Remove cells to get 17-24 givens (hard puzzles)
        n_givens = rng.randint(17, 25)
        mask = rng.choice(81, n_givens, replace=False)
        puzzle = solution.copy()
        remove_mask = np.ones(81, dtype=bool)
        remove_mask[mask] = False
        puzzle[remove_mask] = 0

        # Verify solvable
        verify = solve_sudoku(puzzle)
        if verify is not None and np.array_equal(verify, solution):
            puzzles.append(puzzle)
            solutions.append(solution)

    puzzles = np.array(puzzles, dtype=np.int64)
    solutions = np.array(solutions, dtype=np.int64)
    return puzzles, solutions


def get_synthetic_puzzles(n=1000, seed=42):
    """Generate n synthetic puzzles with mixed difficulty."""
    # Mix: 30% easy (30-35 givens), 40% medium (24-29), 30% hard (17-23)
    rng = np.random.RandomState(seed)
    n_easy = int(0.3 * n)
    n_med = int(0.4 * n)
    n_hard = n - n_easy - n_med

    easy_p, easy_s = generate_puzzles(n_easy, n_empty_range=(46, 51), seed=seed)
    med_p, med_s = generate_puzzles(n_med, n_empty_range=(52, 57), seed=seed + 1)
    hard_p, hard_s = generate_puzzles(n_hard, n_empty_range=(58, 64), seed=seed + 2)

    puzzles = np.concatenate([easy_p, med_p, hard_p])
    solutions = np.concatenate([easy_s, med_s, hard_s])

    # Shuffle
    idx = rng.permutation(len(puzzles))
    return puzzles[idx], solutions[idx]


def benchmark_model(model, puzzles, solutions, device, batch_size=16):
    """Run evaluation and return metrics + timing."""
    base_edges = build_sudoku_edge_index()
    n = len(puzzles)

    # Warmup
    warmup_p = puzzles[:batch_size]
    warmup_s = solutions[:batch_size]
    evaluate(model, warmup_p, warmup_s, base_edges, device, batch_size=batch_size)

    # Timed run
    t0 = time.time()
    cell_acc, grid_acc, avg_loss = evaluate(
        model, puzzles, solutions, base_edges, device, batch_size=batch_size
    )
    elapsed = time.time() - t0

    # Per-difficulty bucket analysis
    n_empty = (puzzles == 0).sum(axis=1)
    easy_mask = n_empty <= 46
    med_mask = (n_empty > 46) & (n_empty <= 57)
    hard_mask = n_empty > 57

    buckets = {}
    for name, mask in [("easy", easy_mask), ("medium", med_mask), ("hard", hard_mask)]:
        if mask.sum() > 0:
            c, g, l = evaluate(
                model, puzzles[mask], solutions[mask], base_edges, device, batch_size=batch_size
            )
            buckets[name] = {
                "n": int(mask.sum()),
                "cell_acc": round(c, 4),
                "grid_acc": round(g, 4),
                "avg_loss": round(l, 4),
            }

    return {
        "cell_acc": round(cell_acc, 4),
        "grid_acc": round(grid_acc, 4),
        "avg_loss": round(avg_loss, 4),
        "time_s": round(elapsed, 2),
        "puzzles_per_s": round(n / elapsed, 2),
        "n_puzzles": n,
        "buckets": buckets,
    }


def main():
    parser = argparse.ArgumentParser(description="Sudoku RRN CPU diagnostic")
    parser.add_argument("--output-dir", default="sudoku_models/diagnostics")
    parser.add_argument("--synth-n", type=int, default=1000)
    parser.add_argument("--batch-size", type=int, default=16)
    parser.add_argument("--pe96", action="store_true", default=True, help="Run PE96 benchmark")
    parser.add_argument("--no-pe96", action="store_true", help="Skip PE96 benchmark")
    parser.add_argument(
        "--models", nargs="*", default=None,
        help="Model keys to benchmark (default: all)"
    )
    args = parser.parse_args()

    device = torch.device("cpu")
    print(f"[INIT] Device: {device}")

    os.makedirs(args.output_dir, exist_ok=True)

    # Select models
    model_keys = args.models if args.models else list(MODELS.keys())
    models_to_run = {k: MODELS[k] for k in model_keys if k in MODELS}
    if not models_to_run:
        print(f"[ERROR] No valid models found. Available: {list(MODELS.keys())}")
        return

    # Generate test data
    run_pe96 = args.pe96 and not args.no_pe96
    pe96_puzzles, pe96_solutions = None, None
    synth_puzzles, synth_solutions = None, None

    if run_pe96:
        print("[DATA] Generating 51 PE96-style hard puzzles...")
        t0 = time.time()
        pe96_puzzles, pe96_solutions = get_pe96_puzzles()
        print(f"[DATA] Generated {len(pe96_puzzles)} PE96 puzzles in {time.time()-t0:.1f}s")

    print(f"[DATA] Generating {args.synth_n} synthetic puzzles...")
    t0 = time.time()
    synth_puzzles, synth_solutions = get_synthetic_puzzles(args.synth_n)
    print(f"[DATA] Generated in {time.time()-t0:.1f}s")

    # Run benchmarks
    all_results = {}

    for key, cfg in models_to_run.items():
        label = cfg["label"]
        path = cfg["path"]
        if not os.path.exists(path):
            print(f"[SKIP] {key}: checkpoint not found at {path}")
            continue

        print(f"\n{'='*60}")
        print(f"[MODEL] {key}: {label}")
        model = load_model(cfg, device)
        params = count_params(model)
        print(f"[MODEL] {params:,} params, device={device}")

        result = {"label": label, "params": params, "key": key}

        if run_pe96 and pe96_puzzles is not None:
            print(f"[PE96] Benchmarking on {len(pe96_puzzles)} hard puzzles...")
            pe96_res = benchmark_model(model, pe96_puzzles, pe96_solutions, device, args.batch_size)
            result["pe96"] = pe96_res
            print(f"  cell_acc={pe96_res['cell_acc']:.4f} grid_acc={pe96_res['grid_acc']:.4f} "
                  f"time={pe96_res['time_s']:.1f}s ({pe96_res['puzzles_per_s']:.1f}/s)")

        print(f"[SYNTH] Benchmarking on {len(synth_puzzles)} puzzles...")
        synth_res = benchmark_model(model, synth_puzzles, synth_solutions, device, args.batch_size)
        result["synth_1k"] = synth_res
        print(f"  cell_acc={synth_res['cell_acc']:.4f} grid_acc={synth_res['grid_acc']:.4f} "
              f"time={synth_res['time_s']:.1f}s ({synth_res['puzzles_per_s']:.1f}/s)")
        for bucket, bres in synth_res.get("buckets", {}).items():
            print(f"    {bucket} ({bres['n']}): cell={bres['cell_acc']:.4f} grid={bres['grid_acc']:.4f}")

        all_results[key] = result
        del model  # Free memory

    # Save report
    report = {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "device": str(device),
        "pe96_puzzles": len(pe96_puzzles) if pe96_puzzles is not None else 0,
        "synth_puzzles": args.synth_n,
        "models": all_results,
    }

    report_path = os.path.join(args.output_dir, "cpu_diagnostic_report.json")
    with open(report_path, "w") as f:
        json.dump(report, f, indent=2, default=str)
    print(f"\n[SAVED] {report_path}")

    # Print comparison table
    print(f"\n{'='*80}")
    print("COMPARISON SUMMARY")
    print(f"{'='*80}")
    print(f"{'Model':<30} {'Params':>8} {'PE96 Grid':>10} {'Synth Grid':>11} {'Synth Cell':>11} {'Speed':>10}")
    print("-" * 80)
    for key, res in all_results.items():
        pe96_g = res.get("pe96", {}).get("grid_acc", 0)
        synth_g = res["synth_1k"]["grid_acc"]
        synth_c = res["synth_1k"]["cell_acc"]
        speed = res["synth_1k"]["puzzles_per_s"]
        print(f"{res['label']:<30} {res['params']:>8,} {pe96_g:>10.4f} {synth_g:>11.4f} "
              f"{synth_c:>11.4f} {speed:>9.1f}/s")


if __name__ == "__main__":
    main()
