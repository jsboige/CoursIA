"""
Sudoku RRN Overnight Training Sweep
====================================
Automated experiments to push accuracy limits.

Phase 1: Architecture sweep on diverse_200k
  - h128/s16, h192/s16, h256/s16, h128/s24, h192/s24, h256/s24
Phase 2: Data experiments with best architecture
  - HF 1M, combined diverse+generated
Phase 3: Iterative resolution tests on top models
Phase 4: Summary report
"""

import os
import sys
import time
import json
import gc
import traceback
import numpy as np
import torch
import torch.nn.functional as F
from torch.utils.data import DataLoader
from torch.amp import autocast

sys.path.insert(0, os.path.dirname(__file__))
from core import (
    SudokuRRN, build_sudoku_edge_index, make_batch_edge_index,
    evaluate, count_params, train_rrn, generate_puzzles,
    SudokuGraphDataset, sudoku_collate_fn, load_sudoku_dataset,
)

SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')
os.makedirs(SAVE_DIR, exist_ok=True)
RESULTS_FILE = os.path.join(SAVE_DIR, 'overnight_sweep_results.json')

device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')


def load_results():
    if os.path.exists(RESULTS_FILE):
        with open(RESULTS_FILE) as f:
            return json.load(f)
    return {'experiments': [], 'iterative_tests': [], 'start_time': time.strftime('%Y-%m-%d %H:%M:%S')}


def save_results(results):
    with open(RESULTS_FILE, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"  Results saved to {RESULTS_FILE}")


def load_npz(name):
    path = os.path.join(SAVE_DIR, 'data_cache', name)
    if not os.path.exists(path):
        return None, None
    data = np.load(path)
    puzzles = data['puzzles']
    solutions = data['solutions']
    if puzzles.ndim == 3:
        puzzles = puzzles.reshape(len(puzzles), 81)
        solutions = solutions.reshape(len(solutions), 81)
    print(f"  Loaded {name}: {len(puzzles):,} puzzles")
    return puzzles, solutions


def split_data(puzzles, solutions, train_frac=0.7, val_frac=0.15, seed=42):
    n = len(puzzles)
    rng = np.random.RandomState(seed)
    idx = rng.permutation(n)
    puzzles, solutions = puzzles[idx], solutions[idx]

    n_train = int(n * train_frac)
    n_val = int(n * val_frac)
    return (
        puzzles[:n_train], solutions[:n_train],
        puzzles[n_train:n_train + n_val], solutions[n_train:n_train + n_val],
        puzzles[n_train + n_val:], solutions[n_train + n_val:],
    )


def run_experiment(config, results):
    name = config['name']

    # Skip if already completed
    for exp in results['experiments']:
        if exp['name'] == name and exp.get('status') == 'completed':
            print(f"\n{'=' * 70}")
            print(f"SKIP {name} (already done)")
            print(f"{'=' * 70}")
            return exp

    print(f"\n{'=' * 70}")
    print(f"EXPERIMENT: {name}")
    hd, md, ns = config['hidden_dim'], config['msg_dim'], config['n_steps']
    print(f"  h={hd} msg={md} steps={ns} dropout={config.get('dropout', 0.1)}")
    print(f"  data={config['data_source']} batch={config.get('batch_size', 64)}")
    print(f"  epochs={config.get('n_epochs', 40)} patience={config.get('patience', 10)} lr={config.get('lr', 5e-4)}")
    print(f"{'=' * 70}")

    t0 = time.time()
    exp_result = {'name': name, 'config': config}

    try:
        # Load data
        data_src = config['data_source']
        if data_src == 'diverse_200k':
            puzzles, solutions = load_npz('diverse_200k.npz')
            if puzzles is None:
                raise FileNotFoundError("diverse_200k.npz not found")
        elif data_src == 'hf_1m':
            puzzles, solutions = load_npz('puzzles_hf_1000000.npz')
            if puzzles is None:
                print("  Downloading HF 1M...")
                puzzles, solutions = load_sudoku_dataset(n_total=1_000_000)
        elif data_src == 'combined_500k':
            puzzles, solutions = load_npz('combined_500k.npz')
            if puzzles is None:
                print("  Generating combined dataset...")
                div_p, div_s = load_npz('diverse_200k.npz')
                if div_p is None:
                    raise FileNotFoundError("diverse_200k.npz not found for combined")
                gen_p, gen_s = generate_puzzles(300_000, n_empty_range=(25, 58), seed=12345)
                puzzles = np.concatenate([div_p, gen_p])
                solutions = np.concatenate([div_s, gen_s])
                np.savez_compressed(
                    os.path.join(SAVE_DIR, 'data_cache', 'combined_500k.npz'),
                    puzzles=puzzles, solutions=solutions,
                )
                print(f"  Saved combined_500k: {len(puzzles):,} puzzles")
        elif data_src == 'generated_500k':
            puzzles, solutions = load_npz('generated_500k.npz')
            if puzzles is None:
                print("  Generating 500K diverse puzzles...")
                puzzles, solutions = generate_puzzles(500_000, n_empty_range=(20, 58), seed=54321)
                np.savez_compressed(
                    os.path.join(SAVE_DIR, 'data_cache', 'generated_500k.npz'),
                    puzzles=puzzles, solutions=solutions,
                )
                print(f"  Saved generated_500k: {len(puzzles):,} puzzles")
        else:
            raise ValueError(f"Unknown data source: {data_src}")

        # Split
        train_p, train_s, val_p, val_s, test_p, test_s = split_data(
            puzzles, solutions,
            train_frac=config.get('train_frac', 0.7),
            val_frac=config.get('val_frac', 0.15),
        )
        print(f"  Split: {len(train_p):,} train / {len(val_p):,} val / {len(test_p):,} test")

        # Curriculum: sort training by difficulty (easy first)
        n_givens = (train_p > 0).sum(axis=1)
        sort_idx = np.argsort(n_givens)
        train_p, train_s = train_p[sort_idx], train_s[sort_idx]
        givens_range = f"{n_givens.min()}-{n_givens.max()}"
        print(f"  Curriculum sorted (givens: {givens_range})")

        # Data loaders
        bs = config.get('batch_size', 64)
        train_loader = DataLoader(
            SudokuGraphDataset(train_p, train_s),
            batch_size=bs, shuffle=True, num_workers=0,
            pin_memory=True, drop_last=True, collate_fn=sudoku_collate_fn,
        )
        val_loader = DataLoader(
            SudokuGraphDataset(val_p, val_s),
            batch_size=bs, shuffle=False, num_workers=0,
            pin_memory=True, collate_fn=sudoku_collate_fn,
        )

        # Model
        base_edges = build_sudoku_edge_index()
        model = SudokuRRN(
            hidden_dim=hd, msg_dim=md, n_steps=ns,
            dropout=config.get('dropout', 0.1),
        ).to(device)
        n_params = count_params(model)
        print(f"  Model: {n_params:,} params")

        save_path = os.path.join(SAVE_DIR, f"sweep_{name}_best.pt")

        # Train
        model, history = train_rrn(
            model, train_loader, val_loader, base_edges, device,
            n_epochs=config.get('n_epochs', 40),
            patience=config.get('patience', 10),
            lr=config.get('lr', 5e-4),
            save_path=save_path,
        )

        # Evaluate
        cell_acc, grid_acc, test_loss = evaluate(
            model, test_p, test_s, base_edges, device, batch_size=bs,
        )

        elapsed = time.time() - t0
        exp_result.update({
            'n_params': n_params,
            'cell_acc': float(cell_acc),
            'grid_acc': float(grid_acc),
            'test_loss': float(test_loss),
            'n_test': len(test_p),
            'n_solved': int(grid_acc * len(test_p)),
            'elapsed_s': round(elapsed, 1),
            'actual_epochs': len(history),
            'best_val_epoch': max(range(len(history)), key=lambda i: history[i].get('val_acc', 0)) + 1 if history else 0,
            'history_summary': [
                {'epoch': h['epoch'], 'val_acc': h.get('val_acc', 0), 'val_loss': h.get('val_loss', 0)}
                for h in history[::5]  # Every 5th epoch
            ],
            'status': 'completed',
        })
        print(f"\n  RESULT: cell={cell_acc:.4f} grid={grid_acc:.4f} ({exp_result['n_solved']}/{len(test_p)}) in {elapsed:.0f}s")

    except Exception as e:
        elapsed = time.time() - t0
        exp_result.update({
            'status': 'failed',
            'error': str(e),
            'traceback': traceback.format_exc(),
            'elapsed_s': round(elapsed, 1),
        })
        print(f"\n  FAILED: {e}")
        print(traceback.format_exc()[-500:])

    # Cleanup
    try:
        del model
    except Exception:
        pass
    gc.collect()
    if torch.cuda.is_available():
        torch.cuda.empty_cache()

    results['experiments'].append(exp_result)
    save_results(results)
    return exp_result


# ── Iterative solver ──────────────────────────────────────────────────────

@torch.no_grad()
def iterative_solve(model, puzzle, base_edges, device, max_iter=81):
    """Solve one puzzle by iteratively filling most-confident cell."""
    model.eval()
    current = puzzle.copy()
    base_edges = base_edges.to(device)
    n_filled = 0

    for _ in range(max_iter):
        empty_mask = current == 0
        if not empty_mask.any():
            break

        # Encode
        is_given = (current > 0).astype(np.float32)
        x = np.zeros((1, 81, 10), dtype=np.float32)
        for d in range(1, 10):
            x[0, :, d - 1] = (current == d).astype(np.float32)
        x[0, :, 9] = is_given

        x_t = torch.tensor(x).to(device)
        edge_index = make_batch_edge_index(base_edges, 1)

        with autocast('cuda'):
            logits_list = model(x_t, edge_index)
            probs = F.softmax(logits_list[-1], dim=-1)  # (1, 81, 9)

        max_probs, max_digits = probs.squeeze(0).max(dim=-1)  # (81,)

        # Mask non-empty
        empty_t = torch.tensor(empty_mask, dtype=torch.float32, device=device)
        masked_conf = max_probs * empty_t

        best_cell = masked_conf.argmax().item()
        best_digit = max_digits[best_cell].item() + 1

        current[best_cell] = best_digit
        n_filled += 1

    return current, n_filled


def test_iterative(model_path, config, test_p, test_s, base_edges, n_test=200):
    """Compare one-shot vs iterative on n_test puzzles."""
    print(f"\n  Iterative resolution test on {n_test} puzzles...")

    model = SudokuRRN(
        hidden_dim=config['hidden_dim'], msg_dim=config['msg_dim'],
        n_steps=config['n_steps'], dropout=config.get('dropout', 0.1),
    ).to(device)
    ckpt = torch.load(model_path, weights_only=False, map_location=device)
    model.load_state_dict(ckpt['model_state_dict'])
    model.eval()

    idx = np.random.RandomState(99).choice(len(test_p), min(n_test, len(test_p)), replace=False)
    puzzles = test_p[idx]
    solutions = test_s[idx]

    # One-shot
    cell_1s, grid_1s, _ = evaluate(model, puzzles, solutions, base_edges, device, batch_size=32)

    # Iterative
    correct_cells = 0
    total_cells = 0
    solved = 0
    t0 = time.time()

    for i in range(len(puzzles)):
        result, n_filled = iterative_solve(model, puzzles[i], base_edges, device)
        empty = puzzles[i] == 0
        n_empty = empty.sum()
        correct = (result[empty] == solutions[i][empty]).sum()
        correct_cells += correct
        total_cells += n_empty
        if correct == n_empty:
            solved += 1
        if (i + 1) % 50 == 0:
            print(f"    {i + 1}/{len(puzzles)} ({time.time() - t0:.1f}s)")

    cell_it = correct_cells / total_cells if total_cells > 0 else 0
    grid_it = solved / len(puzzles) if len(puzzles) > 0 else 0
    elapsed = time.time() - t0

    print(f"  One-shot:   cell={cell_1s:.4f} grid={grid_1s:.4f}")
    print(f"  Iterative:  cell={cell_it:.4f} grid={grid_it:.4f} ({elapsed:.1f}s)")

    del model
    gc.collect()
    if torch.cuda.is_available():
        torch.cuda.empty_cache()

    return {
        'one_shot_cell': float(cell_1s),
        'one_shot_grid': float(grid_1s),
        'iterative_cell': float(cell_it),
        'iterative_grid': float(grid_it),
        'n_test': len(puzzles),
        'time_s': round(elapsed, 1),
    }


# ── Main ──────────────────────────────────────────────────────────────────

def main():
    print("=" * 70)
    print("SUDOKU RRN OVERNIGHT TRAINING SWEEP")
    print(f"Device: {device}")
    if torch.cuda.is_available():
        print(f"GPU: {torch.cuda.get_device_name(0)}")
        print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB")
    print(f"Start: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 70)

    results = load_results()

    # ── Phase 1: Architecture sweep ──────────────────────────────────────
    print("\n" + "#" * 70)
    print("# PHASE 1: ARCHITECTURE SWEEP (diverse_200k)")
    print("#" * 70)

    arch_configs = [
        {'name': 'h128_s16', 'hidden_dim': 128, 'msg_dim': 128, 'n_steps': 16, 'dropout': 0.1,
         'data_source': 'diverse_200k', 'batch_size': 64, 'n_epochs': 40, 'patience': 10, 'lr': 5e-4},
        {'name': 'h192_s16', 'hidden_dim': 192, 'msg_dim': 192, 'n_steps': 16, 'dropout': 0.1,
         'data_source': 'diverse_200k', 'batch_size': 48, 'n_epochs': 40, 'patience': 10, 'lr': 5e-4},
        {'name': 'h256_s16', 'hidden_dim': 256, 'msg_dim': 256, 'n_steps': 16, 'dropout': 0.1,
         'data_source': 'diverse_200k', 'batch_size': 32, 'n_epochs': 40, 'patience': 10, 'lr': 5e-4},
        {'name': 'h128_s24', 'hidden_dim': 128, 'msg_dim': 128, 'n_steps': 24, 'dropout': 0.1,
         'data_source': 'diverse_200k', 'batch_size': 48, 'n_epochs': 40, 'patience': 10, 'lr': 3e-4},
        {'name': 'h192_s24', 'hidden_dim': 192, 'msg_dim': 192, 'n_steps': 24, 'dropout': 0.1,
         'data_source': 'diverse_200k', 'batch_size': 32, 'n_epochs': 40, 'patience': 10, 'lr': 3e-4},
        {'name': 'h256_s24', 'hidden_dim': 256, 'msg_dim': 256, 'n_steps': 24, 'dropout': 0.1,
         'data_source': 'diverse_200k', 'batch_size': 24, 'n_epochs': 40, 'patience': 10, 'lr': 3e-4},
    ]

    for config in arch_configs:
        run_experiment(config, results)

    # ── Find best architecture ───────────────────────────────────────────
    completed = [e for e in results['experiments'] if e.get('status') == 'completed' and e['name'] in [c['name'] for c in arch_configs]]
    if not completed:
        print("\nNo architecture experiments completed! Aborting.")
        save_results(results)
        return

    best = max(completed, key=lambda e: e.get('cell_acc', 0))
    print(f"\nBest architecture: {best['name']}")
    print(f"  cell={best['cell_acc']:.4f} grid={best['grid_acc']:.4f} params={best['n_params']:,}")
    best_config = best['config']

    # ── Phase 2: Data experiments ────────────────────────────────────────
    print("\n" + "#" * 70)
    print("# PHASE 2: DATA EXPERIMENTS")
    print("#" * 70)

    data_configs = [
        {'name': f'data_hf1m_{best["name"]}', **{k: v for k, v in best_config.items() if k != 'name'},
         'data_source': 'hf_1m', 'n_epochs': 30, 'patience': 8, 'batch_size': max(16, best_config.get('batch_size', 64) // 2)},
        {'name': f'data_combined_{best["name"]}', **{k: v for k, v in best_config.items() if k != 'name'},
         'data_source': 'combined_500k', 'n_epochs': 40, 'patience': 10},
        {'name': f'data_gen500k_{best["name"]}', **{k: v for k, v in best_config.items() if k != 'name'},
         'data_source': 'generated_500k', 'n_epochs': 40, 'patience': 10},
    ]

    for config in data_configs:
        run_experiment(config, results)

    # ── Phase 3: Iterative resolution ────────────────────────────────────
    print("\n" + "#" * 70)
    print("# PHASE 3: ITERATIVE RESOLUTION TESTS")
    print("#" * 70)

    # Load test data
    div_p, div_s = load_npz('diverse_200k.npz')
    if div_p is not None:
        _, _, _, _, test_p, test_s = split_data(div_p, div_s)

        # Top 5 models by cell accuracy
        all_completed = [e for e in results['experiments'] if e.get('status') == 'completed']
        top5 = sorted(all_completed, key=lambda e: e.get('cell_acc', 0), reverse=True)[:5]

        for exp in top5:
            model_path = os.path.join(SAVE_DIR, f"sweep_{exp['name']}_best.pt")
            if not os.path.exists(model_path):
                # Also check for existing best model
                alt_path = os.path.join(SAVE_DIR, 'sudoku_rrn_hid128_msg128_n_s16_dro0.1_best.pt')
                if os.path.exists(alt_path) and 'h128_s16' in exp['name']:
                    model_path = alt_path
                else:
                    print(f"  Model not found: {model_path}, skipping")
                    continue

            print(f"\n  Testing iterative on {exp['name']}...")
            iter_result = test_iterative(model_path, exp['config'], test_p, test_s,
                                         build_sudoku_edge_index(), n_test=200)
            iter_result['experiment'] = exp['name']
            results['iterative_tests'].append(iter_result)
            save_results(results)
    else:
        print("  Could not load test data for iterative tests")

    # ── Phase 4: Larger model exploration ────────────────────────────────
    print("\n" + "#" * 70)
    print("# PHASE 4: LARGER MODEL EXPLORATION")
    print("#" * 70)

    large_configs = [
        {'name': 'h384_s16', 'hidden_dim': 384, 'msg_dim': 384, 'n_steps': 16, 'dropout': 0.1,
         'data_source': 'diverse_200k', 'batch_size': 12, 'n_epochs': 30, 'patience': 8, 'lr': 3e-4},
        {'name': 'h384_s24', 'hidden_dim': 384, 'msg_dim': 384, 'n_steps': 24, 'dropout': 0.1,
         'data_source': 'diverse_200k', 'batch_size': 6, 'n_epochs': 25, 'patience': 8, 'lr': 2e-4},
        {'name': 'h512_s16', 'hidden_dim': 512, 'msg_dim': 512, 'n_steps': 16, 'dropout': 0.1,
         'data_source': 'diverse_200k', 'batch_size': 4, 'n_epochs': 25, 'patience': 8, 'lr': 2e-4},
    ]

    for config in large_configs:
        run_experiment(config, results)

    # ── Phase 5: Best large model on best data ──────────────────────────
    print("\n" + "#" * 70)
    print("# PHASE 5: BEST LARGE MODEL ON BEST DATA")
    print("#" * 70)

    all_completed = [e for e in results['experiments'] if e.get('status') == 'completed']
    if len(all_completed) >= 2:
        # Find best architecture (excluding data experiments)
        arch_only = [e for e in all_completed if not e['name'].startswith('data_')]
        if arch_only:
            best_arch = max(arch_only, key=lambda e: e.get('cell_acc', 0))
            # Find best data (from data experiments)
            data_only = [e for e in all_completed if e['name'].startswith('data_')]
            if data_only:
                best_data_exp = max(data_only, key=lambda e: e.get('cell_acc', 0))
                best_data_src = best_data_exp['config']['data_source']
            else:
                best_data_src = 'combined_500k'

            final_config = dict(best_arch['config'])
            final_config['name'] = f'final_{best_arch["name"]}_{best_data_src}'
            final_config['data_source'] = best_data_src
            final_config['n_epochs'] = 50
            final_config['patience'] = 12
            run_experiment(final_config, results)

    # ── Final summary ────────────────────────────────────────────────────
    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)

    all_completed = [e for e in results['experiments'] if e.get('status') == 'completed']
    all_completed.sort(key=lambda e: e.get('cell_acc', 0), reverse=True)

    print(f"\n{'Name':<30} {'Params':>8} {'Cell':>8} {'Grid':>8} {'Solved':>8} {'Time':>8}")
    print("-" * 72)
    for e in all_completed:
        p = e.get('n_params', 0)
        c = e.get('cell_acc', 0)
        g = e.get('grid_acc', 0)
        s = e.get('n_solved', 0)
        n = e.get('n_test', 0)
        t = e.get('elapsed_s', 0)
        print(f"{e['name']:<30} {p:>8,} {c:>7.1%} {g:>7.1%} {s:>4}/{n:<3} {t:>6.0f}s")

    if results.get('iterative_tests'):
        print(f"\nIterative vs One-shot:")
        print(f"{'Experiment':<30} {'1S Cell':>8} {'1S Grid':>8} {'It Cell':>8} {'It Grid':>8} {'Delta':>8}")
        print("-" * 72)
        for it in results['iterative_tests']:
            delta = it['iterative_cell'] - it['one_shot_cell']
            print(f"{it['experiment']:<30} {it['one_shot_cell']:>7.1%} {it['one_shot_grid']:>7.1%} "
                  f"{it['iterative_cell']:>7.1%} {it['iterative_grid']:>7.1%} {delta:>+7.1%}")

    results['end_time'] = time.strftime('%Y-%m-%d %H:%M:%S')
    save_results(results)
    print(f"\nDone! All results in {RESULTS_FILE}")


if __name__ == '__main__':
    main()
