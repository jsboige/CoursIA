"""
Sudoku Iterative Solver Evaluation
====================================
Evaluates trained Sudoku models with advanced iterative inference.
Works with any model (V1 EPF, V3 ResNet) via checkpoint loading.

Key insight: One-shot prediction has a fundamental ceiling for Sudoku.
Even 99% per-cell accuracy gives only 0.99^47 ~ 62% grid accuracy.
Iterative filling with constraint propagation breaks through this ceiling.

Solver strategies:
1. Confidence-threshold batch filling (fill ALL cells above threshold)
2. Constraint checking (row, column, box validity)
3. Adaptive threshold decay (start conservative, gradually accept lower confidence)
4. Fallback to single most-confident cell when no threshold match
"""

import os
import sys
import time
import json
import numpy as np
import torch
import torch.nn as nn
from torch.utils.data import Dataset, DataLoader
from torch.amp import autocast

device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')

# ── Dataset loading (shared with training scripts) ─────────────────────────────
def parse_81(s):
    return np.array([int(c) for c in s], dtype=np.int64).reshape(9, 9)


def load_sudoku_dataset(n_total=1_000_000):
    SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', 'sudoku_models')
    cache_dir = os.path.join(SAVE_DIR, 'data_cache')
    p_cache = os.path.join(cache_dir, f'puzzles_hf_{n_total}.npz')

    if os.path.exists(p_cache):
        print(f"Loading cached puzzles from {p_cache}...")
        data = np.load(p_cache)
        return data['puzzles'], data['solutions']

    raise FileNotFoundError(f"No cached dataset at {p_cache}. Run training script first.")


# ── Model architectures (must match training scripts) ──────────────────────────
class ResBlock(nn.Module):
    def __init__(self, channels):
        super().__init__()
        self.block = nn.Sequential(
            nn.Conv2d(channels, channels, kernel_size=3, padding=1),
            nn.BatchNorm2d(channels),
            nn.ReLU(inplace=True),
            nn.Conv2d(channels, channels, kernel_size=3, padding=1),
            nn.BatchNorm2d(channels),
        )
        self.relu = nn.ReLU(inplace=True)

    def forward(self, x):
        return self.relu(x + self.block(x))


class SudokuResNet(nn.Module):
    """V3 Deep ResNet (31.8M params) - 8 ResBlocks."""
    def __init__(self):
        super().__init__()
        self.stem = nn.Sequential(
            nn.Conv2d(1, 64, kernel_size=3, padding=1),
            nn.BatchNorm2d(64),
            nn.ReLU(inplace=True),
        )
        self.res1 = nn.Sequential(*[ResBlock(64) for _ in range(4)])
        self.transition = nn.Sequential(
            nn.Conv2d(64, 128, kernel_size=1),
            nn.BatchNorm2d(128),
            nn.ReLU(inplace=True),
        )
        self.res2 = nn.Sequential(*[ResBlock(128) for _ in range(4)])
        self.head_conv = nn.Sequential(
            nn.Conv2d(128, 512, kernel_size=1),
            nn.ReLU(inplace=True),
        )
        self.flatten = nn.Flatten()
        self.fc = nn.Linear(512 * 9 * 9, 81 * 9)

    def forward(self, x):
        x = self.stem(x)
        x = self.res1(x)
        x = self.transition(x)
        x = self.res2(x)
        x = self.head_conv(x)
        x = self.flatten(x)
        x = self.fc(x)
        x = x.view(-1, 81, 9)
        return x


class EPFConvModel(nn.Module):
    """V1 EPF architecture (7.6M params) - 3-layer Conv2D."""
    def __init__(self):
        super().__init__()
        self.features = nn.Sequential(
            nn.Conv2d(1, 64, kernel_size=3, padding=1),
            nn.BatchNorm2d(64),
            nn.ReLU(inplace=True),
            nn.Conv2d(64, 64, kernel_size=3, padding=1),
            nn.BatchNorm2d(64),
            nn.ReLU(inplace=True),
            nn.Conv2d(64, 128, kernel_size=1),
            nn.ReLU(inplace=True),
        )
        self.flatten = nn.Flatten()
        self.fc = nn.Linear(128 * 9 * 9, 81 * 9)

    def forward(self, x):
        x = self.features(x)
        x = self.flatten(x)
        x = self.fc(x)
        x = x.view(-1, 81, 9)
        return x


def load_model(checkpoint_path, model_type='resnet'):
    if model_type == 'resnet':
        model = SudokuResNet()
    elif model_type == 'epf':
        model = EPFConvModel()
    else:
        raise ValueError(f"Unknown model_type: {model_type}")

    ckpt = torch.load(checkpoint_path, map_location=device, weights_only=False)
    model.load_state_dict(ckpt['model_state_dict'])
    model = model.to(device)
    model.eval()

    print(f"Loaded {model_type} model from {checkpoint_path}")
    print(f"  Epoch: {ckpt.get('epoch', '?')}, val_loss: {ckpt.get('val_loss', '?'):.4f}, val_acc: {ckpt.get('val_acc', '?'):.4f}")
    n_params = sum(p.numel() for p in model.parameters())
    print(f"  Params: {n_params:,}")
    return model


# ── Constraint checking ────────────────────────────────────────────────────────
def is_valid_placement(grid, row, col, num):
    """Check if placing num at (row, col) violates Sudoku constraints."""
    # Row check
    if num in grid[row]:
        return False
    # Column check
    if num in grid[:, col]:
        return False
    # Box check
    br, bc = 3 * (row // 3), 3 * (col // 3)
    if num in grid[br:br+3, bc:bc+3]:
        return False
    return True


def get_valid_candidates(grid, row, col):
    """Get all valid numbers for a cell."""
    used = set(grid[row]) | set(grid[:, col])
    br, bc = 3 * (row // 3), 3 * (col // 3)
    used |= set(grid[br:br+3, bc:bc+3].flatten())
    return [n for n in range(1, 10) if n not in used]


def count_empty(puzzle):
    return int((puzzle == 0).sum())


# ── Iterative solvers ──────────────────────────────────────────────────────────
def solve_single_cell(model, puzzle, device, max_steps=81):
    """Original solver: fill single most confident cell per step.

    This is what V3 used but with max_steps=81 instead of 10.
    """
    model.eval()
    current = puzzle.copy()

    with torch.no_grad():
        for step in range(max_steps):
            empty_mask = (current == 0)
            if not empty_mask.any():
                return current, step + 1, True  # solved

            x = torch.tensor((current / 9.0 - 0.5).astype(np.float32)).unsqueeze(0).unsqueeze(0).to(device)
            with autocast('cuda'):
                logits = model(x)
            probs = torch.softmax(logits, dim=-1)

            empty_indices = np.where(empty_mask.flatten())[0]
            max_conf = -1
            best_idx = -1
            best_val = -1

            for idx in empty_indices:
                conf, val = probs[0, idx].max(dim=0)
                if conf.item() > max_conf:
                    max_conf = conf.item()
                    best_idx = idx
                    best_val = val.item()

            r, c = divmod(best_idx, 9)
            current[r][c] = best_val + 1

    return current, max_steps, not (current == 0).any()


def solve_batch_confidence(model, puzzle, device, max_steps=81, init_threshold=0.999,
                           decay=0.97, min_threshold=0.5, use_constraints=True):
    """Batch confidence solver: fill ALL cells above threshold per step.

    Args:
        model: Trained Sudoku model
        puzzle: 9x9 numpy array (0 = empty)
        device: torch device
        max_steps: Maximum iterations
        init_threshold: Initial confidence threshold
        decay: Threshold decay factor per step
        min_threshold: Minimum confidence threshold
        use_constraints: If True, validate Sudoku constraints before filling

    Returns:
        (solved_grid, n_steps, is_complete)
    """
    model.eval()
    current = puzzle.copy()
    threshold = init_threshold

    with torch.no_grad():
        for step in range(max_steps):
            empty_mask = (current == 0)
            if not empty_mask.any():
                return current, step + 1, True

            x = torch.tensor((current / 9.0 - 0.5).astype(np.float32)).unsqueeze(0).unsqueeze(0).to(device)
            with autocast('cuda'):
                logits = model(x)
            probs = torch.softmax(logits, dim=-1)

            # Fill ALL cells above confidence threshold
            filled_this_step = 0
            empty_indices = np.where(empty_mask.flatten())[0]

            # Sort by confidence (highest first)
            cell_confs = []
            for idx in empty_indices:
                conf, val = probs[0, idx].max(dim=0)
                cell_confs.append((idx, conf.item(), val.item()))
            cell_confs.sort(key=lambda x: x[1], reverse=True)

            for idx, conf, val in cell_confs:
                if conf < threshold:
                    break
                r, c = divmod(idx, 9)
                candidate = val + 1
                if use_constraints:
                    if is_valid_placement(current, r, c, candidate):
                        current[r][c] = candidate
                        filled_this_step += 1
                else:
                    current[r][c] = candidate
                    filled_this_step += 1

            if filled_this_step == 0:
                # No cell above threshold - fill the single most confident
                if cell_confs:
                    idx, conf, val = cell_confs[0]
                    r, c = divmod(idx, 9)
                    candidate = val + 1
                    if use_constraints and not is_valid_placement(current, r, c, candidate):
                        # Try next best that satisfies constraints
                        for idx2, conf2, val2 in cell_confs[1:]:
                            r2, c2 = divmod(idx2, 9)
                            cand2 = val2 + 1
                            if is_valid_placement(current, r2, c2, cand2):
                                current[r2][c2] = cand2
                                break
                        else:
                            # No valid placement found - force most confident
                            current[r][c] = candidate
                    else:
                        current[r][c] = candidate

            # Decay threshold
            threshold = max(min_threshold, threshold * decay)

    return current, max_steps, not (current == 0).any()


def solve_constraint_propagation(model, puzzle, device, max_steps=81):
    """Constraint propagation solver: use model predictions + naked singles.

    Combines neural network confidence with classical constraint propagation.
    If any cell has only one valid candidate (naked single), fill it regardless
    of model confidence.
    """
    model.eval()
    current = puzzle.copy()

    with torch.no_grad():
        for step in range(max_steps):
            empty_mask = (current == 0)
            if not empty_mask.any():
                return current, step + 1, True

            # Phase 1: Find naked singles (cells with only one valid candidate)
            filled_naked = 0
            for r in range(9):
                for c in range(9):
                    if current[r][c] == 0:
                        candidates = get_valid_candidates(current, r, c)
                        if len(candidates) == 1:
                            current[r][c] = candidates[0]
                            filled_naked += 1

            if filled_naked > 0:
                continue  # Re-run with updated grid

            # Phase 2: Use model predictions for remaining cells
            x = torch.tensor((current / 9.0 - 0.5).astype(np.float32)).unsqueeze(0).unsqueeze(0).to(device)
            with autocast('cuda'):
                logits = model(x)
            probs = torch.softmax(logits, dim=-1)

            # Find most confident prediction among empty cells
            empty_indices = np.where(current.flatten() == 0)[0]
            if len(empty_indices) == 0:
                return current, step + 1, True

            best_conf = -1
            best_idx = -1
            best_val = -1
            for idx in empty_indices:
                conf, val = probs[0, idx].max(dim=0)
                r, c = divmod(idx, 9)
                candidate = val.item() + 1
                if is_valid_placement(current, r, c, candidate):
                    if conf.item() > best_conf:
                        best_conf = conf.item()
                        best_idx = idx
                        best_val = val.item()

            if best_idx >= 0:
                r, c = divmod(best_idx, 9)
                current[r][c] = best_val + 1
            else:
                # No valid placement from model - force most confident
                max_conf = -1
                for idx in empty_indices:
                    conf, val = probs[0, idx].max(dim=0)
                    if conf.item() > max_conf:
                        max_conf = conf.item()
                        best_idx = idx
                        best_val = val.item()
                r, c = divmod(best_idx, 9)
                current[r][c] = best_val + 1

    return current, max_steps, not (current == 0).any()


# ── Evaluation ─────────────────────────────────────────────────────────────────
def evaluate_one_shot(model, puzzles, solutions, device, batch_size=256):
    model.eval()
    n = len(puzzles)
    correct_cells = 0
    correct_empty = 0
    total_cells = 0
    total_empty = 0
    solved_grids = 0

    with torch.no_grad():
        for i in range(0, n, batch_size):
            batch_p = puzzles[i:i+batch_size]
            batch_s = solutions[i:i+batch_size]

            x = torch.tensor((batch_p / 9.0 - 0.5).astype(np.float32)).unsqueeze(1).to(device)
            y = torch.tensor((batch_s - 1).astype(np.int64)).to(device)
            empty = torch.tensor((batch_p == 0).astype(np.float32)).to(device)

            with autocast('cuda'):
                logits = model(x)
            preds = logits.argmax(dim=-1)

            correct = (preds == y.view(preds.shape))
            correct_cells += correct.sum().item()
            total_cells += correct.numel()

            correct_e = correct.float() * empty.view(correct.shape)
            correct_empty += correct_e.sum().item()
            total_empty += empty.sum().item()

            grid_correct = correct.view(-1, 81).all(dim=1)
            solved_grids += grid_correct.sum().item()

    cell_acc = correct_cells / total_cells
    empty_acc = correct_empty / total_empty
    grid_acc = solved_grids / n
    return cell_acc, grid_acc, empty_acc


def evaluate_iterative(model, puzzles, solutions, device, solver_fn, n_eval=500, **solver_kwargs):
    model.eval()
    solved = 0
    correct_cells = 0
    total_cells = 0
    total_steps = 0

    for i in range(min(n_eval, len(puzzles))):
        result, n_steps, complete = solver_fn(model, puzzles[i], device, **solver_kwargs)
        target = solutions[i]

        correct = (result == target)
        correct_cells += correct.sum()
        total_cells += 81
        total_steps += n_steps

        if correct.all():
            solved += 1

        if (i + 1) % 100 == 0:
            current_acc = solved / (i + 1)
            print(f"  {i+1}/{min(n_eval, len(puzzles))}: solved={solved}, grid_acc={current_acc:.4f}")

    cell_acc = correct_cells / total_cells if total_cells > 0 else 0
    grid_acc = solved / min(n_eval, len(puzzles))
    avg_steps = total_steps / min(n_eval, len(puzzles))
    return cell_acc, grid_acc, avg_steps


# ── Main ───────────────────────────────────────────────────────────────────────
def main():
    import argparse
    parser = argparse.ArgumentParser(description='Evaluate Sudoku models with iterative solving')
    parser.add_argument('--model', choices=['resnet', 'epf'], default='resnet')
    parser.add_argument('--checkpoint', type=str, default=None,
                        help='Path to model checkpoint. Auto-detects if omitted.')
    parser.add_argument('--n-test', type=int, default=500)
    parser.add_argument('--max-steps', type=int, default=81)
    parser.add_argument('--solver', choices=['single', 'batch', 'constraint', 'all'], default='all')
    args = parser.parse_args()

    SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', 'sudoku_models')

    # Auto-detect checkpoint
    if args.checkpoint is None:
        if args.model == 'resnet':
            args.checkpoint = os.path.join(SAVE_DIR, 'sudoku_resnet_v3_best.pt')
        else:
            args.checkpoint = os.path.join(SAVE_DIR, 'sudoku_epf_best.pt')

    print("=" * 70)
    print("Sudoku Iterative Solver Evaluation")
    print(f"Model: {args.model} | Checkpoint: {args.checkpoint}")
    print(f"N test: {args.n_test} | Max steps: {args.max_steps} | Solver: {args.solver}")
    print("=" * 70)

    if device.type == 'cuda':
        print(f"GPU: {torch.cuda.get_device_name(0)}")

    # Load model
    model = load_model(args.checkpoint, args.model)

    # Load dataset
    all_puzzles, all_solutions = load_sudoku_dataset(1_000_000)
    N_TRAIN, N_VAL = 900_000, 80_000
    test_p = all_puzzles[N_TRAIN + N_VAL:]
    test_s = all_solutions[N_TRAIN + N_VAL:]
    del all_puzzles, all_solutions

    n_eval = min(args.n_test, len(test_p))

    # One-shot baseline
    print(f"\n{'='*70}")
    print(f"ONE-SHOT BASELINE ({n_eval} puzzles)")
    print(f"{'='*70}")
    os_cell, os_grid, os_empty = evaluate_one_shot(model, test_p[:n_eval], test_s[:n_eval], device)
    print(f"One-shot: cell={os_cell:.4f} | empty={os_empty:.4f} | grid={os_grid:.4f} ({int(os_grid*n_eval)}/{n_eval})")

    results = {
        'one_shot': {'cell_acc': os_cell, 'grid_acc': os_grid, 'empty_acc': os_empty},
        'iterative': {},
    }

    # Iterative solvers
    solvers = {
        'single': (solve_single_cell, {'max_steps': args.max_steps}),
        'batch': (solve_batch_confidence, {
            'max_steps': args.max_steps,
            'init_threshold': 0.999,
            'decay': 0.97,
            'min_threshold': 0.5,
            'use_constraints': True,
        }),
        'constraint': (solve_constraint_propagation, {'max_steps': args.max_steps}),
    }

    if args.solver != 'all':
        solvers = {args.solver: solvers[args.solver]}

    for name, (solver_fn, kwargs) in solvers.items():
        print(f"\n{'='*70}")
        print(f"SOLVER: {name.upper()} ({n_eval} puzzles, max_steps={args.max_steps})")
        print(f"{'='*70}")
        t0 = time.time()
        cell_acc, grid_acc, avg_steps = evaluate_iterative(
            model, test_p, test_s, device, solver_fn, n_eval=n_eval, **kwargs
        )
        elapsed = time.time() - t0
        print(f"\n{name}: cell={cell_acc:.4f} | grid={grid_acc:.4f} ({int(grid_acc*n_eval)}/{n_eval}) | avg_steps={avg_steps:.1f} | time={elapsed:.1f}s")

        results['iterative'][name] = {
            'cell_acc': float(cell_acc),
            'grid_acc': float(grid_acc),
            'avg_steps': float(avg_steps),
            'time_s': elapsed,
            'n_eval': n_eval,
            'max_steps': args.max_steps,
        }

    # Save results
    results_path = os.path.join(SAVE_DIR, f'iterative_eval_{args.model}.json')
    with open(results_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {results_path}")

    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"One-shot grid accuracy: {os_grid*100:.1f}%")
    for name, res in results['iterative'].items():
        target_met = "YES" if res['grid_acc'] >= 0.968 else "NO"
        print(f"{name} grid accuracy: {res['grid_acc']*100:.1f}% (avg {res['avg_steps']:.1f} steps) | Target >=96.8%: {target_met}")
    print(f"{'='*70}")


if __name__ == '__main__':
    main()
