"""
Train CNN/MLP baselines for fair comparison with RRN.
Loads cached 208K dataset directly (no slow regeneration).
"""

import os
import sys
import time
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader

# Reuse core from train_classical
from train_classical import (
    SudokuCNN, SudokuMLP, SudokuDataset, sudoku_collate_fn,
    train_epoch, evaluate_model, DEVICE, SAVE_DIR, DATA_CACHE,
)

SEED = 42
EPOCHS = 40
PATIENCE = 10
LR = 1e-3
BATCH_SIZE = 128

# Target ~350K params for fair comparison with RRN (353K)
CONFIGS = [
    {
        'name': 'cnn_h72_l7_335k',
        'type': 'cnn',
        'params': {'hidden_dim': 72, 'n_layers': 7, 'dropout': 0.1},
    },
    {
        'name': 'mlp_h200_l2_349k',
        'type': 'mlp',
        'params': {'hidden_dim': 200, 'n_layers': 2, 'dropout': 0.1},
    },
    {
        'name': 'cnn_h64_l8_303k',
        'type': 'cnn',
        'params': {'hidden_dim': 64, 'n_layers': 8, 'dropout': 0.1},
    },
    {
        'name': 'mlp_h256_l3_409k',
        'type': 'mlp',
        'params': {'hidden_dim': 256, 'n_layers': 3, 'dropout': 0.1},
    },
]


def load_cached_data():
    """Load the existing cached 208K dataset directly."""
    cache_path = os.path.join(DATA_CACHE, 'diverse_400k.npz')
    if not os.path.exists(cache_path):
        print(f"ERROR: cache not found at {cache_path}")
        sys.exit(1)

    print(f"Loading cached data from {cache_path}...")
    data = np.load(cache_path)
    puzzles = data['puzzles']
    solutions = data['solutions']
    print(f"  Loaded {len(puzzles):,} puzzles (givens: "
          f"min={puzzles.min():.0f} mean={puzzles.astype(bool).sum(1).mean():.1f} "
          f"max={puzzles.astype(bool).sum(1).max()})")
    return puzzles, solutions


def train_baseline(name, model_type, model_params, puzzles, solutions):
    """Train a single baseline model."""
    torch.manual_seed(SEED)
    np.random.seed(SEED)

    # Train/val/test split (80/10/10)
    n = len(puzzles)
    perm = np.random.default_rng(SEED).permutation(n)
    puzzles, solutions = puzzles[perm], solutions[perm]

    n_train = int(n * 0.8)
    n_val = int(n * 0.1)

    train_ds = SudokuDataset(puzzles[:n_train], solutions[:n_train])
    val_ds = SudokuDataset(puzzles[n_train:n_train + n_val],
                           solutions[n_train:n_train + n_val])
    test_ds = SudokuDataset(puzzles[n_train + n_val:], solutions[n_train + n_val:])

    train_loader = DataLoader(train_ds, batch_size=BATCH_SIZE, shuffle=True,
                              num_workers=0, pin_memory=True, drop_last=True,
                              collate_fn=sudoku_collate_fn)
    val_loader = DataLoader(val_ds, batch_size=BATCH_SIZE, shuffle=False,
                            num_workers=0, pin_memory=True,
                            collate_fn=sudoku_collate_fn)
    test_loader = DataLoader(test_ds, batch_size=BATCH_SIZE, shuffle=False,
                             num_workers=0, pin_memory=True,
                             collate_fn=sudoku_collate_fn)

    if model_type == 'cnn':
        model = SudokuCNN(**model_params).to(DEVICE)
    else:
        model = SudokuMLP(**model_params).to(DEVICE)

    n_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"\n{'='*60}")
    print(f"Model: {name} ({model_type.upper()}, {n_params:,} params)")
    print(f"Train: {len(train_ds):,} | Val: {len(val_ds):,} | Test: {len(test_ds):,}")
    print(f"Device: {DEVICE}")
    print(f"{'='*60}")

    optimizer = torch.optim.Adam(model.parameters(), lr=LR, weight_decay=1e-5)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=EPOCHS)

    best_val_acc = 0
    best_val_grid = 0
    best_state = None
    patience_counter = 0

    for epoch in range(1, EPOCHS + 1):
        t0 = time.time()

        train_loss, train_acc = train_epoch(
            model, train_loader, optimizer, DEVICE, model_type)
        val_acc, val_grid = evaluate_model(
            model, val_loader, DEVICE, model_type)

        scheduler.step()
        elapsed = time.time() - t0

        marker = ""
        if val_acc > best_val_acc:
            best_val_acc = val_acc
            best_val_grid = val_grid
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}
            patience_counter = 0
            marker = " *"
        else:
            patience_counter += 1

        print(f"  Epoch {epoch:3d}/{EPOCHS} | "
              f"loss={train_loss:.4f} acc={train_acc:.3f} | "
              f"val_cell={val_acc:.3f} val_grid={val_grid:.3f} | "
              f"lr={optimizer.param_groups[0]['lr']:.1e} | {elapsed:.1f}s{marker}")

        if patience_counter >= PATIENCE:
            print(f"  Early stopping at epoch {epoch}")
            break

    # Restore best and evaluate on test
    if best_state is not None:
        model.load_state_dict(best_state)
        model.to(DEVICE)

    test_acc, test_grid = evaluate_model(model, test_loader, DEVICE, model_type)
    print(f"\n  TEST: cell_acc={test_acc:.4f}, grid_acc={test_grid:.4f}")

    # Save
    save_path = os.path.join(SAVE_DIR, f'comparison_{name}_best.pt')
    torch.save({
        'model_state_dict': best_state,
        'model_type': model_type,
        'model_params': model_params,
        'n_params': n_params,
        'test_cell_acc': test_acc,
        'test_grid_acc': test_grid,
        'best_val_cell_acc': best_val_acc,
        'best_val_grid_acc': best_val_grid,
        'dataset_size': len(puzzles),
    }, save_path)
    print(f"  Saved to {save_path}")

    return {
        'name': name,
        'type': model_type,
        'n_params': n_params,
        'test_cell_acc': test_acc,
        'test_grid_acc': test_grid,
        'best_val_cell_acc': best_val_acc,
        'best_val_grid_acc': best_val_grid,
    }


def main():
    print(f"Device: {DEVICE}")
    if DEVICE.type == 'cuda':
        print(f"GPU: {torch.cuda.get_device_name(0)}")
        print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB")

    puzzles, solutions = load_cached_data()

    results = []
    for cfg in CONFIGS:
        r = train_baseline(cfg['name'], cfg['type'], cfg['params'],
                           puzzles, solutions)
        results.append(r)

    # Summary
    print(f"\n{'='*70}")
    print("BASELINE COMPARISON RESULTS (208K dataset)")
    print(f"{'='*70}")
    print(f"{'Model':<25} {'Type':<5} {'Params':>8} {'Cell Acc':>10} {'Grid Acc':>10}")
    print("-" * 70)
    for r in sorted(results, key=lambda x: -x['test_grid_acc']):
        print(f"{r['name']:<25} {r['type']:<5} {r['n_params']:>8,} "
              f"{r['test_cell_acc']:>10.4f} {r['test_grid_acc']:>10.4f}")

    # Also show RRN reference
    print("-" * 70)
    print("{'rrn_h192_s16 (ref)':<25} {'rrn':<5} {'353,325':>8} {'0.8974':>10} {'0.8348':>10}")
    print(f"{'='*70}")


if __name__ == '__main__':
    main()
