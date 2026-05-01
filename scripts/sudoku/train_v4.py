"""Sudoku RRN V4 Training Script.

Recurrent Relational Network (Palm et al. 2018) for Sudoku solving.
~170K params, graph message passing + GRU with BPTT over 8 reasoning steps.
Dataset: nakashi104/sudoku-1million (HuggingFace).
"""

import os
import sys
import json
import torch
from torch.utils.data import DataLoader

# Add parent to path so we can import core
sys.path.insert(0, os.path.dirname(__file__))

from core import (
    SudokuRRN, count_params, build_sudoku_edge_index,
    load_sudoku_dataset, SudokuGraphDataset, sudoku_collate_fn,
    train_rrn, evaluate,
)

device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
print(f"Device: {device}")
if torch.cuda.is_available():
    print(f"GPU: {torch.cuda.get_device_name(0)}")
    print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB")
    torch.backends.cudnn.benchmark = True


def main():
    N_TRAIN = 900_000
    N_VAL = 80_000
    N_TEST = 20_000
    BATCH_SIZE = 64
    N_EPOCHS = 80
    PATIENCE = 12
    LR = 5e-4
    HIDDEN_DIM = 128
    MSG_DIM = 128
    N_STEPS = 8
    DROPOUT = 0.15

    SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')
    os.makedirs(SAVE_DIR, exist_ok=True)
    SAVE_PATH = os.path.join(SAVE_DIR, 'sudoku_rrn_v4_best.pt')
    RESULTS_PATH = os.path.join(SAVE_DIR, 'training_results_v4.json')

    print("=" * 70)
    print("Sudoku Recurrent Relational Network V4")
    print(f"Config: {N_TRAIN:,} train / {N_VAL:,} val / {N_TEST:,} test")
    print(f"Model: hidden={HIDDEN_DIM} msg={MSG_DIM} steps={N_STEPS} dropout={DROPOUT}")
    print(f"Batch: {BATCH_SIZE} | Epochs: {N_EPOCHS} | Patience: {PATIENCE} | LR: {LR}")
    print(f"Save: {SAVE_PATH}")
    print("=" * 70)

    all_puzzles, all_solutions = load_sudoku_dataset(n_total=1_000_000)

    n_givens = (all_puzzles > 0).sum(axis=1)
    valid = n_givens >= 17
    n_filtered = (~valid).sum()
    if n_filtered > 0:
        print(f"Filtered {n_filtered:,} puzzles with <17 givens")
        all_puzzles = all_puzzles[valid]
        all_solutions = all_solutions[valid]

    n_givens = (all_puzzles > 0).sum(axis=1)
    sort_idx = np.argsort(n_givens)
    all_puzzles = all_puzzles[sort_idx]
    all_solutions = all_solutions[sort_idx]
    print(f"Curriculum: sorted by difficulty (givens range: {n_givens.min()}-{n_givens.max()})")

    train_p = all_puzzles[:N_TRAIN].copy()
    train_s = all_solutions[:N_TRAIN].copy()
    val_p = all_puzzles[N_TRAIN:N_TRAIN+N_VAL].copy()
    val_s = all_solutions[N_TRAIN:N_TRAIN+N_VAL].copy()
    test_p = all_puzzles[N_TRAIN+N_VAL:].copy()
    test_s = all_solutions[N_TRAIN+N_VAL:].copy()

    del all_puzzles, all_solutions
    import gc; gc.collect()

    train_ds = SudokuGraphDataset(train_p, train_s)
    val_ds = SudokuGraphDataset(val_p, val_s)
    train_loader = DataLoader(train_ds, batch_size=BATCH_SIZE, shuffle=True,
                              num_workers=0, pin_memory=True, drop_last=True,
                              collate_fn=sudoku_collate_fn)
    val_loader = DataLoader(val_ds, batch_size=BATCH_SIZE, shuffle=False,
                            num_workers=0, pin_memory=True,
                            collate_fn=sudoku_collate_fn)

    print(f"\nTrain: {len(train_ds):,} | Val: {len(val_ds):,}")

    base_edges = build_sudoku_edge_index()
    n_edges = base_edges.size(1)
    n_neighbors = n_edges // 81
    print(f"\nGraph: 81 nodes, {n_edges} directed edges ({n_neighbors} neighbors/cell)")

    model = SudokuRRN(
        hidden_dim=HIDDEN_DIM,
        msg_dim=MSG_DIM,
        n_steps=N_STEPS,
        dropout=DROPOUT,
    ).to(device)
    n_params = count_params(model)
    print(f"\nModel: SudokuRRN ({n_params:,} params)")

    if torch.cuda.is_available():
        vram_used = torch.cuda.memory_allocated(0) / 1e9
        vram_total = torch.cuda.get_device_properties(0).total_memory / 1e9
        print(f"VRAM: {vram_used:.2f} / {vram_total:.1f} GB (model loaded)")

    import time
    t0_total = time.time()
    model, history = train_rrn(
        model, train_loader, val_loader, base_edges, device,
        n_epochs=N_EPOCHS, patience=PATIENCE, lr=LR, save_path=SAVE_PATH,
    )
    train_time = time.time() - t0_total
    print(f"\nTotal training time: {train_time:.1f}s ({train_time/60:.1f}min)")

    print("\n" + "=" * 70)
    print("ZERO-SHOT EVALUATION")
    print("=" * 70)

    cell_acc, grid_acc, test_loss = evaluate(
        model, test_p, test_s, base_edges, device, batch_size=BATCH_SIZE,
    )
    n_solved = int(grid_acc * N_TEST)
    print(f"Zero-shot: cell_acc={cell_acc:.4f} | grid_acc={grid_acc:.4f} ({n_solved}/{N_TEST})")
    print(f"Test loss: {test_loss:.4f}")

    results = {
        'config': {
            'n_train': N_TRAIN, 'n_val': N_VAL, 'n_test': N_TEST,
            'batch_size': BATCH_SIZE, 'n_epochs': N_EPOCHS, 'patience': PATIENCE,
            'lr': LR, 'model_params': n_params,
            'hidden_dim': HIDDEN_DIM, 'msg_dim': MSG_DIM,
            'n_steps': N_STEPS, 'dropout': DROPOUT,
            'architecture': 'SudokuRRN (Recurrent Relational Network)',
            'dataset': 'nakashi104/sudoku-1million (HuggingFace)',
            'curriculum': 'sorted by difficulty (easy first)',
        },
        'zero_shot': {
            'cell_acc': cell_acc,
            'grid_acc': grid_acc,
            'test_loss': test_loss,
            'n_solved': n_solved,
            'n_total': N_TEST,
        },
        'training_time_s': train_time,
        'actual_epochs': history[-1]['epoch'] if history else 0,
        'history': history,
    }

    with open(RESULTS_PATH, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {RESULTS_PATH}")


if __name__ == '__main__':
    import numpy as np
    main()
