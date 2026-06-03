"""
Sudoku Lightweight Model Training
==================================
Train a small MLP and CNN on the HuggingFace 1M Sudoku dataset.
Models are designed to be <1MB so they can be committed to git.

Outputs:
  sudoku_models/sudoku_mlp_lightweight_best.pt  (~400KB)
  sudoku_models/sudoku_cnn_lightweight_best.pt   (~500KB)
  sudoku_models/training_results_lightweight.json

Usage: python scripts/sudoku_train_lightweight.py
"""

import os
import sys
import time
import json
import numpy as np
import torch
import torch.nn as nn
import torch.optim as optim
from torch.utils.data import Dataset, DataLoader

device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
print(f"Device: {device}")
if torch.cuda.is_available():
    print(f"GPU: {torch.cuda.get_device_name(0)}")
    print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB")


# ── Dataset ────────────────────────────────────────────────────────────────────
def parse_81(s):
    return np.array([int(c) for c in s], dtype=np.int64).reshape(9, 9)


def load_sudoku_dataset(n_total=1_000_000):
    SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')
    cache_dir = os.path.join(SAVE_DIR, 'data_cache')
    os.makedirs(cache_dir, exist_ok=True)
    p_cache = os.path.join(cache_dir, f'puzzles_hf_{n_total}.npz')

    if os.path.exists(p_cache):
        print(f"Loading cached puzzles from {p_cache}...")
        data = np.load(p_cache)
        return data['puzzles'], data['solutions']

    from datasets import load_dataset
    print(f"Downloading nakashi104/sudoku-1million from HuggingFace...")
    ds = load_dataset('nakashi104/sudoku-1million', split='train')
    n_use = min(n_total, len(ds))
    all_puzzles = np.zeros((n_use, 9, 9), dtype=np.int64)
    all_solutions = np.zeros((n_use, 9, 9), dtype=np.int64)
    t0 = time.time()
    for i, row in enumerate(ds.select(range(n_use))):
        all_puzzles[i] = parse_81(row['quizzes'])
        all_solutions[i] = parse_81(row['solutions'])
    np.savez_compressed(p_cache, puzzles=all_puzzles, solutions=all_solutions)
    print(f"Cached {n_use:,} puzzles in {time.time()-t0:.1f}s")
    return all_puzzles, all_solutions


class SudokuFlatDataset(Dataset):
    """Flat encoding: (81, 10) — 9 one-hot digits + 1 is_given."""

    def __init__(self, puzzles, solutions):
        n = len(puzzles)
        p_flat = puzzles.reshape(n, 81)
        s_flat = solutions.reshape(n, 81)
        self.x = np.zeros((n, 81, 10), dtype=np.float32)
        for d in range(1, 10):
            self.x[:, :, d - 1] = (p_flat == d).astype(np.float32)
        self.x[:, :, 9] = (p_flat > 0).astype(np.float32)
        self.y = s_flat.astype(np.int64) - 1
        self.mask = (p_flat == 0).astype(np.float32)

    def __len__(self):
        return len(self.x)

    def __getitem__(self, idx):
        return (
            torch.tensor(self.x[idx]),
            torch.tensor(self.y[idx]),
            torch.tensor(self.mask[idx]),
        )


# ── Models ─────────────────────────────────────────────────────────────────────
class SudokuMLP(nn.Module):
    """Small MLP: Input(810) -> 3x Dense(256) -> Dense(729) -> Reshape(81,9)."""

    def __init__(self, hidden=256, n_layers=3):
        super().__init__()
        layers = []
        in_dim = 81 * 10
        for _ in range(n_layers):
            layers += [nn.Linear(in_dim, hidden), nn.ReLU(), nn.Dropout(0.1)]
            in_dim = hidden
        layers.append(nn.Linear(hidden, 81 * 9))
        self.net = nn.Sequential(*layers)

    def forward(self, x):
        x = x.view(x.size(0), -1)
        x = self.net(x)
        return x.view(-1, 81, 9)


class SudokuCNN(nn.Module):
    """Small CNN: treats 9x9 grid as image with 10 channels.
    Conv layers with same padding preserve 9x9 resolution.
    Final 1x1 conv produces 9 logits per cell.

    Input: (B, 10, 9, 9) -> Output: (B, 81, 9)
    """

    def __init__(self, channels=64, n_blocks=3):
        super().__init__()
        layers = []
        in_ch = 10
        for _ in range(n_blocks):
            layers += [
                nn.Conv2d(in_ch, channels, 3, padding=1),
                nn.BatchNorm2d(channels),
                nn.ReLU(),
            ]
            in_ch = channels
        layers.append(nn.Conv2d(channels, 9, 1))
        self.conv = nn.Sequential(*layers)

    def forward(self, x_flat):
        # x_flat: (B, 81, 10) -> reshape to (B, 10, 9, 9)
        x = x_flat.view(x_flat.size(0), 9, 9, 10).permute(0, 3, 1, 2)
        x = self.conv(x)  # (B, 9, 9, 9)
        x = x.permute(0, 2, 3, 1)  # (B, 9, 9, 9)
        return x.reshape(x.size(0), 81, 9)


def count_params(model):
    return sum(p.numel() for p in model.parameters() if p.requires_grad)


# ── Evaluation ─────────────────────────────────────────────────────────────────
@torch.no_grad()
def evaluate(model, loader, device):
    model.eval()
    correct_cells = 0
    total_cells = 0
    solved_grids = 0
    total_grids = 0
    is_cnn = isinstance(model, SudokuCNN)

    for batch_x, batch_y, batch_m in loader:
        batch_x = batch_x.to(device)
        batch_y = batch_y.to(device)
        batch_m = batch_m.to(device)

        logits = model(batch_x)
        preds = logits.argmax(dim=-1)

        correct = (preds == batch_y).float() * batch_m
        correct_cells += correct.sum().item()
        total_cells += batch_m.sum().item()

        grid_ok = ((preds == batch_y) | (~batch_m.bool())).all(dim=1)
        solved_grids += grid_ok.sum().item()
        total_grids += batch_x.size(0)

    cell_acc = correct_cells / total_cells if total_cells > 0 else 0
    grid_acc = solved_grids / total_grids if total_grids > 0 else 0
    return cell_acc, grid_acc


# ── Training ───────────────────────────────────────────────────────────────────
def train_model(model, train_loader, val_loader, device, n_epochs=30,
                lr=1e-3, patience=8, save_path='model.pt'):
    optimizer = optim.AdamW(model.parameters(), lr=lr, weight_decay=1e-4)
    scheduler = optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=n_epochs, eta_min=1e-6)
    criterion = nn.CrossEntropyLoss(reduction='none')

    best_val_acc = 0
    best_epoch = 0
    no_improve = 0
    history = []

    for epoch in range(1, n_epochs + 1):
        model.train()
        train_loss = 0
        t0 = time.time()

        for batch_x, batch_y, batch_m in train_loader:
            batch_x = batch_x.to(device)
            batch_y = batch_y.to(device)
            batch_m = batch_m.to(device)

            optimizer.zero_grad()
            logits = model(batch_x)
            per_cell = criterion(logits.reshape(-1, 9), batch_y.reshape(-1))
            loss = (per_cell * batch_m.reshape(-1)).sum() / batch_m.sum().clamp(min=1)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            train_loss += loss.item() * batch_x.size(0)

        train_loss /= len(train_loader.dataset)
        scheduler.step()

        val_cell, val_grid = evaluate(model, val_loader, device)
        elapsed = time.time() - t0

        print(f"Epoch {epoch:3d}/{n_epochs} | loss={train_loss:.4f} | "
              f"val_cell={val_cell:.4f} val_grid={val_grid:.4f} | {elapsed:.1f}s")

        history.append({
            'epoch': epoch, 'train_loss': train_loss,
            'val_cell_acc': val_cell, 'val_grid_acc': val_grid,
        })

        if val_grid > best_val_acc or (val_grid == best_val_acc and val_cell > 0):
            best_val_acc = val_grid
            best_epoch = epoch
            no_improve = 0
            torch.save({
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'val_cell_acc': val_cell,
                'val_grid_acc': val_grid,
            }, save_path)
            print(f"  -> Best model saved (val_grid={val_grid:.4f})")
        else:
            no_improve += 1

        if no_improve >= patience:
            print(f"Early stopping at epoch {epoch}")
            break

    ckpt = torch.load(save_path, weights_only=False)
    model.load_state_dict(ckpt['model_state_dict'])
    return model, history


# ── Main ───────────────────────────────────────────────────────────────────────
def main():
    N_TRAIN = 100_000
    N_VAL = 20_000
    N_TEST = 20_000
    BATCH_SIZE = 256

    SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')
    os.makedirs(SAVE_DIR, exist_ok=True)
    RESULTS_PATH = os.path.join(SAVE_DIR, 'training_results_lightweight.json')

    print("=" * 70)
    print("Sudoku Lightweight Models Training")
    print(f"Config: {N_TRAIN:,} train / {N_VAL:,} val / {N_TEST:,} test")
    print("=" * 70)

    all_puzzles, all_solutions = load_sudoku_dataset(n_total=1_000_000)

    # Shuffle
    np.random.seed(42)
    perm = np.random.permutation(len(all_puzzles))
    all_puzzles = all_puzzles[perm]
    all_solutions = all_solutions[perm]
    print(f"Loaded {len(all_puzzles):,} puzzles")

    train_p, train_s = all_puzzles[:N_TRAIN], all_solutions[:N_TRAIN]
    val_p, val_s = all_puzzles[N_TRAIN:N_TRAIN+N_VAL], all_solutions[N_TRAIN:N_TRAIN+N_VAL]
    test_p, test_s = all_puzzles[N_TRAIN+N_VAL:N_TRAIN+N_VAL+N_TEST], all_solutions[N_TRAIN+N_VAL:N_TRAIN+N_VAL+N_TEST]
    del all_puzzles, all_solutions

    train_ds = SudokuFlatDataset(train_p, train_s)
    val_ds = SudokuFlatDataset(val_p, val_s)
    test_ds = SudokuFlatDataset(test_p, test_s)
    train_loader = DataLoader(train_ds, batch_size=BATCH_SIZE, shuffle=True, num_workers=0, pin_memory=True)
    val_loader = DataLoader(val_ds, batch_size=BATCH_SIZE, shuffle=False, num_workers=0, pin_memory=True)
    test_loader = DataLoader(test_ds, batch_size=BATCH_SIZE, shuffle=False, num_workers=0, pin_memory=True)

    print(f"\nTrain: {len(train_ds):,} | Val: {len(val_ds):,} | Test: {len(test_ds):,}")

    all_results = {}

    # ── MLP ────────────────────────────────────────────────────────────────
    print("\n" + "=" * 70)
    print("Training MLP (lightweight)")
    print("=" * 70)
    mlp = SudokuMLP(hidden=256, n_layers=3).to(device)
    n_mlp = count_params(mlp)
    print(f"MLP: {n_mlp:,} params")
    mlp_path = os.path.join(SAVE_DIR, 'sudoku_mlp_lightweight_best.pt')

    t0 = time.time()
    mlp, mlp_hist = train_model(mlp, train_loader, val_loader, device,
                                 n_epochs=30, lr=1e-3, patience=8, save_path=mlp_path)
    mlp_time = time.time() - t0

    mlp_cell, mlp_grid = evaluate(mlp, test_loader, device)
    print(f"\nMLP Test: cell={mlp_cell:.4f} grid={mlp_grid:.4f} ({mlp_time:.0f}s)")

    all_results['mlp'] = {
        'params': n_mlp, 'test_cell_acc': mlp_cell, 'test_grid_acc': mlp_grid,
        'training_time_s': mlp_time, 'history': mlp_hist,
    }

    # ── CNN ────────────────────────────────────────────────────────────────
    print("\n" + "=" * 70)
    print("Training CNN (lightweight)")
    print("=" * 70)
    cnn = SudokuCNN(channels=64, n_blocks=4).to(device)
    n_cnn = count_params(cnn)
    print(f"CNN: {n_cnn:,} params")
    cnn_path = os.path.join(SAVE_DIR, 'sudoku_cnn_lightweight_best.pt')

    t0 = time.time()
    cnn, cnn_hist = train_model(cnn, train_loader, val_loader, device,
                                 n_epochs=30, lr=1e-3, patience=8, save_path=cnn_path)
    cnn_time = time.time() - t0

    cnn_cell, cnn_grid = evaluate(cnn, test_loader, device)
    print(f"\nCNN Test: cell={cnn_cell:.4f} grid={cnn_grid:.4f} ({cnn_time:.0f}s)")

    all_results['cnn'] = {
        'params': n_cnn, 'test_cell_acc': cnn_cell, 'test_grid_acc': cnn_grid,
        'training_time_s': cnn_time, 'history': cnn_hist,
    }

    # ── Summary ────────────────────────────────────────────────────────────
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"{'Model':<15} {'Params':>10} {'Cell Acc':>10} {'Grid Acc':>10} {'Size':>10}")
    print("-" * 60)
    for name, path in [('MLP', mlp_path), ('CNN', cnn_path)]:
        r = all_results[name.lower()]
        size = os.path.getsize(path) / 1024
        print(f"{name:<15} {r['params']:>10,} {r['test_cell_acc']:>9.1%} "
              f"{r['test_grid_acc']:>9.1%} {size:>8.0f}KB")

    with open(RESULTS_PATH, 'w') as f:
        json.dump(all_results, f, indent=2)
    print(f"\nResults saved to {RESULTS_PATH}")


if __name__ == '__main__':
    main()
