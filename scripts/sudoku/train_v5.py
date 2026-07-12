"""
Sudoku Neural Network - GPU Training Script V5 (Grokking Experiment)
====================================================================
Plain MLP with NO structural bias, trained to observe grokking.

Hypothesis: A plain MLP trained on a small Sudoku dataset will first
memorize (100% train, ~0% val), then undergo a phase transition to
generalization after extended training (grokking).

Setup:
- Architecture: Plain MLP (no graph, no message passing, no convolutions)
- Training data: 10K puzzles (deliberately small so model CAN memorize)
- Model: ~1M params (overparameterized relative to data)
- Weight decay: high (critical for grokking)
- Training: 1000+ epochs to observe phase transition

Expected behavior:
1. Phase 1 (memorization): Train acc -> 100%, val acc stays near 0%
2. Phase 2 (grokking): Val acc suddenly jumps to 80-95%+ after long plateau
3. The transition can take 100s-1000s of epochs

Reference: Power et al. (2022) "Grokking: Generalization of Overfitting
Neural Networks on Algorithmic Tasks"

Dataset: nakashi104/sudoku-1million (HuggingFace)
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
from torch.amp import GradScaler, autocast

# ── Device setup ──────────────────────────────────────────────────────────────
device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
print(f"Device: {device}")
if torch.cuda.is_available():
    print(f"GPU: {torch.cuda.get_device_name(0)}")
    print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB")
    torch.backends.cudnn.benchmark = True


# ── Dataset loading ──────────────────────────────────────────────────────────
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
        all_puzzles = data['puzzles']
        all_solutions = data['solutions']
        print(f"Loaded {len(all_puzzles):,} puzzles from cache")
        return all_puzzles, all_solutions

    from datasets import load_dataset
    print(f"Downloading nakashi104/sudoku-1million from HuggingFace...")
    ds = load_dataset('nakashi104/sudoku-1million', split='train')
    print(f"Downloaded {len(ds):,} puzzles")

    n_use = min(n_total, len(ds))
    all_puzzles = np.zeros((n_use, 9, 9), dtype=np.int64)
    all_solutions = np.zeros((n_use, 9, 9), dtype=np.int64)

    t0 = time.time()
    for i, row in enumerate(ds.select(range(n_use))):
        all_puzzles[i] = parse_81(row['quizzes'])
        all_solutions[i] = parse_81(row['solutions'])
        if (i + 1) % 100000 == 0:
            elapsed = time.time() - t0
            rate = (i + 1) / elapsed
            print(f"  {i+1:,}/{n_use:,} ({rate:.0f}/s)")

    elapsed = time.time() - t0
    print(f"Converted {n_use:,} puzzles in {elapsed:.1f}s")

    np.savez_compressed(p_cache, puzzles=all_puzzles, solutions=all_solutions)
    print(f"Cached to {p_cache}")
    return all_puzzles, all_solutions


# ── Dataset ───────────────────────────────────────────────────────────────────
class SudokuFlatDataset(Dataset):
    """Flat encoding: 81 cells x 10 features (9 one-hot digits + 1 is_given)."""

    def __init__(self, puzzles, solutions):
        n = len(puzzles)
        p_flat = puzzles.reshape(n, 81)
        s_flat = solutions.reshape(n, 81)
        self.x = np.zeros((n, 81, 10), dtype=np.float32)
        for d in range(1, 10):
            self.x[:, :, d - 1] = (p_flat == d).astype(np.float32)
        self.x[:, :, 9] = (p_flat > 0).astype(np.float32)
        self.y = (s_flat).astype(np.int64) - 1
        self.mask = (p_flat == 0).astype(np.float32)

    def __len__(self):
        return len(self.x)

    def __getitem__(self, idx):
        return (
            torch.tensor(self.x[idx]),
            torch.tensor(self.y[idx]),
            torch.tensor(self.mask[idx]),
        )


# ── Model ─────────────────────────────────────────────────────────────────────
class SudokuMLP(nn.Module):
    """Plain MLP for Sudoku — NO structural bias.

    Input(810) -> Dense(1024) -> ReLU -> Dense(1024) -> ReLU
              -> Dense(512) -> ReLU -> Dense(729) -> Reshape(81,9)
    """

    def __init__(self, hidden=1024, n_layers=4):
        super().__init__()
        layers = []
        in_dim = 81 * 10  # 810
        for _ in range(n_layers):
            layers.append(nn.Linear(in_dim, hidden))
            layers.append(nn.ReLU())
            in_dim = hidden
        layers.append(nn.Linear(hidden, 81 * 9))
        self.net = nn.Sequential(*layers)

    def forward(self, x):
        x = x.view(x.size(0), -1)  # (B, 810)
        x = self.net(x)  # (B, 729)
        return x.view(-1, 81, 9)


def count_params(model):
    return sum(p.numel() for p in model.parameters() if p.requires_grad)


# ── Evaluation ────────────────────────────────────────────────────────────────
def evaluate(model, loader, device):
    model.eval()
    correct_cells = 0
    total_cells = 0
    solved_grids = 0
    total_grids = 0

    with torch.no_grad():
        for batch_x, batch_y, batch_m in loader:
            batch_x = batch_x.to(device)
            batch_y = batch_y.to(device)
            batch_m = batch_m.to(device)

            with autocast('cuda'):
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


# ── Training loop ─────────────────────────────────────────────────────────────
def train_grokking(model, train_loader, val_loader, device, n_epochs=1000,
                   lr=1e-3, weight_decay=0.1, save_path='sudoku_mlp_grokking.pt'):
    optimizer = optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    scheduler = optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=n_epochs, eta_min=1e-6)
    criterion = nn.CrossEntropyLoss(reduction='none')
    scaler = GradScaler('cuda')

    best_val_acc = 0
    best_epoch = 0
    history = []

    print(f"\nGrokking experiment: {n_epochs} epochs, weight_decay={weight_decay}")
    print(f"Expecting: memorization phase -> grokking transition -> generalization")
    print("-" * 70)

    for epoch in range(1, n_epochs + 1):
        model.train()
        train_loss = 0
        t0 = time.time()

        for batch_x, batch_y, batch_m in train_loader:
            batch_x = batch_x.to(device)
            batch_y = batch_y.to(device)
            batch_m = batch_m.to(device)

            optimizer.zero_grad()
            with autocast('cuda'):
                logits = model(batch_x)
                per_cell_loss = criterion(logits.reshape(-1, 9), batch_y.reshape(-1))
                loss = (per_cell_loss * batch_m.reshape(-1)).sum() / batch_m.sum().clamp(min=1)

            scaler.scale(loss).backward()
            scaler.unscale_(optimizer)
            torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
            scaler.step(optimizer)
            scaler.update()

            train_loss += loss.item() * batch_x.size(0)

        train_loss /= len(train_loader.dataset)
        scheduler.step()

        # Evaluate every N epochs (save time)
        eval_interval = 5 if epoch <= 50 else (10 if epoch <= 200 else 25)
        if epoch % eval_interval == 0 or epoch <= 10:
            train_cell, train_grid = evaluate(model, train_loader, device)
            val_cell, val_grid = evaluate(model, val_loader, device)
            elapsed = time.time() - t0

            print(f"Epoch {epoch:4d}/{n_epochs} | "
                  f"loss={train_loss:.4f} | "
                  f"train_cell={train_cell:.4f} train_grid={train_grid:.4f} | "
                  f"val_cell={val_cell:.4f} val_grid={val_grid:.4f} | "
                  f"{elapsed:.1f}s")

            history.append({
                'epoch': epoch,
                'train_loss': train_loss,
                'train_cell_acc': train_cell,
                'train_grid_acc': train_grid,
                'val_cell_acc': val_cell,
                'val_grid_acc': val_grid,
            })

            if val_grid > best_val_acc:
                best_val_acc = val_grid
                best_epoch = epoch
                torch.save({
                    'epoch': epoch,
                    'model_state_dict': model.state_dict(),
                    'val_grid_acc': val_grid,
                    'val_cell_acc': val_cell,
                }, save_path)
                print(f"  -> Best model saved (val_grid={val_grid:.4f})")

            # Early exit if grokked perfectly
            if val_grid >= 0.95:
                print(f"\nGrokking achieved! val_grid_acc={val_grid:.4f} at epoch {epoch}")
        else:
            elapsed = time.time() - t0
            if epoch % 50 == 0:
                print(f"Epoch {epoch:4d}/{n_epochs} | loss={train_loss:.4f} | {elapsed:.1f}s")

    ckpt = torch.load(save_path, weights_only=False)
    model.load_state_dict(ckpt['model_state_dict'])
    print(f"\nLoaded best model from epoch {ckpt['epoch']} (val_grid={ckpt['val_grid_acc']:.4f})")

    return model, history


# ── Main ──────────────────────────────────────────────────────────────────────
def main():
    # Grokking params: small data, large model, high weight decay
    N_TRAIN = 10_000       # Small — model CAN memorize
    N_VAL = 10_000         # Val set from different distribution
    N_TEST = 10_000
    BATCH_SIZE = 256
    N_EPOCHS = 2000        # Long training to observe phase transition
    LR = 1e-3
    WEIGHT_DECAY = 0.1     # High — critical for grokking
    HIDDEN = 1024
    N_LAYERS = 4

    SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')
    os.makedirs(SAVE_DIR, exist_ok=True)
    SAVE_PATH = os.path.join(SAVE_DIR, 'sudoku_mlp_grokking_best.pt')
    RESULTS_PATH = os.path.join(SAVE_DIR, 'training_results_v5_grokking.json')

    print("=" * 70)
    print("Sudoku Grokking Experiment V5")
    print(f"Plain MLP — NO graph structure, NO message passing")
    print(f"Config: {N_TRAIN:,} train / {N_VAL:,} val / {N_TEST:,} test")
    print(f"Model: {N_LAYERS}x Dense({HIDDEN}) | weight_decay={WEIGHT_DECAY}")
    print(f"Epochs: {N_EPOCHS} | LR: {LR}")
    print("=" * 70)

    all_puzzles, all_solutions = load_sudoku_dataset(n_total=1_000_000)

    # Random split (no curriculum — no structural advantage)
    n_givens = (all_puzzles > 0).sum(axis=1)
    valid = n_givens >= 17
    all_puzzles = all_puzzles[valid]
    all_solutions = all_solutions[valid]

    np.random.seed(42)
    perm = np.random.permutation(len(all_puzzles))
    all_puzzles = all_puzzles[perm]
    all_solutions = all_solutions[perm]

    train_p = all_puzzles[:N_TRAIN]
    train_s = all_solutions[:N_TRAIN]
    val_p = all_puzzles[N_TRAIN:N_TRAIN + N_VAL]
    val_s = all_solutions[N_TRAIN:N_TRAIN + N_VAL]
    test_p = all_puzzles[N_TRAIN + N_VAL:N_TRAIN + N_VAL + N_TEST]
    test_s = all_solutions[N_TRAIN + N_VAL:N_TRAIN + N_VAL + N_TEST]

    del all_puzzles, all_solutions

    train_ds = SudokuFlatDataset(train_p, train_s)
    val_ds = SudokuFlatDataset(val_p, val_s)
    test_ds = SudokuFlatDataset(test_p, test_s)
    train_loader = DataLoader(train_ds, batch_size=BATCH_SIZE, shuffle=True, num_workers=0, pin_memory=True)
    val_loader = DataLoader(val_ds, batch_size=BATCH_SIZE, shuffle=False, num_workers=0, pin_memory=True)
    test_loader = DataLoader(test_ds, batch_size=BATCH_SIZE, shuffle=False, num_workers=0, pin_memory=True)

    print(f"\nTrain: {len(train_ds):,} | Val: {len(val_ds):,} | Test: {len(test_ds):,}")

    model = SudokuMLP(hidden=HIDDEN, n_layers=N_LAYERS).to(device)
    n_params = count_params(model)
    print(f"\nModel: SudokuMLP ({n_params:,} params)")
    print(model)

    t0_total = time.time()
    model, history = train_grokking(
        model, train_loader, val_loader, device,
        n_epochs=N_EPOCHS, lr=LR, weight_decay=WEIGHT_DECAY, save_path=SAVE_PATH,
    )
    train_time = time.time() - t0_total
    print(f"\nTotal training time: {train_time:.1f}s ({train_time/60:.1f}min)")

    # Final test evaluation
    print("\n" + "=" * 70)
    print("FINAL TEST EVALUATION")
    print("=" * 70)
    test_cell, test_grid = evaluate(model, test_loader, device)
    print(f"Test: cell_acc={test_cell:.4f} | grid_acc={test_grid:.4f}")

    # Analyze grokking transition
    grokked = False
    grokking_epoch = None
    for h in history:
        if h['val_grid_acc'] > 0.5:
            grokked = True
            grokking_epoch = h['epoch']
            break

    results = {
        'config': {
            'n_train': N_TRAIN, 'n_val': N_VAL, 'n_test': N_TEST,
            'batch_size': BATCH_SIZE, 'n_epochs': N_EPOCHS,
            'lr': LR, 'weight_decay': WEIGHT_DECAY,
            'hidden': HIDDEN, 'n_layers': N_LAYERS,
            'model_params': n_params,
            'architecture': 'Plain MLP (no structural bias)',
            'experiment': 'Grokking',
        },
        'test': {'cell_acc': test_cell, 'grid_acc': test_grid},
        'grokking': {
            'observed': grokked,
            'transition_epoch': grokking_epoch,
        },
        'training_time_s': train_time,
        'history': history,
    }

    with open(RESULTS_PATH, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {RESULTS_PATH}")

    print("\n" + "=" * 70)
    print("GROKKING SUMMARY")
    print("=" * 70)
    print(f"Model: Plain MLP ({n_params:,} params, no graph structure)")
    print(f"Data: {N_TRAIN:,} puzzles (overparameterized)")
    print(f"Training: {history[-1]['epoch'] if history else 0} epochs, {train_time/60:.1f}min")
    if grokked:
        print(f"Grokking: YES — transition at epoch {grokking_epoch}")
    else:
        print(f"Grokking: NOT observed in {N_EPOCHS} epochs")
    print(f"Test grid accuracy: {test_grid*100:.1f}%")
    print(f"Test cell accuracy: {test_cell*100:.1f}%")
    print("=" * 70)


if __name__ == '__main__':
    main()
