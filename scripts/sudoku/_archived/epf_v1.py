"""DEPRECATED — Archived 2026-04-28.
Superseded by: scripts/sudoku/core/ + scripts/sudoku/train_v4.py
Original: scripts/sudoku_epf_gpu_train.py
This file is kept for reference only. Do not use for new work.
"""

"""
Sudoku Neural Network - GPU Training Script
=============================================
EPF-style Conv2D stack (~7.6M params) trained on RTX 3070 with 1M puzzles.
Target: >=96.8% grid accuracy (matching EPF student model).

Architecture: Input(9,9,1) -> Conv2D(64,3x3)+BN+ReLU -> Conv2D(64,3x3)+BN+ReLU
             -> Conv2D(128,1x1)+ReLU -> Flatten -> Dense(729) -> Reshape(81,9) -> Softmax
Encoding: single-channel normalized (/9.0 - 0.5)

Dataset: nakashi104/sudoku-1million (HuggingFace) — 1M puzzles, ~47 empty cells/puzzle
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
    """Parse 81-char string into 9x9 int array."""
    return np.array([int(c) for c in s], dtype=np.int64).reshape(9, 9)


def load_sudoku_dataset(n_total=1_060_000):
    """Load sudoku dataset from HuggingFace with local caching.

    Uses nakashi104/sudoku-1million (1M puzzles, ~47 empty cells).
    Caches to npz for fast reloading.
    """
    SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', 'sudoku_models')
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
    print(f"Converting {n_use:,} puzzles to numpy arrays...")
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
class SudokuDataset(Dataset):
    def __init__(self, puzzles, solutions):
        # EPF-style encoding: single channel, normalized
        self.puzzles = (puzzles / 9.0 - 0.5).astype(np.float32)
        self.solutions = (solutions - 1).astype(np.int64)  # 0-8 for CrossEntropy

    def __len__(self):
        return len(self.puzzles)

    def __getitem__(self, idx):
        x = torch.tensor(self.puzzles[idx]).unsqueeze(0)  # (1, 9, 9)
        y = torch.tensor(self.solutions[idx]).view(-1)     # (81,)
        return x, y


# ── Model ─────────────────────────────────────────────────────────────────────
class EPFConvModel(nn.Module):
    """EPF student model architecture (~7.6M params).
    Conv2D stack -> Dense(729) -> Reshape(81,9) -> Softmax
    """
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
        # x: (B, 1, 9, 9)
        x = self.features(x)           # (B, 128, 9, 9)
        x = self.flatten(x)            # (B, 10368)
        x = self.fc(x)                 # (B, 729)
        x = x.view(-1, 81, 9)          # (B, 81, 9)
        return x                       # logits (no softmax — CrossEntropy handles it)


def count_params(model):
    return sum(p.numel() for p in model.parameters() if p.requires_grad)


# ── Evaluation ────────────────────────────────────────────────────────────────
def evaluate_one_shot(model, puzzles, solutions, device, batch_size=256):
    """One-shot evaluation: predict all 81 cells at once."""
    model.eval()
    n = len(puzzles)
    correct_cells = 0
    total_cells = 0
    solved_grids = 0

    with torch.no_grad():
        for i in range(0, n, batch_size):
            batch_p = puzzles[i:i+batch_size]
            batch_s = solutions[i:i+batch_size]

            x = torch.tensor((batch_p / 9.0 - 0.5).astype(np.float32)).unsqueeze(1).to(device)
            y = torch.tensor((batch_s - 1).astype(np.int64)).to(device)

            logits = model(x)  # (B, 81, 9)
            preds = logits.argmax(dim=-1)  # (B, 81)

            correct = (preds == y.view(preds.shape))
            correct_cells += correct.sum().item()
            total_cells += correct.numel()

            # Grid solved = all 81 cells correct
            grid_correct = correct.view(-1, 81).all(dim=1)
            solved_grids += grid_correct.sum().item()

    cell_acc = correct_cells / total_cells if total_cells > 0 else 0
    grid_acc = solved_grids / n if n > 0 else 0
    return cell_acc, grid_acc


def iterative_solve(model, puzzle, device, max_steps=5):
    """Iterative solving: predict, fill most confident, repeat."""
    model.eval()
    current = puzzle.copy()

    with torch.no_grad():
        for step in range(max_steps):
            x = torch.tensor((current / 9.0 - 0.5).astype(np.float32)).unsqueeze(0).unsqueeze(0).to(device)
            logits = model(x)  # (1, 81, 9)
            probs = torch.softmax(logits, dim=-1)  # (1, 81, 9)

            # Find empty cells
            empty_mask = (current == 0)
            if not empty_mask.any():
                break

            # Find most confident prediction among empty cells
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
            current[r][c] = best_val + 1  # back to 1-9

    return current


def evaluate_iterative(model, puzzles, solutions, device, n_eval=200, max_steps=5):
    """Evaluate with iterative solving."""
    model.eval()
    solved = 0
    correct_cells = 0
    total_cells = 0

    for i in range(min(n_eval, len(puzzles))):
        result = iterative_solve(model, puzzles[i], device, max_steps)
        target = solutions[i]

        correct = (result == target)
        correct_cells += correct.sum()
        total_cells += 81

        if correct.all():
            solved += 1

        if (i + 1) % 50 == 0:
            print(f"  Iterative: {i+1}/{min(n_eval, len(puzzles))}, solved so far: {solved}")

    cell_acc = correct_cells / total_cells if total_cells > 0 else 0
    grid_acc = solved / min(n_eval, len(puzzles))
    return cell_acc, grid_acc


# ── Data generation (fallback) ────────────────────────────────────────────────
def generate_sudoku_pair():
    """Generate a (solution, puzzle) pair — fallback if no dataset available."""
    def fill_grid(grid):
        for i in range(81):
            r, c = divmod(i, 9)
            if grid[r][c] == 0:
                nums = list(range(1, 10))
                np.random.shuffle(nums)
                for n in nums:
                    if (all(grid[r][j] != n for j in range(9)) and
                        all(grid[j][c] != n for j in range(9)) and
                        all(grid[r//3*3 + dr][c//3*3 + dc] != n
                            for dr in range(3) for dc in range(3))):
                        grid[r][c] = n
                        if fill_grid(grid):
                            return True
                        grid[r][c] = 0
                return False
        return True

    grid = [[0]*9 for _ in range(9)]
    fill_grid(grid)
    solution = np.array(grid, dtype=np.int64)

    puzzle = solution.copy()
    n_remove = np.random.randint(30, 51)
    indices = np.random.choice(81, n_remove, replace=False)
    for idx in indices:
        r, c = divmod(idx, 9)
        puzzle[r][c] = 0

    return puzzle, solution


# ── Training loop ─────────────────────────────────────────────────────────────
def train(model, train_loader, val_loader, device, n_epochs=100, patience=10,
          lr=1e-3, save_path='sudoku_epf_best.pt'):
    """Train with mixed precision, early stopping, ReduceLROnPlateau."""

    optimizer = optim.Adam(model.parameters(), lr=lr)
    scheduler = optim.lr_scheduler.ReduceLROnPlateau(
        optimizer, mode='min', factor=0.5, patience=5, min_lr=1e-6
    )
    criterion = nn.CrossEntropyLoss()
    scaler = GradScaler('cuda')

    best_val_loss = float('inf')
    best_epoch = 0
    patience_counter = 0
    history = []

    print(f"\nTraining for up to {n_epochs} epochs (patience={patience})")
    print(f"Mixed precision: FP16 autocast")
    print("-" * 70)

    for epoch in range(1, n_epochs + 1):
        # ── Train ──
        model.train()
        train_loss = 0
        train_correct = 0
        train_total = 0
        t0 = time.time()

        for batch_x, batch_y in train_loader:
            batch_x = batch_x.to(device)
            batch_y = batch_y.to(device)

            optimizer.zero_grad()

            with autocast('cuda'):
                logits = model(batch_x)  # (B, 81, 9)
                loss = criterion(logits.view(-1, 9), batch_y.view(-1))

            scaler.scale(loss).backward()
            scaler.step(optimizer)
            scaler.update()

            train_loss += loss.item() * batch_x.size(0)
            preds = logits.argmax(dim=-1)
            train_correct += (preds == batch_y.view(preds.shape)).sum().item()
            train_total += batch_y.numel()

        train_loss /= len(train_loader.dataset)
        train_acc = train_correct / train_total

        # ── Validate ──
        model.eval()
        val_loss = 0
        val_correct = 0
        val_total = 0

        with torch.no_grad():
            for batch_x, batch_y in val_loader:
                batch_x = batch_x.to(device)
                batch_y = batch_y.to(device)
                with autocast('cuda'):
                    logits = model(batch_x)
                    loss = criterion(logits.view(-1, 9), batch_y.view(-1))
                val_loss += loss.item() * batch_x.size(0)
                preds = logits.argmax(dim=-1)
                val_correct += (preds == batch_y.view(preds.shape)).sum().item()
                val_total += batch_y.numel()

        val_loss /= len(val_loader.dataset)
        val_acc = val_correct / val_total

        scheduler.step(val_loss)

        elapsed = time.time() - t0
        current_lr = optimizer.param_groups[0]['lr']

        print(f"Epoch {epoch:3d}/{n_epochs} | "
              f"train_loss={train_loss:.4f} acc={train_acc:.4f} | "
              f"val_loss={val_loss:.4f} acc={val_acc:.4f} | "
              f"lr={current_lr:.2e} | {elapsed:.1f}s")

        history.append({
            'epoch': epoch,
            'train_loss': train_loss,
            'train_acc': train_acc,
            'val_loss': val_loss,
            'val_acc': val_acc,
            'lr': current_lr,
        })

        # ── Checkpoint ──
        if val_loss < best_val_loss:
            best_val_loss = val_loss
            best_epoch = epoch
            patience_counter = 0
            torch.save({
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'optimizer_state_dict': optimizer.state_dict(),
                'val_loss': val_loss,
                'val_acc': val_acc,
            }, save_path)
            print(f"  -> Best model saved (val_loss={val_loss:.4f})")
        else:
            patience_counter += 1
            if patience_counter >= patience:
                print(f"\nEarly stopping at epoch {epoch}. Best: epoch {best_epoch} (val_loss={best_val_loss:.4f})")
                break

    # Load best model
    ckpt = torch.load(save_path, weights_only=False)
    model.load_state_dict(ckpt['model_state_dict'])
    print(f"Loaded best model from epoch {ckpt['epoch']} (val_loss={ckpt['val_loss']:.4f}, val_acc={ckpt['val_acc']:.4f})")

    return model, history


# ── Main ──────────────────────────────────────────────────────────────────────
def main():
    # ── Config ──
    N_TRAIN = 900_000
    N_VAL = 80_000
    N_TEST = 20_000
    BATCH_SIZE = 128
    N_EPOCHS = 150
    PATIENCE = 15
    LR = 1e-3
    SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', 'sudoku_models')
    os.makedirs(SAVE_DIR, exist_ok=True)
    SAVE_PATH = os.path.join(SAVE_DIR, 'sudoku_epf_best.pt')
    RESULTS_PATH = os.path.join(SAVE_DIR, 'training_results.json')

    print("=" * 70)
    print("Sudoku EPF-Style GPU Training")
    print(f"Config: {N_TRAIN:,} train / {N_VAL:,} val / {N_TEST:,} test")
    print(f"Batch: {BATCH_SIZE} | Epochs: {N_EPOCHS} | Patience: {PATIENCE} | LR: {LR}")
    print(f"Save: {SAVE_PATH}")
    print("=" * 70)

    # ── Load data from HuggingFace ──
    all_puzzles, all_solutions = load_sudoku_dataset(n_total=1_000_000)

    train_p = all_puzzles[:N_TRAIN]
    train_s = all_solutions[:N_TRAIN]
    val_p = all_puzzles[N_TRAIN:N_TRAIN+N_VAL]
    val_s = all_solutions[N_TRAIN:N_TRAIN+N_VAL]
    test_p = all_puzzles[N_TRAIN+N_VAL:]
    test_s = all_solutions[N_TRAIN+N_VAL:]

    del all_puzzles, all_solutions

    train_ds = SudokuDataset(train_p, train_s)
    val_ds = SudokuDataset(val_p, val_s)
    train_loader = DataLoader(train_ds, batch_size=BATCH_SIZE, shuffle=True, num_workers=0, pin_memory=True)
    val_loader = DataLoader(val_ds, batch_size=BATCH_SIZE, shuffle=False, num_workers=0, pin_memory=True)

    print(f"\nTrain: {len(train_ds):,} | Val: {len(val_ds):,}")

    # ── Model ──
    model = EPFConvModel().to(device)
    n_params = count_params(model)
    print(f"\nModel: EPFConvModel ({n_params:,} params)")
    print(model)

    # VRAM check
    if torch.cuda.is_available():
        vram_used = torch.cuda.memory_allocated(0) / 1e9
        vram_total = torch.cuda.get_device_properties(0).total_memory / 1e9
        print(f"VRAM: {vram_used:.2f} / {vram_total:.1f} GB (model loaded)")

    # ── Train ──
    t0_total = time.time()
    model, history = train(
        model, train_loader, val_loader, device,
        n_epochs=N_EPOCHS, patience=PATIENCE, lr=LR, save_path=SAVE_PATH
    )
    train_time = time.time() - t0_total
    print(f"\nTotal training time: {train_time:.1f}s ({train_time/60:.1f}min)")

    # ── Final evaluation ──
    print("\n" + "=" * 70)
    print("FINAL EVALUATION")
    print("=" * 70)

    # One-shot on test set
    print(f"\nOne-shot evaluation ({N_TEST:,} puzzles)...")
    os_cell, os_grid = evaluate_one_shot(model, test_p, test_s, device)
    print(f"One-shot: cell_acc={os_cell:.4f} | grid_acc={os_grid:.4f} ({int(os_grid*N_TEST)}/{N_TEST})")

    # Iterative on subset
    n_iter = min(500, N_TEST)
    print(f"\nIterative evaluation ({n_iter} puzzles, max_steps=5)...")
    iter_cell, iter_grid = evaluate_iterative(model, test_p, test_s, device, n_eval=n_iter)
    print(f"Iterative: cell_acc={iter_cell:.4f} | grid_acc={iter_grid:.4f} ({int(iter_grid*n_iter)}/{n_iter})")

    # ── Save results ──
    results = {
        'config': {
            'n_train': N_TRAIN, 'n_val': N_VAL, 'n_test': N_TEST,
            'batch_size': BATCH_SIZE, 'n_epochs': N_EPOCHS, 'patience': PATIENCE,
            'lr': LR, 'model_params': n_params,
            'dataset': 'nakashi104/sudoku-1million (HuggingFace)',
        },
        'one_shot': {'cell_acc': os_cell, 'grid_acc': os_grid},
        'iterative': {'cell_acc': iter_cell, 'grid_acc': iter_grid, 'n_eval': n_iter},
        'training_time_s': train_time,
        'history': history,
    }

    with open(RESULTS_PATH, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {RESULTS_PATH}")

    # ── Summary ──
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Model: EPFConvModel ({n_params:,} params)")
    print(f"Training: {N_TRAIN:,} puzzles, {history[-1]['epoch']} epochs, {train_time/60:.1f}min")
    print(f"One-shot grid accuracy: {os_grid*100:.1f}% ({int(os_grid*N_TEST)}/{N_TEST})")
    print(f"Iterative grid accuracy: {iter_grid*100:.1f}% ({int(iter_grid*n_iter)}/{n_iter})")
    target_met = "YES" if os_grid >= 0.968 or iter_grid >= 0.968 else "NO"
    print(f"Target >=96.8%: {target_met}")
    print("=" * 70)


if __name__ == '__main__':
    main()
