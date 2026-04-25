"""
Sudoku Neural Network - GPU Training Script V3 (Deep Residual)
==============================================================
Deep ResNet-style Conv2D architecture with masked loss.
Target: >=96.8% grid accuracy (matching EPF student model).

Architecture: Input(9,9,1) -> Conv(64,3x3) -> [ResBlock x 8] -> Conv(512,1x1)
             -> Flatten -> Dense(729) -> Reshape(81,9) -> Softmax
Encoding: single-channel normalized (/9.0 - 0.5)

Key improvements over V2:
- 8 residual blocks with skip connections (depth without vanishing gradients)
- Wider feature maps (64 -> 128 in later blocks)
- OneCycleLR scheduler for faster convergence
- Masked loss on empty cells only

Dataset: nakashi104/sudoku-1million (HuggingFace) - 1M puzzles, ~47 empty cells/puzzle
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
        self.puzzles = (puzzles / 9.0 - 0.5).astype(np.float32)
        self.solutions = (solutions - 1).astype(np.int64)
        self.masks = (puzzles == 0).astype(np.float32)

    def __len__(self):
        return len(self.puzzles)

    def __getitem__(self, idx):
        x = torch.tensor(self.puzzles[idx]).unsqueeze(0)
        y = torch.tensor(self.solutions[idx]).view(-1)
        m = torch.tensor(self.masks[idx]).view(-1)
        return x, y, m


# ── Model ─────────────────────────────────────────────────────────────────────
class ResBlock(nn.Module):
    """Residual block: Conv-BN-ReLU-Conv-BN + skip connection."""
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
    """Deep ResNet for Sudoku (~2.4M params, 8 residual blocks).

    Input(1,9,9) -> Conv(64) -> ResBlock x4 -> Conv(128) -> ResBlock x4
    -> Conv(512,1x1) -> Flatten -> Dense(729) -> Reshape(81,9)
    """
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
        x = self.stem(x)        # (B, 64, 9, 9)
        x = self.res1(x)        # (B, 64, 9, 9)
        x = self.transition(x)  # (B, 128, 9, 9)
        x = self.res2(x)        # (B, 128, 9, 9)
        x = self.head_conv(x)   # (B, 512, 9, 9)
        x = self.flatten(x)     # (B, 41472)
        x = self.fc(x)          # (B, 729)
        x = x.view(-1, 81, 9)  # (B, 81, 9)
        return x


def count_params(model):
    return sum(p.numel() for p in model.parameters() if p.requires_grad)


# ── Evaluation ────────────────────────────────────────────────────────────────
def evaluate_one_shot(model, puzzles, solutions, device, batch_size=256):
    model.eval()
    n = len(puzzles)
    correct_cells_full = 0
    correct_cells_empty = 0
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

            logits = model(x)
            preds = logits.argmax(dim=-1)

            correct = (preds == y.view(preds.shape))
            correct_cells_full += correct.sum().item()
            total_cells += correct.numel()

            correct_empty = correct.float() * empty.view(correct.shape)
            correct_cells_empty += correct_empty.sum().item()
            total_empty += empty.sum().item()

            grid_correct = correct.view(-1, 81).all(dim=1)
            solved_grids += grid_correct.sum().item()

    cell_acc = correct_cells_full / total_cells if total_cells > 0 else 0
    empty_acc = correct_cells_empty / total_empty if total_empty > 0 else 0
    grid_acc = solved_grids / n if n > 0 else 0
    return cell_acc, grid_acc, empty_acc


def iterative_solve(model, puzzle, device, max_steps=10):
    model.eval()
    current = puzzle.copy()

    with torch.no_grad():
        for step in range(max_steps):
            empty_mask = (current == 0)
            if not empty_mask.any():
                break

            x = torch.tensor((current / 9.0 - 0.5).astype(np.float32)).unsqueeze(0).unsqueeze(0).to(device)
            logits = model(x)
            probs = torch.softmax(logits, dim=-1)

            # Fill ALL cells with confidence > threshold in batch
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

    return current


def evaluate_iterative(model, puzzles, solutions, device, n_eval=500, max_steps=10):
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

        if (i + 1) % 100 == 0:
            print(f"  Iterative: {i+1}/{min(n_eval, len(puzzles))}, solved so far: {solved}")

    cell_acc = correct_cells / total_cells if total_cells > 0 else 0
    grid_acc = solved / min(n_eval, len(puzzles))
    return cell_acc, grid_acc


# ── Training loop ─────────────────────────────────────────────────────────────
def train(model, train_loader, val_loader, device, n_epochs=100, patience=15,
          lr=1e-3, save_path='sudoku_resnet_best.pt'):
    optimizer = optim.Adam(model.parameters(), lr=lr, weight_decay=1e-4)
    scheduler = optim.lr_scheduler.OneCycleLR(
        optimizer, max_lr=lr, epochs=n_epochs,
        steps_per_epoch=len(train_loader), pct_start=0.1
    )
    criterion = nn.CrossEntropyLoss(reduction='none')
    scaler = GradScaler('cuda')

    best_val_loss = float('inf')
    best_epoch = 0
    best_val_acc = 0
    patience_counter = 0
    history = []

    print(f"\nTraining for up to {n_epochs} epochs (patience={patience})")
    print(f"Mixed precision: FP16 autocast")
    print(f"Masked loss: only empty cells contribute to loss")
    print(f"Scheduler: OneCycleLR (max_lr={lr})")
    print("-" * 70)

    for epoch in range(1, n_epochs + 1):
        model.train()
        train_loss = 0
        train_correct = 0
        train_total = 0
        t0 = time.time()

        for batch_x, batch_y, batch_m in train_loader:
            batch_x = batch_x.to(device)
            batch_y = batch_y.to(device)
            batch_m = batch_m.to(device)

            optimizer.zero_grad()

            with autocast('cuda'):
                logits = model(batch_x)
                per_cell_loss = criterion(logits.view(-1, 9), batch_y.view(-1))
                loss = (per_cell_loss * batch_m.view(-1)).sum() / batch_m.sum().clamp(min=1)

            scaler.scale(loss).backward()
            scaler.unscale_(optimizer)
            torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
            scaler.step(optimizer)
            scaler.update()
            scheduler.step()

            train_loss += loss.item() * batch_x.size(0)
            preds = logits.argmax(dim=-1)
            correct = (preds == batch_y.view(preds.shape)).float() * batch_m.view(preds.shape)
            train_correct += correct.sum().item()
            train_total += batch_m.sum().item()

        train_loss /= len(train_loader.dataset)
        train_acc = train_correct / train_total if train_total > 0 else 0

        model.eval()
        val_loss = 0
        val_correct = 0
        val_total = 0

        with torch.no_grad():
            for batch_x, batch_y, batch_m in val_loader:
                batch_x = batch_x.to(device)
                batch_y = batch_y.to(device)
                batch_m = batch_m.to(device)
                with autocast('cuda'):
                    logits = model(batch_x)
                    per_cell_loss = criterion(logits.view(-1, 9), batch_y.view(-1))
                    loss = (per_cell_loss * batch_m.view(-1)).sum() / batch_m.sum().clamp(min=1)
                val_loss += loss.item() * batch_x.size(0)
                preds = logits.argmax(dim=-1)
                correct = (preds == batch_y.view(preds.shape)).float() * batch_m.view(preds.shape)
                val_correct += correct.sum().item()
                val_total += batch_m.sum().item()

        val_loss /= len(val_loader.dataset)
        val_acc = val_correct / val_total if val_total > 0 else 0

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

        if val_loss < best_val_loss:
            best_val_loss = val_loss
            best_val_acc = val_acc
            best_epoch = epoch
            patience_counter = 0
            torch.save({
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'optimizer_state_dict': optimizer.state_dict(),
                'val_loss': val_loss,
                'val_acc': val_acc,
            }, save_path)
            print(f"  -> Best model saved (val_loss={val_loss:.4f}, val_acc={val_acc:.4f})")
        else:
            patience_counter += 1
            if patience_counter >= patience:
                print(f"\nEarly stopping at epoch {epoch}. Best: epoch {best_epoch} (val_loss={best_val_loss:.4f})")
                break

    ckpt = torch.load(save_path, weights_only=False)
    model.load_state_dict(ckpt['model_state_dict'])
    print(f"Loaded best model from epoch {ckpt['epoch']} (val_loss={ckpt['val_loss']:.4f}, val_acc={ckpt['val_acc']:.4f})")

    return model, history


# ── Main ──────────────────────────────────────────────────────────────────────
def main():
    N_TRAIN = 900_000
    N_VAL = 80_000
    N_TEST = 20_000
    BATCH_SIZE = 256
    N_EPOCHS = 100
    PATIENCE = 12
    LR = 3e-3
    SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', 'sudoku_models')
    os.makedirs(SAVE_DIR, exist_ok=True)
    SAVE_PATH = os.path.join(SAVE_DIR, 'sudoku_resnet_v3_best.pt')
    RESULTS_PATH = os.path.join(SAVE_DIR, 'training_results_v3.json')

    print("=" * 70)
    print("Sudoku Deep ResNet GPU Training V3")
    print(f"Config: {N_TRAIN:,} train / {N_VAL:,} val / {N_TEST:,} test")
    print(f"Batch: {BATCH_SIZE} | Epochs: {N_EPOCHS} | Patience: {PATIENCE} | LR: {LR}")
    print(f"Save: {SAVE_PATH}")
    print("=" * 70)

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

    model = SudokuResNet().to(device)
    n_params = count_params(model)
    print(f"\nModel: SudokuResNet ({n_params:,} params)")
    print(model)

    if torch.cuda.is_available():
        vram_used = torch.cuda.memory_allocated(0) / 1e9
        vram_total = torch.cuda.get_device_properties(0).total_memory / 1e9
        print(f"VRAM: {vram_used:.2f} / {vram_total:.1f} GB (model loaded)")

    t0_total = time.time()
    model, history = train(
        model, train_loader, val_loader, device,
        n_epochs=N_EPOCHS, patience=PATIENCE, lr=LR, save_path=SAVE_PATH
    )
    train_time = time.time() - t0_total
    print(f"\nTotal training time: {train_time:.1f}s ({train_time/60:.1f}min)")

    print("\n" + "=" * 70)
    print("FINAL EVALUATION")
    print("=" * 70)

    print(f"\nOne-shot evaluation ({N_TEST:,} puzzles)...")
    os_cell, os_grid, os_empty = evaluate_one_shot(model, test_p, test_s, device)
    print(f"One-shot: cell_acc={os_cell:.4f} | empty_acc={os_empty:.4f} | grid_acc={os_grid:.4f} ({int(os_grid*N_TEST)}/{N_TEST})")

    n_iter = min(500, N_TEST)
    print(f"\nIterative evaluation ({n_iter} puzzles, max_steps=10)...")
    iter_cell, iter_grid = evaluate_iterative(model, test_p, test_s, device, n_eval=n_iter)
    print(f"Iterative: cell_acc={iter_cell:.4f} | grid_acc={iter_grid:.4f} ({int(iter_grid*n_iter)}/{n_iter})")

    results = {
        'config': {
            'n_train': N_TRAIN, 'n_val': N_VAL, 'n_test': N_TEST,
            'batch_size': BATCH_SIZE, 'n_epochs': N_EPOCHS, 'patience': PATIENCE,
            'lr': LR, 'model_params': n_params,
            'architecture': 'SudokuResNet (8 ResBlocks, 64/128 channels)',
            'dataset': 'nakashi104/sudoku-1million (HuggingFace)',
        },
        'one_shot': {'cell_acc': os_cell, 'grid_acc': os_grid, 'empty_acc': os_empty},
        'iterative': {'cell_acc': iter_cell, 'grid_acc': iter_grid, 'n_eval': n_iter},
        'training_time_s': train_time,
        'history': history,
    }

    with open(RESULTS_PATH, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {RESULTS_PATH}")

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Model: SudokuResNet ({n_params:,} params)")
    print(f"Training: {N_TRAIN:,} puzzles, {history[-1]['epoch']} epochs, {train_time/60:.1f}min")
    print(f"One-shot grid accuracy: {os_grid*100:.1f}% ({int(os_grid*N_TEST)}/{N_TEST})")
    print(f"One-shot empty-cell accuracy: {os_empty*100:.1f}%")
    print(f"Iterative grid accuracy: {iter_grid*100:.1f}% ({int(iter_grid*n_iter)}/{n_iter})")
    target_met = "YES" if os_grid >= 0.968 or iter_grid >= 0.968 else "NO"
    print(f"Target >=96.8%: {target_met}")
    print("=" * 70)


if __name__ == '__main__':
    main()
