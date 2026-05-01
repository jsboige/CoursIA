"""DEPRECATED — Archived 2026-04-28.
Superseded by: scripts/sudoku/core/ + scripts/sudoku/train_v4.py
Original: scripts/sudoku_epf_experiment.py
This file is kept for reference only. Do not use for new work.
"""

"""
Standalone experiment: EPF-inspired architecture for Sudoku solving.

Tests whether the EPF student model architecture (Conv+BN+Conv+BN+Conv+Dense)
outperforms our current ResCNN on the same training data.

Two phases:
1. Quick test with 50K data (current notebook amount) to validate architecture
2. Full test with 200K data to reach target performance
"""

import os
import sys
import time
import numpy as np
import random

# Force CPU (no CUDA on this machine)
os.environ["CUDA_VISIBLE_DEVICES"] = ""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader

# Unbuffered output
sys.stdout.reconfigure(line_buffering=True)

DEVICE = torch.device("cpu")
print(f"Device: {DEVICE}")
print(f"PyTorch: {torch.__version__}")
print(f"CPU threads: {torch.get_num_threads()}")
torch.set_num_threads(8)

# ============================================================
# Sudoku puzzle generation (copied from notebook)
# ============================================================

def is_valid(board, row, col, num):
    for j in range(9):
        if board[row][j] == num:
            return False
    for i in range(9):
        if board[i][col] == num:
            return False
    box_row, box_col = 3 * (row // 3), 3 * (col // 3)
    for i in range(box_row, box_row + 3):
        for j in range(box_col, box_col + 3):
            if board[i][j] == num:
                return False
    return True

def solve_random(board):
    empty = None
    for i in range(9):
        for j in range(9):
            if board[i][j] == 0:
                empty = (i, j)
                break
        if empty:
            break
    if not empty:
        return True
    row, col = empty
    nums = list(range(1, 10))
    random.shuffle(nums)
    for num in nums:
        if is_valid(board, row, col, num):
            board[row][col] = num
            if solve_random(board):
                return True
            board[row][col] = 0
    return False

def generate_puzzle(min_clues=30):
    board = [[0]*9 for _ in range(9)]
    solve_random(board)
    solution = np.array(board, dtype=np.int64).copy()
    puzzle = solution.copy()
    cells = [(i, j) for i in range(9) for j in range(9)]
    random.shuffle(cells)
    to_remove = 81 - min_clues
    removed = 0
    for i, j in cells:
        if removed >= to_remove:
            break
        puzzle[i][j] = 0
        removed += 1
    return puzzle, solution

def generate_dataset(n, min_clues=30):
    puzzles, solutions = [], []
    for i in range(n):
        if (i+1) % 10000 == 0:
            print(f"  Generated {i+1}/{n} puzzles...")
        p, s = generate_puzzle(min_clues)
        puzzles.append(p)
        solutions.append(s)
    return np.array(puzzles), np.array(solutions)

# ============================================================
# Encoding functions
# ============================================================

def encode_epf(puzzle):
    """EPF-style single-channel normalized encoding: /9 - 0.5"""
    return (puzzle / 9.0 - 0.5).astype(np.float32)

def encode_onehot(puzzle):
    """Current notebook one-hot encoding (10 channels)"""
    onehot = np.zeros((10, 9, 9), dtype=np.float32)
    for i in range(9):
        for j in range(9):
            val = int(puzzle[i][j])
            onehot[val][i][j] = 1.0
    return onehot

# ============================================================
# Models
# ============================================================

class EPFModel(nn.Module):
    """EPF student architecture in PyTorch: Conv+BN -> Conv+BN -> Conv -> Dense(729)"""
    def __init__(self):
        super().__init__()
        self.features = nn.Sequential(
            nn.Conv2d(1, 64, 3, padding=1),
            nn.BatchNorm2d(64),
            nn.ReLU(inplace=True),
            nn.Conv2d(64, 64, 3, padding=1),
            nn.BatchNorm2d(64),
            nn.ReLU(inplace=True),
            nn.Conv2d(64, 128, 1),
            nn.ReLU(inplace=True),
        )
        self.flatten = nn.Flatten()
        self.fc = nn.Linear(128 * 9 * 9, 9 * 9 * 9)

    def forward(self, x):
        x = self.features(x)
        x = self.flatten(x)
        x = self.fc(x)
        x = x.view(-1, 9, 9, 9)
        return x

class EPFModelDeep(nn.Module):
    """Deeper variant: 4 conv layers + Dense, closer to state-of-art"""
    def __init__(self):
        super().__init__()
        self.features = nn.Sequential(
            nn.Conv2d(1, 128, 3, padding=1),
            nn.BatchNorm2d(128),
            nn.ReLU(inplace=True),
            nn.Conv2d(128, 128, 3, padding=1),
            nn.BatchNorm2d(128),
            nn.ReLU(inplace=True),
            nn.Conv2d(128, 256, 3, padding=1),
            nn.BatchNorm2d(256),
            nn.ReLU(inplace=True),
            nn.Conv2d(256, 512, 1),
            nn.ReLU(inplace=True),
        )
        self.flatten = nn.Flatten()
        self.fc = nn.Linear(512 * 9 * 9, 9 * 9 * 9)

    def forward(self, x):
        x = self.features(x)
        x = self.flatten(x)
        x = self.fc(x)
        x = x.view(-1, 9, 9, 9)
        return x

# ============================================================
# Dataset
# ============================================================

class SudokuDatasetEPF(Dataset):
    def __init__(self, puzzles, solutions):
        self.puzzles = puzzles
        self.solutions = solutions

    def __len__(self):
        return len(self.puzzles)

    def __getitem__(self, idx):
        x = encode_epf(self.puzzles[idx])
        y = self.solutions[idx] - 1  # 0-indexed classes
        x = torch.tensor(x).unsqueeze(0)  # (1, 9, 9)
        y = torch.tensor(y, dtype=torch.long)
        return x, y

# ============================================================
# Training
# ============================================================

def train_model(model, train_loader, val_loader, n_epochs=30, lr=0.001, patience=5):
    model.to(DEVICE)
    optimizer = torch.optim.Adam(model.parameters(), lr=lr)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=n_epochs)
    criterion = nn.CrossEntropyLoss()

    best_val_loss = float('inf')
    best_state = None
    patience_counter = 0

    for epoch in range(n_epochs):
        model.train()
        train_loss = 0
        train_correct = 0
        train_total = 0

        for batch_x, batch_y in train_loader:
            batch_x, batch_y = batch_x.to(DEVICE), batch_y.to(DEVICE)
            optimizer.zero_grad()
            output = model(batch_x)  # (B, 9, 9, 9)
            loss = criterion(output.view(-1, 9), batch_y.view(-1))
            loss.backward()
            optimizer.step()

            train_loss += loss.item() * batch_x.size(0)
            preds = output.argmax(dim=-1)  # (B, 9, 9)
            train_correct += (preds == batch_y).sum().item()
            train_total += batch_y.numel()

        scheduler.step()

        model.eval()
        val_loss = 0
        val_correct = 0
        val_total = 0
        with torch.no_grad():
            for batch_x, batch_y in val_loader:
                batch_x, batch_y = batch_x.to(DEVICE), batch_y.to(DEVICE)
                output = model(batch_x)
                loss = criterion(output.view(-1, 9), batch_y.view(-1))
                val_loss += loss.item() * batch_x.size(0)
                preds = output.argmax(dim=-1)
                val_correct += (preds == batch_y).sum().item()
                val_total += batch_y.numel()

        train_loss /= len(train_loader.dataset)
        val_loss /= len(val_loader.dataset)
        train_acc = train_correct / train_total
        val_acc = val_correct / val_total

        print(f"  Epoch {epoch+1:3d}/{n_epochs}: "
              f"train_loss={train_loss:.4f} acc={train_acc:.4f} | "
              f"val_loss={val_loss:.4f} acc={val_acc:.4f}")

        if val_loss < best_val_loss:
            best_val_loss = val_loss
            best_state = {k: v.clone() for k, v in model.state_dict().items()}
            patience_counter = 0
        else:
            patience_counter += 1
            if patience_counter >= patience:
                print(f"  Early stopping at epoch {epoch+1}")
                break

    if best_state:
        model.load_state_dict(best_state)
    return model, best_val_loss

# ============================================================
# Evaluation
# ============================================================

def evaluate_model(model, puzzles, solutions, n_eval=500, batch_size=64):
    """Evaluate one-shot prediction accuracy."""
    model.eval()
    model.to(DEVICE)

    n = min(n_eval, len(puzzles))
    cell_correct = 0
    cell_total = 0
    grid_correct = 0

    with torch.no_grad():
        for i in range(0, n, batch_size):
            batch_p = puzzles[i:i+batch_size]
            batch_s = solutions[i:i+batch_size]
            batch_x = torch.tensor(
                np.array([encode_epf(p) for p in batch_p]), dtype=torch.float32
            ).unsqueeze(1).to(DEVICE)
            output = model(batch_x)
            preds = output.argmax(dim=-1).cpu().numpy() + 1  # 1-indexed

            for j in range(len(batch_p)):
                sol = batch_s[j]
                pred = preds[j]
                match = (pred == sol)
                cell_correct += match.sum()
                cell_total += 81
                if match.all():
                    grid_correct += 1

    cell_acc = cell_correct / cell_total if cell_total > 0 else 0
    grid_acc = grid_correct / n if n > 0 else 0
    return cell_acc, grid_acc, grid_correct

def iterative_predict(model, puzzle, max_iter=81):
    """Iteratively fill cells one at a time."""
    model.eval()
    board = puzzle.copy().astype(np.float32)

    for _ in range(max_iter):
        x = torch.tensor(encode_epf(board)).unsqueeze(0).unsqueeze(0).to(DEVICE)
        with torch.no_grad():
            output = model(x)
            probs = F.softmax(output.squeeze(0), dim=-1)  # (9, 9, 9)

        best_conf = -1
        best_pos = None
        best_val = None

        for i in range(9):
            for j in range(9):
                if board[i][j] == 0:
                    cell_probs = probs[i][j]
                    conf, val = cell_probs.max(dim=0)
                    conf = conf.item()
                    if conf > best_conf:
                        best_conf = conf
                        best_pos = (i, j)
                        best_val = val.item() + 1

        if best_pos is None:
            break

        board[best_pos[0]][best_pos[1]] = best_val

    return board.astype(np.int64)

def evaluate_iterative(model, puzzles, solutions, n_eval=200):
    """Evaluate with iterative prediction."""
    model.eval()
    model.to(DEVICE)

    n = min(n_eval, len(puzzles))
    grid_correct = 0
    cell_correct = 0
    cell_total = 0

    for idx in range(n):
        if (idx+1) % 50 == 0:
            print(f"    Iterative eval: {idx+1}/{n}...")
        pred = iterative_predict(model, puzzles[idx])
        sol = solutions[idx]
        match = (pred == sol)
        cell_correct += match.sum()
        cell_total += 81
        if match.all():
            grid_correct += 1

    cell_acc = cell_correct / cell_total if cell_total > 0 else 0
    grid_acc = grid_correct / n if n > 0 else 0
    return cell_acc, grid_acc, grid_correct

# ============================================================
# Main experiment
# ============================================================

def run_experiment():
    print("=" * 60)
    print("EPF-Inspired Sudoku Solver Experiment")
    print("=" * 60)

    # Phase 1: Quick validation with 50K data (match notebook)
    N_TRAIN_Q = 45000
    N_TEST_Q = 5000
    N_TOTAL_Q = N_TRAIN_Q + N_TEST_Q

    print(f"\n--- Phase 1: Quick validation ({N_TOTAL_Q:,} data) ---")
    print(f"Generating {N_TOTAL_Q} puzzles...")
    t0 = time.time()
    all_puzzles_q, all_solutions_q = generate_dataset(N_TOTAL_Q, min_clues=30)
    print(f"  Generated in {time.time()-t0:.1f}s")

    train_p_q = all_puzzles_q[:N_TRAIN_Q]
    train_s_q = all_solutions_q[:N_TRAIN_Q]
    test_p_q = all_puzzles_q[N_TRAIN_Q:]
    test_s_q = all_solutions_q[N_TRAIN_Q:]

    train_ds_q = SudokuDatasetEPF(train_p_q, train_s_q)
    test_ds_q = SudokuDatasetEPF(test_p_q, test_s_q)
    train_loader_q = DataLoader(train_ds_q, batch_size=128, shuffle=True, num_workers=0)
    val_loader_q = DataLoader(test_ds_q, batch_size=256, shuffle=False, num_workers=0)

    # Quick test: EPF architecture with 50K data, 20 epochs
    print("\n--- Phase 1a: EPF Original (50K data, 20 epochs) ---")
    model_epf_q = EPFModel()
    n_params = sum(p.numel() for p in model_epf_q.parameters())
    print(f"Parameters: {n_params:,}")

    t0 = time.time()
    model_epf_q, _ = train_model(model_epf_q, train_loader_q, val_loader_q, n_epochs=20, lr=0.001, patience=5)
    print(f"Training time: {time.time()-t0:.1f}s")

    cell_q, grid_q, grids_q = evaluate_model(model_epf_q, test_p_q, test_s_q, n_eval=1000)
    print(f"\nOne-shot (1000 puzzles): cell={cell_q*100:.1f}% grid={grid_q*100:.1f}% ({grids_q}/1000)")

    cell_qi, grid_qi, grids_qi = evaluate_iterative(model_epf_q, test_p_q, test_s_q, n_eval=100)
    print(f"Iterative (100 puzzles): cell={cell_qi*100:.1f}% grid={grid_qi*100:.1f}% ({grids_qi}/100)")

    # Phase 2: Full experiment with 200K data
    N_TRAIN = 180000
    N_TEST = 20000
    N_TOTAL = N_TRAIN + N_TEST

    print(f"\n--- Phase 2: Full experiment ({N_TOTAL:,} data) ---")
    print(f"Generating {N_TOTAL} puzzles...")
    t0 = time.time()
    all_puzzles, all_solutions = generate_dataset(N_TOTAL, min_clues=30)
    print(f"  Generated in {time.time()-t0:.1f}s")

    train_p = all_puzzles[:N_TRAIN]
    train_s = all_solutions[:N_TRAIN]
    test_p = all_puzzles[N_TRAIN:]
    test_s = all_solutions[N_TRAIN:]

    print(f"  Train: {len(train_p)}, Test: {len(test_p)}")

    train_ds = SudokuDatasetEPF(train_p, train_s)
    test_ds = SudokuDatasetEPF(test_p, test_s)
    train_loader = DataLoader(train_ds, batch_size=128, shuffle=True, num_workers=0)
    val_loader = DataLoader(test_ds, batch_size=256, shuffle=False, num_workers=0)

    # Experiment 1: EPF original architecture
    print("\n" + "=" * 60)
    print("Experiment 1: EPF Original (7.6M params)")
    print("=" * 60)
    model_epf = EPFModel()
    n_params = sum(p.numel() for p in model_epf.parameters())
    print(f"Parameters: {n_params:,}")

    t0 = time.time()
    model_epf, best_loss = train_model(model_epf, train_loader, val_loader, n_epochs=30, lr=0.001, patience=7)
    print(f"Training time: {time.time()-t0:.1f}s")

    cell_acc, grid_acc, grids = evaluate_model(model_epf, test_p, test_s, n_eval=1000)
    print(f"\nOne-shot evaluation (1000 puzzles):")
    print(f"  Cell accuracy: {cell_acc:.4f} ({cell_acc*100:.1f}%)")
    print(f"  Grid accuracy: {grid_acc:.4f} ({grid_acc*100:.1f}%)")
    print(f"  Grids solved:  {grids}/1000")

    cell_acc_i, grid_acc_i, grids_i = evaluate_iterative(model_epf, test_p, test_s, n_eval=200)
    print(f"\nIterative evaluation (200 puzzles):")
    print(f"  Cell accuracy: {cell_acc_i:.4f} ({cell_acc_i*100:.1f}%)")
    print(f"  Grid accuracy: {grid_acc_i:.4f} ({grid_acc_i*100:.1f}%)")
    print(f"  Grids solved:  {grids_i}/200")

    # Experiment 2: Deep EPF variant
    print("\n" + "=" * 60)
    print("Experiment 2: EPF Deep (more filters)")
    print("=" * 60)
    model_deep = EPFModelDeep()
    n_params_d = sum(p.numel() for p in model_deep.parameters())
    print(f"Parameters: {n_params_d:,}")

    t0 = time.time()
    model_deep, best_loss_d = train_model(model_deep, train_loader, val_loader, n_epochs=30, lr=0.001, patience=7)
    print(f"Training time: {time.time()-t0:.1f}s")

    cell_acc_d, grid_acc_d, grids_d = evaluate_model(model_deep, test_p, test_s, n_eval=1000)
    print(f"\nOne-shot evaluation (1000 puzzles):")
    print(f"  Cell accuracy: {cell_acc_d:.4f} ({cell_acc_d*100:.1f}%)")
    print(f"  Grid accuracy: {grid_acc_d:.4f} ({grid_acc_d*100:.1f}%)")
    print(f"  Grids solved:  {grids_d}/1000")

    cell_acc_di, grid_acc_di, grids_di = evaluate_iterative(model_deep, test_p, test_s, n_eval=200)
    print(f"\nIterative evaluation (200 puzzles):")
    print(f"  Cell accuracy: {cell_acc_di:.4f} ({cell_acc_di*100:.1f}%)")
    print(f"  Grid accuracy: {grid_acc_di:.4f} ({grid_acc_di*100:.1f}%)")
    print(f"  Grids solved:  {grids_di}/200")

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Phase 1 (50K data, 20 epochs):")
    print(f"  EPF Original: cell={cell_q*100:.1f}% grid={grid_q*100:.1f}% ({grids_q}/1000) | iter_grid={grid_qi*100:.1f}% ({grids_qi}/100)")
    print(f"")
    print(f"Phase 2 (200K data, 30 epochs):")
    print(f"{'Model':<20} {'Params':>10} {'Cell%':>8} {'Grid%':>8} {'Solved':>8} | {'Iter Cell%':>10} {'Iter Grid%':>10} {'Iter Solved':>10}")
    print("-" * 100)
    print(f"{'EPF Original':<20} {n_params:>10,} {cell_acc*100:>7.1f}% {grid_acc*100:>7.1f}% {grids:>7}/1000 | {cell_acc_i*100:>9.1f}% {grid_acc_i*100:>9.1f}% {grids_i:>9}/200")
    print(f"{'EPF Deep':<20} {n_params_d:>10,} {cell_acc_d*100:>7.1f}% {grid_acc_d*100:>7.1f}% {grids_d:>7}/1000 | {cell_acc_di*100:>9.1f}% {grid_acc_di*100:>9.1f}% {grids_di:>9}/200")
    print(f"")
    print(f"EPF student target: 96.8% grid accuracy (one-shot, 1M+ data, 100+ epochs)")
    print(f"Current notebook ResCNN: 15.5% grid accuracy (iterative, 50K data, 18 epochs)")

    # Save best model
    best_grid = max(grid_acc, grid_acc_d)
    best_name = "EPF Original" if grid_acc >= grid_acc_d else "EPF Deep"
    best_model = model_epf if grid_acc >= grid_acc_d else model_deep

    import tempfile
    model_path = os.path.join(tempfile.gettempdir(), "sudoku_epf_best.pth")
    torch.save(best_model.state_dict(), model_path)
    print(f"\nBest model ({best_name}) saved to: {model_path}")

    return {
        "phase1": {"cell": cell_q, "grid": grid_q, "grids": grids_q,
                    "cell_iter": cell_qi, "grid_iter": grid_qi, "grids_iter": grids_qi},
        "epf": {"cell": cell_acc, "grid": grid_acc, "grids": grids,
                 "cell_iter": cell_acc_i, "grid_iter": grid_acc_i, "grids_iter": grids_i},
        "deep": {"cell": cell_acc_d, "grid": grid_acc_d, "grids": grids_d,
                  "cell_iter": cell_acc_di, "grid_iter": grid_acc_di, "grids_iter": grids_di},
    }

if __name__ == "__main__":
    results = run_experiment()
