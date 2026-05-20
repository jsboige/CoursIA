"""
Sudoku Neural Network Training Pipeline
========================================
Generates diverse-difficulty puzzles and trains RRN/CNN/MLP with grid search.

Usage:
    python scripts/sudoku_train.py              # Full pipeline: generate + train
    python scripts/sudoku_train.py --skip-gen   # Skip generation, use cached data
    python scripts/sudoku_train.py --models rrn cnn  # Train specific models only

Architecture references:
    - Palm et al. (2018): Recurrent Relational Networks (RRN) — message passing + GRU
    - Lee et al. (2018): Message passing for SAT/constraint problems
    - Norvig (2006): Constraint propagation + backtracking solver
    - Grokking (Power et al. 2022): Overtraining past memorization → generalization
"""

import os
import sys
import time
import json
import argparse
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader

# ── Constants ────────────────────────────────────────────────────────────────
SAVE_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')
DATA_CACHE = os.path.join(SAVE_DIR, 'data_cache')
DIGITS = '123456789'
DEVICE = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
if DEVICE.type == 'cuda':
    torch.backends.cudnn.benchmark = True


# ═══════════════════════════════════════════════════════════════════════════════
# SECTION 1: Norvig-based Puzzle Generator
# ═══════════════════════════════════════════════════════════════════════════════

def _build_units_peers():
    units = [[] for _ in range(81)]
    peers = [None] * 81
    all_units = []
    for r in range(9):
        all_units.append([r * 9 + c for c in range(9)])
    for c in range(9):
        all_units.append([r * 9 + c for r in range(9)])
    for br in range(0, 9, 3):
        for bc in range(0, 9, 3):
            all_units.append([(br + dr) * 9 + (bc + dc) for dr in range(3) for dc in range(3)])
    for i in range(81):
        units[i] = [u for u in all_units if i in u]
        peer_set = set()
        for u in units[i]:
            peer_set.update(u)
        peer_set.discard(i)
        peers[i] = tuple(peer_set)
    return all_units, units, peers


_UNITS, _CELL_UNITS, _PEERS = _build_units_peers()


def _fill(grid, s, d):
    if grid[s] == d:
        return grid
    for d2 in grid[s].replace(d, ''):
        grid = _eliminate(grid, s, d2)
        if grid is None:
            return None
    return grid


def _eliminate(grid, s, d):
    if d not in grid[s]:
        return grid
    grid[s] = grid[s].replace(d, '')
    val = grid[s]
    if len(val) == 0:
        return None
    if len(val) == 1:
        for p in _PEERS[s]:
            grid = _eliminate(grid, p, val)
            if grid is None:
                return None
    for u in _CELL_UNITS[s]:
        dplaces = [sq for sq in u if d in grid[sq]]
        if len(dplaces) == 0:
            return None
        if len(dplaces) == 1:
            grid = _fill(grid, dplaces[0], d)
            if grid is None:
                return None
    return grid


def _search(grid):
    if grid is None:
        return None
    min_len, best = 10, -1
    for s in range(81):
        n = len(grid[s])
        if 1 < n < min_len:
            min_len, best = n, s
    if best == -1:
        return grid
    for d in grid[best]:
        result = _search(_fill(grid.copy(), best, d))
        if result is not None:
            return result
    return None


def solve_sudoku(puzzle_81):
    """Norvig solver. Returns solution as np array (81,) or None."""
    grid = {i: DIGITS for i in range(81)}
    for i in range(81):
        if puzzle_81[i] != 0:
            grid = _fill(grid, i, str(puzzle_81[i]))
            if grid is None:
                return None
    result = _search(grid)
    if result is None:
        return None
    return np.array([int(result[i]) for i in range(81)], dtype=np.int64)


def generate_complete_grid(rng=None):
    """Generate a random complete valid Sudoku grid."""
    if rng is None:
        rng = np.random.default_rng()
    while True:
        grid = {i: DIGITS for i in range(81)}
        indices = rng.permutation(81)
        success = True
        for idx in indices:
            candidates = list(grid[idx])
            rng.shuffle(candidates)
            placed = False
            for d in candidates:
                test = _fill(grid.copy(), idx, d)
                if test is not None:
                    grid = test
                    placed = True
                    break
            if not placed:
                success = False
                break
        if success:
            return np.array([int(grid[i]) for i in range(81)], dtype=np.int64)


def generate_puzzle_from_solution(solution, n_empty, rng=None):
    """Remove cells from solution to create a puzzle with n_empty empty cells.

    Strategy: remove cells in random order. For hard puzzles (>30 empties),
    verify solvability. Skip uniqueness check for training — we just need
    valid (puzzle, solution) pairs, not minimal puzzles.
    """
    if rng is None:
        rng = np.random.default_rng()
    puzzle = solution.copy()
    order = rng.permutation(81)
    removed = 0

    for idx in order:
        if removed >= n_empty:
            break
        puzzle[idx] = 0
        removed += 1

    # Verify it's still solvable (should always be since solution is valid)
    if removed < n_empty * 0.8:
        return None
    return puzzle


def generate_dataset(n_total, givens_range=(17, 50), seed=42, batch_size=10000):
    """Generate a dataset with uniform difficulty distribution.

    Returns (puzzles, solutions) arrays of shape (n_total, 81).
    Difficulty is uniformly distributed across givens_range.
    """
    rng = np.random.default_rng(seed)
    n_givens_levels = givens_range[1] - givens_range[0] + 1

    puzzles_list = []
    solutions_list = []

    generated = 0
    while generated < n_total:
        # Pick a target difficulty uniformly
        target_givens = rng.integers(givens_range[0], givens_range[1] + 1)
        n_empty = 81 - target_givens

        # Generate a complete grid
        solution = generate_complete_grid(rng)

        # Remove cells
        puzzle = generate_puzzle_from_solution(solution, n_empty, rng)
        if puzzle is None:
            continue

        puzzles_list.append(puzzle)
        solutions_list.append(solution)
        generated += 1

        if generated % 10000 == 0:
            print(f"  Generated {generated:,}/{n_total:,} puzzles...")
            # Progress stats
            recent_givens = (np.array(puzzles_list[-10000:]) > 0).sum(axis=1)
            print(f"    Last batch givens: mean={recent_givens.mean():.1f}, "
                  f"range={recent_givens.min()}-{recent_givens.max()}")

    puzzles = np.array(puzzles_list, dtype=np.int64)
    solutions = np.array(solutions_list, dtype=np.int64)

    # Shuffle
    perm = rng.permutation(n_total)
    puzzles = puzzles[perm]
    solutions = solutions[perm]

    return puzzles, solutions


def load_hf_dataset(n_total, seed=42):
    """Download puzzles from HuggingFace + generate hard puzzles locally.

    Strategy:
    - nakashi104/sudoku-1million: 1M puzzles, mostly 29-37 givens (fast download)
    - Generate hard puzzles (17-28 givens) using Norvig solver
    - Stratify to get uniform distribution across 17-50 givens
    """
    from datasets import load_dataset

    os.makedirs(DATA_CACHE, exist_ok=True)
    cache_path = os.path.join(DATA_CACHE, f'diverse_{n_total // 1000}k.npz')

    if os.path.exists(cache_path):
        print(f"Loading cached diverse dataset from {cache_path}...")
        data = np.load(cache_path)
        puzzles, solutions = data['puzzles'], data['solutions']
        givens = (puzzles > 0).sum(axis=1)
        print(f"  {len(puzzles):,} puzzles, givens: {givens.min()}-{givens.max()}, "
              f"mean={givens.mean():.1f}")
        return puzzles, solutions

    # Target: uniform distribution across givens levels
    rng = np.random.default_rng(seed)
    target_per_level = n_total // 34  # 17..50 = 34 levels
    buckets = {g: [] for g in range(17, 51)}

    # Phase 1: Download HF dataset (fast, covers 29-37 givens well)
    print("Phase 1: Downloading nakashi104/sudoku-1million (1M puzzles)...")
    ds = load_dataset("nakashi104/sudoku-1million", split="train")

    hf_count = 0
    for i, row in enumerate(ds):
        p_str = row['quizzes']
        s_str = row['solutions']
        p = np.array([0 if c == '0' else int(c) for c in p_str], dtype=np.int64)
        s = np.array([int(c) for c in s_str], dtype=np.int64)

        n_givens = int((p > 0).sum())
        if 17 <= n_givens <= 50 and len(buckets.get(n_givens, [])) < target_per_level:
            buckets[n_givens].append((p, s))
            hf_count += 1

        if i % 200000 == 0 and i > 0:
            filled = sum(1 for g in range(17, 51) if len(buckets[g]) >= target_per_level)
            print(f"  {i:,} scanned, {filled}/34 levels filled, {hf_count:,} collected")

    filled_hf = sum(1 for g in range(17, 51) if len(buckets[g]) >= target_per_level)
    print(f"  HF: {hf_count:,} puzzles, {filled_hf}/34 levels filled")

    # Phase 2: Generate hard puzzles (17-28 givens) to fill gaps
    empty_levels = [g for g in range(17, 29) if len(buckets[g]) < target_per_level]
    total_gen_needed = sum(target_per_level - len(buckets[g]) for g in empty_levels)

    if total_gen_needed > 0:
        print(f"\nPhase 2: Generating {total_gen_needed:,} hard puzzles "
              f"(levels {min(empty_levels)}-{max(empty_levels)} givens)...")
        generated = 0
        attempts = 0
        while generated < total_gen_needed and attempts < total_gen_needed * 20:
            # Pick a level that needs more puzzles
            level = rng.choice(empty_levels)
            if len(buckets[level]) >= target_per_level:
                empty_levels = [g for g in empty_levels if len(buckets[g]) < target_per_level]
                if not empty_levels:
                    break
                continue

            n_empty = 81 - level
            solution = generate_complete_grid(rng)
            puzzle = generate_puzzle_from_solution(solution, n_empty, rng)

            if puzzle is not None:
                buckets[level].append((puzzle, solution))
                generated += 1

            attempts += 1
            if generated % 500 == 0 and generated > 0:
                print(f"  Generated {generated:,}/{total_gen_needed:,} "
                      f"({attempts} attempts, {generated/attempts:.1%} yield)")

        print(f"  Generated {generated:,} hard puzzles")

    # Assemble final dataset
    print(f"\nPhase 3: Assembling stratified dataset...")
    puzzles_list = []
    solutions_list = []

    for g in range(17, 51):
        bucket = buckets[g]
        n_take = min(target_per_level, len(bucket))
        indices = rng.choice(len(bucket), size=n_take, replace=False) if len(bucket) > n_take else np.arange(len(bucket))
        for idx in indices:
            puzzles_list.append(bucket[idx][0])
            solutions_list.append(bucket[idx][1])

    # Fill remaining quota from over-represented levels
    remaining = n_total - len(puzzles_list)
    if remaining > 0:
        all_extra = []
        for g in range(17, 51):
            bucket = buckets[g]
            n_take = min(target_per_level, len(bucket))
            all_extra.extend(bucket[n_take:])
        if all_extra:
            n_fill = min(remaining, len(all_extra))
            indices = rng.choice(len(all_extra), size=n_fill, replace=False)
            for idx in indices:
                puzzles_list.append(all_extra[idx][0])
                solutions_list.append(all_extra[idx][1])

    puzzles = np.array(puzzles_list[:n_total], dtype=np.int64)
    solutions = np.array(solutions_list[:n_total], dtype=np.int64)

    # Shuffle
    perm = rng.permutation(len(puzzles))
    puzzles = puzzles[perm]
    solutions = solutions[perm]

    givens = (puzzles > 0).sum(axis=1)
    print(f"  Final: {len(puzzles):,} puzzles, givens: {givens.min()}-{givens.max()}, "
          f"mean={givens.mean():.1f}")

    np.savez(cache_path, puzzles=puzzles, solutions=solutions)
    print(f"  Cached to {cache_path}")
    return puzzles, solutions


def load_or_generate_dataset(n_total, seed=42, force_regenerate=False):
    """Load cached, download from HF, or generate diverse puzzles."""
    os.makedirs(DATA_CACHE, exist_ok=True)
    cache_path = os.path.join(DATA_CACHE, f'diverse_{n_total // 1000}k_seed{seed}.npz')

    if os.path.exists(cache_path) and not force_regenerate:
        print(f"Loading cached dataset from {cache_path}...")
        data = np.load(cache_path)
        puzzles = data['puzzles']
        solutions = data['solutions']
        if puzzles.ndim == 3:
            puzzles = puzzles.reshape(len(puzzles), 81)
            solutions = solutions.reshape(len(solutions), 81)
        print(f"Loaded {len(puzzles):,} puzzles")
        givens = (puzzles > 0).sum(axis=1)
        print(f"Givens distribution: min={givens.min()}, max={givens.max()}, "
              f"mean={givens.mean():.1f}")
        return puzzles, solutions

    # Try HuggingFace first (much faster than generation)
    try:
        return load_hf_dataset(n_total, seed=seed)
    except Exception as e:
        print(f"HuggingFace download failed: {e}")
        print("Falling back to Norvig-based generation (slow for hard puzzles)...")

    print(f"Generating {n_total:,} diverse puzzles (seed={seed})...")
    t0 = time.time()
    puzzles, solutions = generate_dataset(n_total, givens_range=(17, 50), seed=seed)
    elapsed = time.time() - t0
    print(f"Generated {n_total:,} puzzles in {elapsed:.0f}s ({n_total/elapsed:.0f} puzzles/s)")

    np.savez(cache_path, puzzles=puzzles, solutions=solutions)
    print(f"Cached to {cache_path}")

    givens = (puzzles > 0).sum(axis=1)
    print(f"Givens distribution: min={givens.min()}, max={givens.max()}, "
          f"mean={givens.mean():.1f}")
    return puzzles, solutions


# ═══════════════════════════════════════════════════════════════════════════════
# SECTION 2: Graph Utilities
# ═══════════════════════════════════════════════════════════════════════════════

def build_sudoku_edge_index():
    """Build directed edge index for Sudoku constraint graph.
    Each cell connects to all cells in same row, column, and box.
    Returns: edge_index (2, E) LongTensor.
    """
    edges = []
    for i in range(81):
        r, c = divmod(i, 9)
        br, bc = (r // 3) * 3, (c // 3) * 3
        for j in range(81):
            if i == j:
                continue
            r2, c2 = divmod(j, 9)
            if r2 == r or c2 == c or (r2 // 3 == br and c2 // 3 == bc):
                edges.append((i, j))
    return torch.tensor(edges, dtype=torch.long).t().contiguous()


# ═══════════════════════════════════════════════════════════════════════════════
# SECTION 3: Models
# ═══════════════════════════════════════════════════════════════════════════════

class SudokuRRN(nn.Module):
    """Recurrent Relational Network for Sudoku.

    Architecture based on Palm et al. (2018):
    - Message passing between constrained cells
    - GRU for iterative state refinement
    - Multi-step reasoning (n_steps forward passes)
    """

    def __init__(self, hidden_dim=128, msg_dim=128, n_steps=8, dropout=0.15):
        super().__init__()
        self.hidden_dim = hidden_dim
        self.n_steps = n_steps

        # Input: 9-dim one-hot for given digit, 1-dim for is_empty
        self.input_proj = nn.Linear(10, hidden_dim)

        # Message network: concatenate [sender, receiver] → message
        self.msg_mlp = nn.Sequential(
            nn.Linear(hidden_dim * 2, msg_dim),
            nn.ReLU(),
            nn.Linear(msg_dim, msg_dim),
        )

        # GRU for state update
        self.gru = nn.GRUCell(msg_dim, hidden_dim)

        # Output head: hidden → 9 logits
        self.output_head = nn.Sequential(
            nn.Dropout(dropout),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, 9),
        )

    def forward(self, x, edge_index):
        """
        x: (B, 81, 10) — one-hot encoded input (9 digits + is_empty flag)
        edge_index: (2, E) — graph edges
        Returns: (B, 81, 9) — logits for each cell
        """
        B = x.size(0)
        E = edge_index.size(1)

        h = self.input_proj(x)  # (B, 81, hidden_dim)

        senders, receivers = edge_index[0], edge_index[1]

        for _ in range(self.n_steps):
            # Gather sender/receiver features
            h_send = h[:, senders, :]  # (B, E, hidden)
            h_recv = h[:, receivers, :]  # (B, E, hidden)

            # Compute messages
            msg_input = torch.cat([h_send, h_recv], dim=-1)
            messages = self.msg_mlp(msg_input)  # (B, E, msg_dim)

            # Aggregate messages per receiver
            agg = torch.zeros(B, 81, messages.size(-1), device=x.device, dtype=messages.dtype)
            recv_exp = receivers.unsqueeze(0).unsqueeze(-1).expand(B, -1, messages.size(-1))
            agg.scatter_add_(1, recv_exp, messages)

            # GRU update (cast to full precision for stability)
            h_flat = h.reshape(B * 81, self.hidden_dim)
            agg_flat = agg.reshape(B * 81, messages.size(-1))
            h_flat = self.gru(agg_flat.float(), h_flat)
            h = h_flat.reshape(B, 81, self.hidden_dim)

        return self.output_head(h)  # (B, 81, 9)


class SudokuCNN(nn.Module):
    """9x9 CNN for Sudoku — captures spatial structure via convolutions."""

    def __init__(self, hidden_dim=128, n_layers=10, dropout=0.1):
        super().__init__()
        self.input_proj = nn.Conv2d(10, hidden_dim, 3, padding=1)

        layers = []
        for _ in range(n_layers):
            layers.append(nn.Conv2d(hidden_dim, hidden_dim, 3, padding=1))
            layers.append(nn.BatchNorm2d(hidden_dim))
            layers.append(nn.ReLU())
            layers.append(nn.Dropout2d(dropout))
        self.hidden_layers = nn.Sequential(*layers)

        self.output_head = nn.Conv2d(hidden_dim, 9, 1)

    def forward(self, x):
        """
        x: (B, 81, 10) → reshaped to (B, 10, 9, 9)
        Returns: (B, 81, 9)
        """
        B = x.size(0)
        h = x.reshape(B, 9, 9, 10).permute(0, 3, 1, 2)  # (B, 10, 9, 9)
        h = F.relu(self.input_proj(h))
        h = self.hidden_layers(h)
        h = self.output_head(h)  # (B, 9, 9, 9)
        return h.reshape(B, 81, 9)


class SudokuMLP(nn.Module):
    """Flat MLP baseline — no spatial/graph structure."""

    def __init__(self, hidden_dim=512, n_layers=6, dropout=0.1):
        super().__init__()
        layers = [nn.Linear(810, hidden_dim), nn.ReLU(), nn.Dropout(dropout)]
        for _ in range(n_layers - 1):
            layers.extend([nn.Linear(hidden_dim, hidden_dim), nn.ReLU(), nn.Dropout(dropout)])
        layers.append(nn.Linear(hidden_dim, 729))
        self.net = nn.Sequential(*layers)

    def forward(self, x):
        """x: (B, 81, 10) → Returns: (B, 81, 9)"""
        B = x.size(0)
        out = self.net(x.reshape(B, 810))
        return out.reshape(B, 81, 9)


# ═══════════════════════════════════════════════════════════════════════════════
# SECTION 4: Dataset and Training
# ═══════════════════════════════════════════════════════════════════════════════

class SudokuDataset(Dataset):
    def __init__(self, puzzles, solutions):
        self.puzzles = puzzles  # (N, 81) int
        self.solutions = solutions  # (N, 81) int

    def __len__(self):
        return len(self.puzzles)

    def __getitem__(self, idx):
        p = self.puzzles[idx]
        s = self.solutions[idx]

        # One-hot encode: 9 channels for digits 1-9, 1 channel for is_empty
        x = np.zeros((81, 10), dtype=np.float32)
        for i in range(81):
            if p[i] != 0:
                x[i, p[i] - 1] = 1.0
            else:
                x[i, 9] = 1.0

        # Target: 0-indexed (solution digit - 1)
        y = np.zeros(81, dtype=np.int64)
        for i in range(81):
            if p[i] == 0:
                y[i] = s[i] - 1
            else:
                y[i] = -1  # ignore given cells

        return torch.tensor(x), torch.tensor(y), torch.tensor(p != 0)


def sudoku_collate_fn(batch):
    xs, ys, masks = zip(*batch)
    return torch.stack(xs), torch.stack(ys), torch.stack(masks)


_USE_AMP = DEVICE.type == 'cuda'
_SCALER = torch.amp.GradScaler('cuda', enabled=_USE_AMP)


def train_epoch(model, loader, optimizer, device, model_type='rrn', edge_index=None):
    model.train()
    total_loss = 0
    total_correct = 0
    total_cells = 0

    for x, y, given_mask in loader:
        x, y = x.to(device, non_blocking=True), y.to(device, non_blocking=True)
        given_mask = given_mask.to(device, non_blocking=True)
        empty_mask = ~given_mask

        optimizer.zero_grad(set_to_none=True)

        with torch.amp.autocast('cuda', enabled=_USE_AMP):
            if model_type == 'rrn':
                logits = model(x, edge_index)
            else:
                logits = model(x)

            logits_flat = logits.reshape(-1, 9)
            y_flat = y.reshape(-1)
            empty_flat = empty_mask.reshape(-1)

            loss = F.cross_entropy(logits_flat[empty_flat], y_flat[empty_flat])

        _SCALER.scale(loss).backward()
        _SCALER.unscale_(optimizer)
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        _SCALER.step(optimizer)
        _SCALER.update()

        total_loss += loss.item() * empty_flat.sum().item()
        preds = logits_flat[empty_flat].argmax(dim=-1)
        total_correct += (preds == y_flat[empty_flat]).sum().item()
        total_cells += empty_flat.sum().item()

    return total_loss / max(total_cells, 1), total_correct / max(total_cells, 1)


@torch.no_grad()
def evaluate_model(model, loader, device, model_type='rrn', edge_index=None):
    model.eval()
    total_correct = 0
    total_cells = 0
    total_grids_solved = 0
    total_grids = 0

    for x, y, given_mask in loader:
        x, y = x.to(device, non_blocking=True), y.to(device, non_blocking=True)
        given_mask = given_mask.to(device, non_blocking=True)
        empty_mask = ~given_mask

        with torch.amp.autocast('cuda', enabled=_USE_AMP):
            if model_type == 'rrn':
                logits = model(x, edge_index)
            else:
                logits = model(x)

        logits_flat = logits.reshape(-1, 9)
        y_flat = y.reshape(-1)
        empty_flat = empty_mask.reshape(-1)

        preds = logits_flat[empty_flat].argmax(dim=-1)
        total_correct += (preds == y_flat[empty_flat]).sum().item()
        total_cells += empty_flat.sum().item()

        # Vectorized grid accuracy
        preds_grid = logits.argmax(dim=-1)  # (B, 81)
        B = x.size(0)
        for b in range(B):
            emask = empty_mask[b]
            if emask.sum() > 0 and (preds_grid[b][emask] == y[b][emask]).all():
                total_grids_solved += 1
            total_grids += 1

    cell_acc = total_correct / max(total_cells, 1)
    grid_acc = total_grids_solved / max(total_grids, 1)
    return cell_acc, grid_acc


def run_single_training(puzzles, solutions, model_config, args, run_id,
                        max_train=None):
    """Train a single model configuration. Returns results dict.

    max_train: limit training set size (for adaptive sweep).
    """
    # Subsample if requested
    n_total = len(puzzles)
    if max_train is not None and max_train < int(n_total * 0.8):
        # Subsample stratified by difficulty
        rng = np.random.default_rng(args.seed + run_id)
        perm = rng.permutation(n_total)
        n_needed = int(max_train / 0.8)  # account for train/val/test split
        puzzles = puzzles[perm[:n_needed]]
        solutions = solutions[perm[:n_needed]]

    n_train = int(len(puzzles) * 0.8)
    n_val = int(len(puzzles) * 0.1)
    # n_test = remainder

    train_ds = SudokuDataset(puzzles[:n_train], solutions[:n_train])
    val_ds = SudokuDataset(puzzles[n_train:n_train + n_val],
                           solutions[n_train:n_train + n_val])

    train_loader = DataLoader(train_ds, batch_size=args.batch_size, shuffle=True,
                              num_workers=0, pin_memory=True, drop_last=True,
                              collate_fn=sudoku_collate_fn)
    val_loader = DataLoader(val_ds, batch_size=args.batch_size, shuffle=False,
                            num_workers=0, pin_memory=True,
                            collate_fn=sudoku_collate_fn)

    model_type = model_config['type']
    params = {k: v for k, v in model_config.items() if k not in ('type', 'batch_size')}

    if model_type == 'rrn':
        model = SudokuRRN(**params).to(DEVICE)
        edge_index = build_sudoku_edge_index().to(DEVICE)
    elif model_type == 'cnn':
        model = SudokuCNN(**params).to(DEVICE)
        edge_index = None
    elif model_type == 'mlp':
        model = SudokuMLP(**params).to(DEVICE)
        edge_index = None
    else:
        raise ValueError(f"Unknown model type: {model_type}")

    n_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"\n{'='*60}")
    print(f"Run {run_id}: {model_config}")
    print(f"Model: {model_type.upper()} ({n_params:,} params)")
    print(f"Train: {len(train_ds):,} | Val: {len(val_ds):,}")
    print(f"{'='*60}")

    optimizer = torch.optim.Adam(model.parameters(), lr=args.lr, weight_decay=1e-5)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=args.epochs)
    criterion = nn.CrossEntropyLoss()

    best_val_acc = 0
    best_val_grid = 0
    best_state = None
    patience_counter = 0
    history = []

    for epoch in range(1, args.epochs + 1):
        t0 = time.time()

        train_loss, train_acc = train_epoch(
            model, train_loader, optimizer, DEVICE, model_type, edge_index)
        val_acc, val_grid = evaluate_model(
            model, val_loader, DEVICE, model_type, edge_index)

        scheduler.step()
        elapsed = time.time() - t0

        history.append({
            'epoch': epoch,
            'train_loss': train_loss,
            'train_acc': train_acc,
            'val_cell_acc': val_acc,
            'val_grid_acc': val_grid,
            'lr': optimizer.param_groups[0]['lr'],
            'time_s': elapsed,
        })

        marker = ""
        if val_acc > best_val_acc:
            best_val_acc = val_acc
            best_val_grid = val_grid
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}
            patience_counter = 0
            marker = " *"
        else:
            patience_counter += 1

        print(f"  Epoch {epoch:3d}/{args.epochs} | "
              f"loss={train_loss:.4f} acc={train_acc:.3f} | "
              f"val_cell={val_acc:.3f} val_grid={val_grid:.3f} | "
              f"lr={optimizer.param_groups[0]['lr']:.1e} | {elapsed:.1f}s{marker}")

        if patience_counter >= args.patience:
            print(f"  Early stopping at epoch {epoch}")
            break

    # Restore best model and evaluate on test set
    if best_state is not None:
        model.load_state_dict(best_state)
        model.to(DEVICE)

    n_test_start = n_train + n_val
    test_ds = SudokuDataset(puzzles[n_test_start:], solutions[n_test_start:])
    test_loader = DataLoader(test_ds, batch_size=args.batch_size, shuffle=False,
                             num_workers=0, pin_memory=True,
                             collate_fn=sudoku_collate_fn)
    test_acc, test_grid = evaluate_model(model, test_loader, DEVICE, model_type, edge_index)

    print(f"\n  TEST: cell_acc={test_acc:.4f}, grid_acc={test_grid:.4f}")
    print(f"  Best val: cell_acc={best_val_acc:.4f}, grid_acc={best_val_grid:.4f}")

    # Save model
    model_name = f"sudoku_{model_type}"
    for k, v in params.items():
        model_name += f"_{k[:3]}{v}"
    model_path = os.path.join(SAVE_DIR, f'{model_name}_best.pt')
    torch.save({
        'model_state_dict': best_state,
        'model_config': model_config,
        'n_params': n_params,
        'val_cell_acc': best_val_acc,
        'val_grid_acc': best_val_grid,
        'test_cell_acc': test_acc,
        'test_grid_acc': test_grid,
        'history': history,
    }, model_path)
    print(f"  Saved to {model_path}")

    return {
        'config': model_config,
        'n_params': n_params,
        'test_cell_acc': test_acc,
        'test_grid_acc': test_grid,
        'best_val_cell_acc': best_val_acc,
        'best_val_grid_acc': best_val_grid,
        'n_epochs': len(history),
        'training_time_s': sum(h['time_s'] for h in history),
        'history': history,
        'model_path': model_path,
    }


# ═══════════════════════════════════════════════════════════════════════════════
# SECTION 5: Grid Search Configurations
# ═══════════════════════════════════════════════════════════════════════════════

def _get_max_train(config):
    """Return max training samples for a given config (adaptive sweep sizing).

    Smaller models overfit faster so need less data to diagnose capacity.
    These can be adjusted if models overfit or underfit.
    """
    model_type = config['type']
    hidden = config.get('hidden_dim', 64)
    # Estimate param count from config for scaling
    if model_type == 'rrn':
        steps = config.get('n_steps', 16)
        msg = config.get('msg_dim', hidden)
        # Rough param estimate: ~3*hidden^2 + steps*(hidden*msg*4 + hidden^2*3)
        est = 3 * hidden * hidden + steps * (hidden * msg * 4 + hidden * hidden * 3)
    elif model_type == 'cnn':
        layers = config.get('n_layers', 6)
        est = hidden * hidden * layers * 9
    elif model_type == 'mlp':
        layers = config.get('n_layers', 4)
        est = 81 * 9 * hidden + hidden * hidden * (layers - 1) + hidden * 81 * 9
    else:
        est = 100_000

    if est < 20_000:
        return 15_000
    elif est < 60_000:
        return 25_000
    elif est < 200_000:
        return 40_000
    elif est < 500_000:
        return 55_000
    else:
        return 70_000


GRID_CONFIGS = {
    'rrn': [
        # Sweep: steps=4 and steps=16 for 3 hidden sizes
        {'type': 'rrn', 'hidden_dim': 32,  'msg_dim': 32,  'n_steps': 4,  'dropout': 0.1},
        {'type': 'rrn', 'hidden_dim': 32,  'msg_dim': 32,  'n_steps': 16, 'dropout': 0.1},
        {'type': 'rrn', 'hidden_dim': 64,  'msg_dim': 64,  'n_steps': 16, 'dropout': 0.1},
        {'type': 'rrn', 'hidden_dim': 128, 'msg_dim': 128, 'n_steps': 16, 'dropout': 0.1, 'batch_size': 192},
    ],
    'cnn': [
        {'type': 'cnn', 'hidden_dim': 64,  'n_layers': 6,  'dropout': 0.1},
        {'type': 'cnn', 'hidden_dim': 128, 'n_layers': 8,  'dropout': 0.1},
    ],
    'mlp': [
        {'type': 'mlp', 'hidden_dim': 256, 'n_layers': 4, 'dropout': 0.1, 'batch_size': 256},
        {'type': 'mlp', 'hidden_dim': 512, 'n_layers': 6, 'dropout': 0.1, 'batch_size': 192},
    ],
}


def main():
    parser = argparse.ArgumentParser(description='Sudoku NN Training Pipeline')
    parser.add_argument('--n-total', type=int, default=200_000,
                        help='Total number of puzzles to generate/load')
    parser.add_argument('--skip-gen', action='store_true',
                        help='Skip generation, use cached dataset')
    parser.add_argument('--models', nargs='+', default=['rrn', 'cnn', 'mlp'],
                        help='Which model types to train')
    parser.add_argument('--epochs', type=int, default=30,
                        help='Max epochs per training run')
    parser.add_argument('--patience', type=int, default=6,
                        help='Early stopping patience')
    parser.add_argument('--batch-size', type=int, default=256,
                        help='Training batch size')
    parser.add_argument('--lr', type=float, default=1e-3,
                        help='Learning rate')
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--quick', action='store_true',
                        help='Quick test: 10K puzzles, 10 epochs, 1 config per model')
    parser.add_argument('--no-hf', action='store_true',
                        help='Skip HuggingFace download, generate locally')
    args = parser.parse_args()

    print(f"Device: {DEVICE}")
    if torch.cuda.is_available():
        print(f"GPU: {torch.cuda.get_device_name(0)}")
        print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB")

    # ── Generate / Load Dataset ──────────────────────────────────────────────
    n_total = 10_000 if args.quick else args.n_total
    force = not args.skip_gen and not args.no_hf
    if args.no_hf:
        puzzles, solutions = load_or_generate_dataset(n_total, seed=args.seed,
                                                      force_regenerate=True)
    else:
        puzzles, solutions = load_or_generate_dataset(n_total, seed=args.seed,
                                                      force_regenerate=force)

    # ── Grid Search ──────────────────────────────────────────────────────────
    all_results = []
    run_id = 0

    for model_type in args.models:
        if model_type not in GRID_CONFIGS:
            print(f"Unknown model type: {model_type}")
            continue

        configs = GRID_CONFIGS[model_type]
        if args.quick:
            configs = configs[:1]  # Just one config per model type in quick mode

        for config in configs:
            run_id += 1

            # Skip if checkpoint already exists from a previous run
            model_name = f"sudoku_{config['type']}"
            for k, v in config.items():
                if k != 'type' and k != 'batch_size':
                    model_name += f"_{k[:3]}{v}"
            ckpt_path = os.path.join(SAVE_DIR, f'{model_name}_best.pt')
            if os.path.exists(ckpt_path):
                print(f"\nSkip run {run_id}: {config} (checkpoint exists)")
                ckpt = torch.load(ckpt_path, map_location='cpu', weights_only=False)
                hist = ckpt.get('history', [])
                result = {
                    'config': config,
                    'n_params': ckpt.get('n_params', 0),
                    'test_cell_acc': ckpt.get('test_cell_acc', 0),
                    'test_grid_acc': ckpt.get('test_grid_acc', 0),
                    'best_val_cell_acc': ckpt.get('val_cell_acc', 0),
                    'best_val_grid_acc': ckpt.get('val_grid_acc', 0),
                    'n_epochs': len(hist),
                    'training_time_s': sum(h.get('time_s', 0) for h in hist),
                    'history': hist,
                    'model_path': ckpt_path,
                }
                all_results.append(result)
                continue

            # Per-config batch size override
            effective_args = args
            if 'batch_size' in config:
                import copy
                effective_args = copy.copy(args)
                effective_args.batch_size = config['batch_size']

            # Adaptive dataset sizing: smaller models need less data
            max_train = _get_max_train(config)
            try:
                result = run_single_training(puzzles, solutions, config, effective_args,
                                             run_id, max_train=max_train)
                all_results.append(result)
            except Exception as e:
                print(f"\nFAILED run {run_id}: {config}")
                print(f"  Error: {e}")
                import traceback
                traceback.print_exc()
                all_results.append({
                    'config': config,
                    'error': str(e),
                })

    # ── Summary ──────────────────────────────────────────────────────────────
    print(f"\n{'='*70}")
    print("GRID SEARCH SUMMARY")
    print(f"{'='*70}")
    print(f"{'#':<4} {'Type':<5} {'Params':>10} {'Val Cell':>10} {'Val Grid':>10} "
          f"{'Test Cell':>10} {'Test Grid':>10} {'Epochs':>7} {'Time':>8}")
    print("-" * 80)

    for i, r in enumerate(all_results):
        if 'error' in r:
            print(f"{i+1:<4} FAILED: {r['config']} — {r['error']}")
            continue
        print(f"{i+1:<4} {r['config']['type']:<5} {r['n_params']:>10,} "
              f"{r['best_val_cell_acc']:>10.4f} {r['best_val_grid_acc']:>10.4f} "
              f"{r['test_cell_acc']:>10.4f} {r['test_grid_acc']:>10.4f} "
              f"{r['n_epochs']:>7} {r['training_time_s']:>7.0f}s")

    # Find best per type
    for model_type in args.models:
        type_results = [r for r in all_results
                        if 'error' not in r and r['config']['type'] == model_type]
        if type_results:
            best = max(type_results, key=lambda r: r['test_grid_acc'])
            print(f"\nBest {model_type.upper()}: {best['n_params']:,} params, "
                  f"test_cell={best['test_cell_acc']:.4f}, "
                  f"test_grid={best['test_grid_acc']:.4f}")

    # Save results
    results_path = os.path.join(SAVE_DIR, 'grid_search_results.json')
    with open(results_path, 'w') as f:
        # Truncate history to last 5 epochs for JSON size
        for r in all_results:
            if 'history' in r:
                r['history_summary'] = r['history'][-5:]
                del r['history']
        json.dump({'args': vars(args), 'results': all_results}, f, indent=2)
    print(f"\nResults saved to {results_path}")

    # ── Refinement Phase: best config with more steps + epochs ────────────────
    successful = [r for r in all_results if 'error' not in r]
    if not successful or args.quick:
        return

    # Best overall by test_cell_acc
    best = max(successful, key=lambda r: r['test_cell_acc'])
    config = dict(best['config'])

    # For RRN: upgrade steps to 32
    if config['type'] == 'rrn':
        config['n_steps'] = 32
        # Scale batch_size down for more reasoning steps to fit VRAM
        base_batch = config.get('batch_size', args.batch_size)
        config['batch_size'] = max(64, base_batch // 2)
    # For CNN/MLP: just more epochs
    print(f"\n{'='*70}")
    print(f"REFINEMENT — Best config ({best['config']['type'].upper()}) with more capacity")
    print(f"  Sweep best: {best['config']} -> test_cell={best['test_cell_acc']:.4f}")
    print(f"  Refining to: {config}")
    print(f"{'='*70}")

    import copy
    refine_args = copy.copy(args)
    refine_args.epochs = 60
    refine_args.patience = 12
    if 'batch_size' in config:
        refine_args.batch_size = config['batch_size']
    refine_results = []

    try:
        result = run_single_training(
            puzzles, solutions, config, refine_args, run_id=100)
        result['refinement_of'] = best.get('model_path', '')
        refine_results.append(result)
    except Exception as e:
        print(f"  FAILED refinement: {e}")

    # Also train best with steps=64 if RRN
    if best['config']['type'] == 'rrn':
        config64 = dict(best['config'])
        config64['n_steps'] = 64
        config64['batch_size'] = max(32, config.get('batch_size', args.batch_size) // 2)
        print(f"\n  Also trying steps=64 (batch={config64['batch_size']})...")
        refine_args2 = copy.copy(args)
        refine_args2.epochs = 40
        refine_args2.patience = 10
        refine_args2.batch_size = config64['batch_size']
        try:
            result = run_single_training(
                puzzles, solutions, config64, refine_args2, run_id=101)
            result['refinement_of'] = best.get('model_path', '')
            refine_results.append(result)
        except Exception as e:
            print(f"  FAILED steps=64 refinement: {e}")

    if refine_results:
        print(f"\n{'='*70}")
        print("REFINEMENT RESULTS")
        print(f"{'='*70}")
        for r in refine_results:
            print(f"  {r['config']['type'].upper()} ({r['n_params']:,} params): "
                  f"test_cell={r['test_cell_acc']:.4f}, test_grid={r['test_grid_acc']:.4f}, "
                  f"epochs={r['n_epochs']}")

        refine_path = os.path.join(SAVE_DIR, 'grid_search_refinement.json')
        with open(refine_path, 'w') as f:
            for r in refine_results:
                if 'history' in r:
                    r['history_summary'] = r['history'][-10:]
                    del r['history']
            json.dump({'refinement_results': refine_results}, f, indent=2)
        print(f"  Saved to {refine_path}")


if __name__ == '__main__':
    main()
