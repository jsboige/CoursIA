"""Sudoku dataset loading and PyTorch DataLoader utilities."""

import os
import time
import numpy as np
import torch
from torch.utils.data import Dataset


def parse_81(s):
    """Parse an 81-character Sudoku string into a numpy array."""
    return np.array([int(c) for c in s], dtype=np.int64)


def load_sudoku_dataset(n_total=1_000_000, save_dir=None):
    """Load sudoku-1million from HuggingFace with local Parquet caching.

    Args:
        n_total: Max number of puzzles to load.
        save_dir: Directory for cache (default: sudoku_models/data_cache).
    """
    if save_dir is None:
        save_dir = os.path.join(os.path.dirname(__file__), '..', '..', '..', 'sudoku_models')
    cache_dir = os.path.join(save_dir, 'data_cache')
    os.makedirs(cache_dir, exist_ok=True)
    p_cache = os.path.join(cache_dir, f'puzzles_hf_{n_total}.npz')

    if os.path.exists(p_cache):
        print(f"Loading cached puzzles from {p_cache}...")
        data = np.load(p_cache)
        all_puzzles = data['puzzles']
        all_solutions = data['solutions']
        print(f"Loaded {len(all_puzzles):,} puzzles from cache")
        if all_puzzles.ndim == 3:
            all_puzzles = all_puzzles.reshape(len(all_puzzles), 81)
            all_solutions = all_solutions.reshape(len(all_solutions), 81)
        return all_puzzles, all_solutions

    from datasets import load_dataset
    print(f"Downloading nakashi104/sudoku-1million from HuggingFace...")
    ds = load_dataset('nakashi104/sudoku-1million', split='train')
    print(f"Downloaded {len(ds):,} puzzles")

    n_use = min(n_total, len(ds))
    all_puzzles = np.zeros((n_use, 81), dtype=np.int64)
    all_solutions = np.zeros((n_use, 81), dtype=np.int64)

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


class SudokuGraphDataset(Dataset):
    """Graph-formatted Sudoku dataset. One-hot encoding done in collate_fn."""

    def __init__(self, puzzles, solutions):
        self.puzzles = puzzles.astype(np.int8)
        self.solutions = solutions.astype(np.int8)

    def __len__(self):
        return len(self.puzzles)

    def __getitem__(self, idx):
        return self.puzzles[idx], self.solutions[idx]


def sudoku_collate_fn(batch):
    """Vectorized collate: one-hot encode an entire batch at once."""
    puzzles_np = np.array([b[0] for b in batch], dtype=np.int64)
    solutions_np = np.array([b[1] for b in batch], dtype=np.int64)
    bs = len(batch)

    is_given = (puzzles_np > 0).astype(np.float32)
    x = np.zeros((bs, 81, 10), dtype=np.float32)
    for d in range(1, 10):
        x[:, :, d - 1] = (puzzles_np == d).astype(np.float32)
    x[:, :, 9] = is_given

    return (
        torch.tensor(x),
        torch.tensor(solutions_np - 1, dtype=torch.long),
        torch.tensor(is_given),
    )
