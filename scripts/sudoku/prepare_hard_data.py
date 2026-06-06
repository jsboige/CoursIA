"""
Sudoku Phase 2 — Hard dataset preparation.

Downloads the sapientinc/sudoku-extreme benchmark (genuinely hard puzzles, 17-36
givens, curated unique solutions used by HRM/TRM reasoning papers) and caches it
as npz arrays in the same format the RRN training scripts expect:
    puzzles:   (N, 81) int8, 0 = empty cell
    solutions: (N, 81) int8, 1-9 digits

Format of the source CSV (train.csv / test.csv):
    source,question,answer,rating
    question / answer are 81-char strings, '.' or '0' = empty in question.

Usage:
    python scripts/sudoku/prepare_hard_data.py [--max-train N] [--max-test N]

Outputs (into sudoku_models/data_cache/):
    sudoku_extreme_train.npz
    sudoku_extreme_test.npz
"""

import os
import csv
import argparse
import numpy as np

MODELS_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')
DATA_DIR = os.path.join(MODELS_DIR, 'data_cache')

REPO = 'sapientinc/sudoku-extreme'


def _parse_81(s):
    """Parse an 81-char Sudoku string into a (81,) int8 array (0 = empty)."""
    return np.array([0 if ch in '0.' else int(ch) for ch in s], dtype=np.int8)


def _convert_csv(csv_path, max_rows=None):
    puzzles = []
    solutions = []
    with open(csv_path, newline='') as f:
        reader = csv.DictReader(f)
        for i, row in enumerate(reader):
            q = row['question']
            a = row['answer']
            if len(q) != 81 or len(a) != 81:
                continue
            puzzles.append(_parse_81(q))
            solutions.append(_parse_81(a))
            if max_rows and len(puzzles) >= max_rows:
                break
    return np.array(puzzles, dtype=np.int8), np.array(solutions, dtype=np.int8)


def _report(name, puzzles):
    givens = (puzzles > 0).sum(axis=1)
    print(f"  {name}: {len(puzzles):,} puzzles | givens "
          f"min={givens.min()} max={givens.max()} mean={givens.mean():.1f} "
          f"| pct<=22 givens={(givens <= 22).mean():.3f}")


def main():
    parser = argparse.ArgumentParser(description='Prepare hard Sudoku dataset (Phase 2)')
    parser.add_argument('--max-train', type=int, default=None,
                        help='Max train puzzles (default: all)')
    parser.add_argument('--max-test', type=int, default=30000,
                        help='Max test puzzles (default: 30000)')
    args = parser.parse_args()

    os.makedirs(DATA_DIR, exist_ok=True)

    from huggingface_hub import hf_hub_download

    print(f"Downloading {REPO} CSVs from HuggingFace...")
    train_csv = hf_hub_download(REPO, 'train.csv', repo_type='dataset')
    test_csv = hf_hub_download(REPO, 'test.csv', repo_type='dataset')

    print("Converting train.csv...")
    train_p, train_s = _convert_csv(train_csv, args.max_train)
    _report('train', train_p)

    print("Converting test.csv...")
    test_p, test_s = _convert_csv(test_csv, args.max_test)
    _report('test', test_p)

    train_out = os.path.join(DATA_DIR, 'sudoku_extreme_train.npz')
    test_out = os.path.join(DATA_DIR, 'sudoku_extreme_test.npz')
    np.savez_compressed(train_out, puzzles=train_p, solutions=train_s)
    np.savez_compressed(test_out, puzzles=test_p, solutions=test_s)
    print(f"Saved: {train_out}")
    print(f"Saved: {test_out}")


if __name__ == '__main__':
    main()
