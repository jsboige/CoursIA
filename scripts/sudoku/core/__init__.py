"""Sudoku neural network training core modules.

Re-exports the most commonly used symbols for convenience.
"""

from .models import SudokuRRN, count_params
from .graph import build_sudoku_edge_index, make_batch_edge_index
from .dataset import (
    parse_81, load_sudoku_dataset, SudokuGraphDataset, sudoku_collate_fn,
)
from .evaluate import evaluate
from .generation import generate_complete_grid, generate_puzzles
from .training import train_rrn
from .solvers import solve_sudoku, is_valid_puzzle

__all__ = [
    'SudokuRRN', 'count_params',
    'build_sudoku_edge_index', 'make_batch_edge_index',
    'parse_81', 'load_sudoku_dataset', 'SudokuGraphDataset', 'sudoku_collate_fn',
    'evaluate',
    'generate_complete_grid', 'generate_puzzles',
    'train_rrn',
    'solve_sudoku', 'is_valid_puzzle',
]
