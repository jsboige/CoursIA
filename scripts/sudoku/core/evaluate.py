"""Zero-shot evaluation for Sudoku RRN models."""

import numpy as np
import torch
import torch.nn as nn
from torch.amp import autocast

from .graph import make_batch_edge_index
from .models import count_params


@torch.no_grad()
def evaluate(model, puzzles, solutions, base_edges, device, batch_size=64):
    """Pure zero-shot evaluation: single forward pass, predict from last step.

    Args:
        model: SudokuRRN model.
        puzzles: (N, 81) int array, 0 = empty cell.
        solutions: (N, 81) int array, values 1-9.
        base_edges: Base edge index from build_sudoku_edge_index().
        device: torch device.
        batch_size: Evaluation batch size.

    Returns:
        (cell_acc, grid_acc, avg_loss)
    """
    model.eval()
    base_edges = base_edges.to(device)
    n = len(puzzles)
    correct_cells = 0
    total_cells = 0
    solved_grids = 0

    criterion = nn.CrossEntropyLoss(reduction='none')
    total_loss = 0
    loss_count = 0

    for i in range(0, n, batch_size):
        batch_p = puzzles[i:i+batch_size]
        batch_s = solutions[i:i+batch_size]
        bs = len(batch_p)

        is_given = (batch_p > 0).astype(np.float32)
        digits = np.clip(batch_p, 0, 9)
        x = np.zeros((bs, 81, 10), dtype=np.float32)
        for d in range(1, 10):
            x[:, :, d-1] = (digits == d).astype(np.float32)
        x[:, :, 9] = is_given

        x_t = torch.tensor(x).to(device)
        y_t = torch.tensor((batch_s - 1).astype(np.int64)).to(device)
        empty_t = torch.tensor(1.0 - is_given).to(device)

        edge_index = make_batch_edge_index(base_edges, bs)

        with autocast('cuda'):
            logits_list = model(x_t, edge_index)

        last_logits = logits_list[-1]
        preds = last_logits.argmax(dim=-1)

        correct = (preds == y_t).float() * empty_t
        correct_cells += correct.sum().item()
        total_cells += empty_t.sum().item()

        grid_correct = (preds == y_t).view(bs, 81)
        empty_mask = empty_t.bool().view(bs, 81)
        grids_solved = []
        for g in range(bs):
            if empty_mask[g].any():
                grids_solved.append(grid_correct[g][empty_mask[g]].all().item())
            else:
                grids_solved.append(True)
        solved_grids += sum(grids_solved)

        with autocast('cuda'):
            per_cell = criterion(last_logits.reshape(-1, 9), y_t.reshape(-1))
            empty_flat = empty_t.reshape(-1)
            masked = per_cell * empty_flat
            total_loss += masked.sum().item()
            loss_count += empty_flat.sum().item()

    cell_acc = correct_cells / total_cells if total_cells > 0 else 0
    grid_acc = solved_grids / n if n > 0 else 0
    avg_loss = total_loss / loss_count if loss_count > 0 else 0
    return cell_acc, grid_acc, avg_loss
