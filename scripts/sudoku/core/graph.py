"""Sudoku constraint graph construction."""

import torch


def build_sudoku_edge_index():
    """Build directed edge index for Sudoku constraint graph.

    Each cell (0-80) connects to its 20 constraint neighbors:
    8 in same row + 8 in same column + 4 in same box (excluding overlaps).
    Total: 81 * 20 = 1620 directed edges.
    """
    rows, cols = [], []
    for i in range(81):
        r, c = divmod(i, 9)
        br, bc = (r // 3) * 3, (c // 3) * 3
        neighbors = set()
        for cc in range(9):
            if cc != c:
                neighbors.add(r * 9 + cc)
        for rr in range(9):
            if rr != r:
                neighbors.add(rr * 9 + c)
        for dr in range(3):
            for dc in range(3):
                idx = (br + dr) * 9 + (bc + dc)
                if idx != i and idx not in neighbors:
                    neighbors.add(idx)
        for j in neighbors:
            rows.append(j)
            cols.append(i)
    return torch.tensor([rows, cols], dtype=torch.long)


def make_batch_edge_index(base_edges, batch_size):
    """Replicate edge index for a batch, offsetting node indices."""
    n_nodes = 81
    edges_list = []
    for b in range(batch_size):
        edges_list.append(base_edges + b * n_nodes)
    return torch.cat(edges_list, dim=1)
