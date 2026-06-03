"""
Sudoku RRN (Recurrent Relational Network) — Core Module.

Architecture: message-passing GNN with GRU update over a Sudoku constraint graph.
Edges connect cells sharing a row, column, or 3x3 block.
Each step: compute messages -> aggregate -> GRU update.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np


def build_sudoku_edge_index():
    """Build edge index for Sudoku constraint graph (row + col + block peers)."""
    edges = set()
    for i in range(81):
        r, c = i // 9, i % 9
        br, bc = 3 * (r // 3), 3 * (c // 3)
        # Row peers
        for j in range(9):
            k = r * 9 + j
            if k != i:
                edges.add((i, k))
        # Col peers
        for j in range(9):
            k = j * 9 + c
            if k != i:
                edges.add((i, k))
        # Block peers
        for dr in range(3):
            for dc in range(3):
                k = (br + dr) * 9 + (bc + dc)
                if k != i:
                    edges.add((i, k))
    src, dst = zip(*edges)
    return torch.tensor([list(dst), list(src)], dtype=torch.long)


def make_batch_edge_index(base_edge_index, batch_size):
    """Replicate edge index for a batch of graphs."""
    edges = []
    for i in range(batch_size):
        edges.append(base_edge_index + i * 81)
    return torch.cat(edges, dim=1)


def parse_81(s):
    """Parse an 81-char string into a 9x9 numpy array."""
    return np.array([int(c) for c in s], dtype=np.int64).reshape(9, 9)


class SudokuRRN(nn.Module):
    """Recurrent Relational Network for Sudoku."""

    def __init__(self, hidden_dim=192, msg_dim=None, n_steps=16, dropout=0.1):
        super().__init__()
        if msg_dim is None:
            msg_dim = hidden_dim
        self.hidden_dim = hidden_dim
        self.msg_dim = msg_dim
        self.n_steps = n_steps

        # Input: 10-dim one-hot -> hidden
        self.input_embed = nn.Sequential(
            nn.Linear(10, hidden_dim),
            nn.LayerNorm(hidden_dim),
        )

        # Learnable position embedding
        self.pos_embed = nn.Parameter(torch.randn(81, hidden_dim) * 0.01)

        # Message MLP: concat(src, dst) -> msg
        self.msg_mlp = nn.Sequential(
            nn.Linear(hidden_dim * 2, msg_dim),
            nn.Dropout(dropout),
            nn.ReLU(inplace=True),
            nn.Linear(msg_dim, msg_dim),
        )

        # GRU for state update
        self.gru = nn.GRUCell(msg_dim, hidden_dim)

        # Layer norm
        self.norm = nn.LayerNorm(hidden_dim)

        # Output head
        self.output = nn.Linear(hidden_dim, 9)

    def _compute_messages(self, h, edge_index):
        src, dst = edge_index[1], edge_index[0]
        h_src = h[src]
        h_dst = h[dst]
        msg_input = torch.cat([h_src, h_dst], dim=-1)
        return self.msg_mlp(msg_input)

    def _aggregate_messages(self, msgs, edge_index, n_nodes):
        dst = edge_index[0]
        agg = msgs.new_zeros(n_nodes, self.msg_dim)
        agg.index_add_(0, dst, msgs)
        return agg

    def _step(self, h, edge_index, n_nodes):
        msgs = self._compute_messages(h, edge_index)
        agg = self._aggregate_messages(msgs, edge_index, n_nodes)
        h_new = self.gru(agg, h)
        return self.norm(h_new)

    def forward(self, x, edge_index):
        """
        Args:
            x: (batch*81, 10) one-hot input
            edge_index: (2, batch*num_edges) graph edges
        Returns:
            logits: (batch*81, 9) per-cell class logits
            all_logits: list of (batch*81, 9) at each step (for auxiliary loss)
        """
        n_nodes = x.size(0)
        n_graphs = n_nodes // 81
        h = self.input_embed(x) + self.pos_embed.repeat(n_graphs, 1)
        all_logits = []
        for _ in range(self.n_steps):
            h = self._step(h, edge_index, h.size(0))
            all_logits.append(self.output(h))
        return all_logits[-1], all_logits

    def count_params(self):
        return sum(p.numel() for p in self.parameters())
