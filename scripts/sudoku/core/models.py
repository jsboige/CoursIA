"""Sudoku RRN model definition (Palm et al. 2018)."""

import torch
import torch.nn as nn


class SudokuRRN(nn.Module):
    """Recurrent Relational Network for Sudoku.

    Graph message passing with GRU updates over multiple reasoning steps.

    Args:
        hidden_dim: Hidden state dimension per cell (default: 128)
        msg_dim: Message dimension (default: 128)
        n_steps: Number of recurrent reasoning steps (default: 32)
        dropout: Dropout rate in message MLP (default: 0.15)
    """

    def __init__(self, hidden_dim=128, msg_dim=128, n_steps=32, dropout=0.15):
        super().__init__()
        self.hidden_dim = hidden_dim
        self.msg_dim = msg_dim
        self.n_steps = n_steps

        self.input_embed = nn.Sequential(
            nn.Linear(10, hidden_dim),
            nn.LayerNorm(hidden_dim),
        )

        self.pos_embed = nn.Parameter(torch.randn(81, hidden_dim) * 0.01)

        self.msg_mlp = nn.Sequential(
            nn.Linear(hidden_dim * 2, msg_dim),
            nn.Dropout(dropout),
            nn.ReLU(inplace=True),
            nn.Linear(msg_dim, msg_dim),
        )

        self.gru = nn.GRUCell(msg_dim, hidden_dim)
        self.norm = nn.LayerNorm(hidden_dim)
        self.output = nn.Linear(hidden_dim, 9)

    def _compute_messages(self, h, edge_index):
        src, dst = edge_index[0], edge_index[1]
        h_src = h[src]
        h_dst = h[dst]
        msg_input = torch.cat([h_src, h_dst], dim=-1)
        return self.msg_mlp(msg_input)

    def _aggregate_messages(self, msgs, edge_index, n_nodes):
        _, dst = edge_index[0], edge_index[1]
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
            x: (batch_size, 81, 10) input features
            edge_index: (2, batch_size * 1620) edges for the batch

        Returns:
            logits_list: list of (batch_size, 81, 9) logits at each step
        """
        batch_size = x.size(0)
        n_nodes = batch_size * 81

        h = self.input_embed(x) + self.pos_embed.unsqueeze(0)
        h = h.reshape(n_nodes, self.hidden_dim)

        logits_list = []
        for _ in range(self.n_steps):
            h = self._step(h, edge_index, n_nodes)
            logits = self.output(h)
            logits_list.append(logits.view(batch_size, 81, 9))

        return logits_list


def count_params(model):
    return sum(p.numel() for p in model.parameters() if p.requires_grad)
