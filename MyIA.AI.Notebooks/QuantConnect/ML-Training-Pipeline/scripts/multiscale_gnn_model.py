"""Multi-scale GAT for cross-asset log-RV forecasting (Issue #834 M5).

Three temporal paths (daily / weekly / monthly, à la Corsi 2009) each pass
through a 2-layer GAT over the cross-asset graph. Outputs are concatenated
and projected to a per-coin scalar log-RV prediction.

Designed for small graphs (N=3..10 coins). Not a deep GNN — over-smoothing
on tiny graphs. The "multi-scale" part is temporal, mirroring HAR.

Inputs at training time are produced by `multiscale_gnn_features.build_panel`
+ `to_pyg_batches`.
"""

from __future__ import annotations

from dataclasses import dataclass

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch_geometric.nn import GATConv


@dataclass(frozen=True)
class MultiScaleGNNConfig:
    n_features: int = 4  # log_rv, rv_d, rv_w, rv_m
    hidden: int = 32
    heads: int = 4
    dropout: float = 0.15
    n_scales: int = 3  # daily / weekly / monthly


class _ScaleGAT(nn.Module):
    """Single-scale 2-layer GAT branch.

    Reduces (N, F) → (N, hidden) using attention-weighted message passing
    over the dynamic adjacency for that day.
    """

    def __init__(self, in_dim: int, hidden: int, heads: int, dropout: float):
        super().__init__()
        # Layer 1: in_dim → heads*hidden//heads = hidden
        self.gat1 = GATConv(
            in_channels=in_dim,
            out_channels=hidden // heads,
            heads=heads,
            dropout=dropout,
            concat=True,
            add_self_loops=False,  # adjacency already includes them
        )
        # Layer 2: hidden → hidden (heads merged)
        self.gat2 = GATConv(
            in_channels=hidden,
            out_channels=hidden,
            heads=1,
            dropout=dropout,
            concat=False,
            add_self_loops=False,
        )
        self.dropout = dropout

    def forward(
        self,
        x: torch.Tensor,
        edge_index: torch.Tensor,
        edge_weight: torch.Tensor | None = None,
    ) -> torch.Tensor:
        h = self.gat1(x, edge_index, edge_attr=edge_weight)
        h = F.elu(h)
        h = F.dropout(h, p=self.dropout, training=self.training)
        h = self.gat2(h, edge_index, edge_attr=edge_weight)
        h = F.elu(h)
        return h


class MultiScaleGNN(nn.Module):
    """3-scale GAT + fusion MLP for cross-asset log-RV forecast.

    Forward inputs:
        x_d : (N, F)  — daily features at t (last 1 day)
        x_w : (N, F)  — weekly features at t (mean over last 5d, already
                       baked into x's rv_w channel — but we re-pass full x
                       so the GAT can attend to all 4 features)
        x_m : (N, F)
        edge_index : (2, E) shared across scales (could differ if you pre-
                     compute different graphs per scale; we keep one for now)
        edge_weight : (E,)

    Output:
        ŷ : (N,) — predicted log-RV at t+1..t+h (averaged target).
    """

    def __init__(self, config: MultiScaleGNNConfig | None = None):
        super().__init__()
        cfg = config or MultiScaleGNNConfig()
        self.cfg = cfg
        self.scale_d = _ScaleGAT(cfg.n_features, cfg.hidden, cfg.heads, cfg.dropout)
        self.scale_w = _ScaleGAT(cfg.n_features, cfg.hidden, cfg.heads, cfg.dropout)
        self.scale_m = _ScaleGAT(cfg.n_features, cfg.hidden, cfg.heads, cfg.dropout)
        self.fusion = nn.Sequential(
            nn.Linear(3 * cfg.hidden, cfg.hidden),
            nn.ELU(),
            nn.Dropout(cfg.dropout),
            nn.Linear(cfg.hidden, 1),
        )

    def forward(
        self,
        x_d: torch.Tensor,
        x_w: torch.Tensor,
        x_m: torch.Tensor,
        edge_index: torch.Tensor,
        edge_weight: torch.Tensor | None = None,
    ) -> torch.Tensor:
        h_d = self.scale_d(x_d, edge_index, edge_weight)
        h_w = self.scale_w(x_w, edge_index, edge_weight)
        h_m = self.scale_m(x_m, edge_index, edge_weight)
        h = torch.cat([h_d, h_w, h_m], dim=-1)  # (N, 3*hidden)
        out = self.fusion(h).squeeze(-1)  # (N,)
        return out

    def num_parameters(self) -> int:
        return sum(p.numel() for p in self.parameters() if p.requires_grad)
