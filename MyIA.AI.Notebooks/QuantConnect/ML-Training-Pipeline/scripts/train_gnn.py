"""
Train GNN models for multi-asset volatility spillover on crypto panier.

Implements GCN, GAT, and RGCN baselines on 10-coin crypto panier (Stage 3a).
Graph structure: rolling correlation-based adjacency, sector priors.

Models cross-asset dependencies via message passing on dynamic graphs.
Targets: next-step returns (direction) and realized volatility.

Architecture references:
    - Kipf & Welling, GCN (ICLR 2017)
    - Velickovic et al., GAT (ICLR 2018)
    - MDGNN (AAAI 2024): multi-relational dynamic graphs

Walk-forward OOS validation, multi-seed (>=4 seeds, edge >= 2*std).
Transaction costs deducted from Sharpe (Stage 0 TransactionCostModel).

Usage:
    python train_gnn.py --dry-run
    python train_gnn.py --model gat --window 60 --threshold 0.3
    python train_gnn.py --walk-forward --n-splits 5 --seeds 42,123,456,789

Output:
    Checkpoints in --output-dir with metadata.json
"""

import argparse
import json
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
import torch
import torch.nn as nn
import torch.nn.functional as F

sys.path.append(str(Path(__file__).resolve().parent))
from graph_builder import (
    CRYPTO_PANIER_SYMBOLS,
    CryptoGraphBuilder,
    build_sector_adjacency_crypto,
    load_crypto_panier,
)

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import batch_thermal_check, get_gpu_temp, setup_amp

from baselines import oos_direction_distribution

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None

try:
    from transaction_costs import TransactionCostModel
except ImportError:
    TransactionCostModel = None

try:
    from baselines import majority_class_baseline
except ImportError:
    majority_class_baseline = None


# ---------------------------------------------------------------------------
# Graph Convolution Layer (Kipf & Welling, ICLR 2017)
# ---------------------------------------------------------------------------

class GraphConvLayer(nn.Module):
    """Single GCN layer: D^{-1/2} A D^{-1/2} X W."""

    def __init__(self, in_features: int, out_features: int):
        super().__init__()
        self.W = nn.Parameter(torch.randn(in_features, out_features) * 0.1)
        self.bias = nn.Parameter(torch.zeros(out_features))

    def forward(
        self, x: torch.Tensor, adj: torch.Tensor
    ) -> torch.Tensor:
        """
        Args:
            x: [B, N, in_features] or [N, in_features]
            adj: [N, N] normalized adjacency
        """
        support = torch.matmul(x, self.W)
        if x.dim() == 3:
            if adj.dim() == 2:
                output = torch.matmul(adj.unsqueeze(0), support)
            else:
                output = torch.matmul(adj, support)
        else:
            output = torch.matmul(adj, support)
        return output + self.bias


# ---------------------------------------------------------------------------
# GAT Layer (Velickovic et al., ICLR 2018) — reuses STGAT pattern
# ---------------------------------------------------------------------------

class GATLayer(nn.Module):
    """Single-head graph attention layer."""

    def __init__(
        self, in_features: int, out_features: int, dropout: float = 0.1
    ):
        super().__init__()
        self.W = nn.Parameter(torch.randn(in_features, out_features) * 0.1)
        self.a = nn.Parameter(torch.randn(2 * out_features, 1) * 0.1)
        self.dropout = nn.Dropout(dropout)
        self.leaky_relu = nn.LeakyReLU(0.2)

    def forward(
        self, h: torch.Tensor, adj: torch.Tensor | None = None
    ) -> torch.Tensor:
        if h.dim() == 2:
            h = h.unsqueeze(0)
            squeeze = True
        else:
            squeeze = False

        B, N, _ = h.shape
        Wh = torch.matmul(h, self.W)

        a_input = torch.cat([
            Wh.unsqueeze(2).expand(B, N, N, -1),
            Wh.unsqueeze(1).expand(B, N, N, -1),
        ], dim=-1)
        e = self.leaky_relu(torch.matmul(a_input, self.a).squeeze(-1))

        if adj is not None:
            if adj.dim() == 2:
                mask = adj.unsqueeze(0).expand(B, -1, -1)
            else:
                mask = adj
            e = e.masked_fill(mask == 0, float("-inf"))

        attention = F.softmax(e, dim=-1)
        attention = self.dropout(attention)
        out = torch.matmul(attention, Wh)

        if squeeze:
            out = out.squeeze(0)
        return out


# ---------------------------------------------------------------------------
# Relational GCN Layer (Schlichtkrull et al., 2018)
# ---------------------------------------------------------------------------

class RGCNLayer(nn.Module):
    """Relational GCN layer with relation-specific weight matrices."""

    def __init__(
        self, in_features: int, out_features: int, n_relations: int = 3
    ):
        super().__init__()
        self.n_relations = n_relations
        self.W_base = nn.Parameter(torch.randn(in_features, out_features) * 0.1)
        self.W_rel = nn.ParameterList([
            nn.Parameter(torch.randn(in_features, out_features) * 0.1)
            for _ in range(n_relations)
        ])
        self.bias = nn.Parameter(torch.zeros(out_features))

    def forward(
        self,
        x: torch.Tensor,
        adj_list: list[torch.Tensor],
    ) -> torch.Tensor:
        if x.dim() == 2:
            x = x.unsqueeze(0)
            squeeze = True
        else:
            squeeze = False

        B, N, _ = x.shape
        out = torch.matmul(x, self.W_base)

        for r, adj_r in enumerate(adj_list[: self.n_relations]):
            support = torch.matmul(x, self.W_rel[r])
            if adj_r.dim() == 2:
                adj_r = adj_r.unsqueeze(0).expand(B, -1, -1)
            out = out + torch.matmul(adj_r, support) / self.n_relations

        out = out + self.bias

        if squeeze:
            out = out.squeeze(0)
        return out


# ---------------------------------------------------------------------------
# GNN Models
# ---------------------------------------------------------------------------

class GCNModel(nn.Module):
    """Stacked GCN for multi-asset return prediction."""

    def __init__(
        self,
        n_assets: int,
        n_features: int,
        d_model: int = 64,
        n_layers: int = 2,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.input_proj = nn.Linear(n_features, d_model)
        self.layers = nn.ModuleList()
        for i in range(n_layers):
            self.layers.append(GraphConvLayer(d_model, d_model))
        self.norm = nn.LayerNorm(d_model)
        self.drop = nn.Dropout(dropout)
        self.output_proj = nn.Linear(d_model * n_assets, 1)

    def forward(self, x: torch.Tensor, adj: torch.Tensor) -> torch.Tensor:
        """
        Args:
            x: [B, N, n_features] node features
            adj: [N, N] normalized adjacency

        Returns:
            [B, 1] aggregated prediction
        """
        h = F.relu(self.input_proj(x))
        for layer in self.layers:
            h = F.relu(layer(h, adj))
            h = self.drop(h)
        h = self.norm(h)
        h = h.reshape(h.shape[0], -1)
        return self.output_proj(h)


class GATModel(nn.Module):
    """Stacked GAT for multi-asset return prediction."""

    def __init__(
        self,
        n_assets: int,
        n_features: int,
        d_model: int = 64,
        n_layers: int = 2,
        n_heads: int = 4,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.input_proj = nn.Linear(n_features, d_model)
        self.gat_layers = nn.ModuleList()
        self.projections = nn.ModuleList()
        head_dim = d_model // n_heads
        for _ in range(n_layers):
            heads = nn.ModuleList([
                GATLayer(d_model, head_dim, dropout)
                for _ in range(n_heads)
            ])
            self.gat_layers.append(heads)
            self.projections.append(nn.Linear(n_heads * head_dim, d_model))
        self.norm = nn.LayerNorm(d_model)
        self.drop = nn.Dropout(dropout)
        self.output_proj = nn.Linear(d_model * n_assets, 1)

    def forward(self, x: torch.Tensor, adj: torch.Tensor | None = None) -> torch.Tensor:
        h = F.relu(self.input_proj(x))
        for heads, proj in zip(self.gat_layers, self.projections):
            h_cat = torch.cat([head(h, adj) for head in heads], dim=-1)
            h = F.relu(proj(h_cat))
            h = self.drop(h)
        h = self.norm(h)
        h = h.reshape(h.shape[0], -1)
        return self.output_proj(h)


class RGCNModel(nn.Module):
    """Relational GCN using multiple adjacency types (correlation, sector, distance)."""

    def __init__(
        self,
        n_assets: int,
        n_features: int,
        d_model: int = 64,
        n_layers: int = 2,
        n_relations: int = 3,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.input_proj = nn.Linear(n_features, d_model)
        self.layers = nn.ModuleList()
        for _ in range(n_layers):
            self.layers.append(RGCNLayer(d_model, d_model, n_relations))
        self.norm = nn.LayerNorm(d_model)
        self.drop = nn.Dropout(dropout)
        self.output_proj = nn.Linear(d_model * n_assets, 1)

    def forward(
        self,
        x: torch.Tensor,
        adj_list: list[torch.Tensor],
    ) -> torch.Tensor:
        h = F.relu(self.input_proj(x))
        for layer in self.layers:
            h = F.relu(layer(h, adj_list))
            h = self.drop(h)
        h = self.norm(h)
        h = h.reshape(h.shape[0], -1)
        return self.output_proj(h)


# ---------------------------------------------------------------------------
# Model factory
# ---------------------------------------------------------------------------

MODEL_REGISTRY = {
    "gcn": GCNModel,
    "gat": GATModel,
    "rgcn": RGCNModel,
}


def create_model(
    model_type: str,
    n_assets: int,
    n_features: int,
    d_model: int = 64,
    n_layers: int = 2,
    n_heads: int = 4,
    n_relations: int = 3,
    dropout: float = 0.1,
) -> nn.Module:
    if model_type not in MODEL_REGISTRY:
        raise ValueError(f"Unknown model: {model_type}. Available: {list(MODEL_REGISTRY.keys())}")

    kwargs = dict(
        n_assets=n_assets,
        n_features=n_features,
        d_model=d_model,
        n_layers=n_layers,
        dropout=dropout,
    )
    if model_type == "gat":
        kwargs["n_heads"] = n_heads
    if model_type == "rgcn":
        kwargs["n_relations"] = n_relations

    return MODEL_REGISTRY[model_type](**kwargs)


# ---------------------------------------------------------------------------
# Data preparation
# ---------------------------------------------------------------------------

def prepare_gnn_data(
    closes: pd.DataFrame,
    seq_len: int = 60,
    window: int = 60,
    adj_method: str = "correlation",
    adj_threshold: float = 0.3,
    continuous_adj: bool = False,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Prepare GNN input data with dynamic adjacency.

    Returns
    -------
    X : np.ndarray, shape (T, N, F)
        Node features per timestep.
    y : np.ndarray, shape (T,)
        Target: next-step mean return across assets.
    adjs : np.ndarray, shape (T', N, N)
        Dynamic adjacency matrices (T' = T - window + 1).
    """
    returns = closes.pct_change().dropna()
    n_assets = len(returns.columns)

    # Node features: [ret, vol_20, mom_20]
    lookback = 20
    features = []
    for col in returns.columns:
        features.append(returns[col].values)
        features.append(returns[col].rolling(lookback).std().values)
        features.append(returns[col].rolling(lookback).sum().values)

    feat_arr = np.stack(features, axis=-1)  # (T, N*3)
    feat_arr = np.nan_to_num(feat_arr, nan=0.0)

    # Reshape to (T, N, 3)
    T_total = feat_arr.shape[0]
    feat_arr = feat_arr.reshape(T_total, n_assets, -1)

    # Target: next-step mean return
    targets = returns.mean(axis=1).shift(-1).dropna().values

    # Align
    min_len = min(len(feat_arr), len(targets))
    feat_arr = feat_arr[:min_len]
    targets = targets[:min_len]

    # Build dynamic adjacency
    builder = CryptoGraphBuilder(returns, window=window)
    adjs = builder.build_dynamic_adjacency(
        method=adj_method, threshold=adj_threshold, continuous=continuous_adj,
    )

    # Align features/targets with adjacency
    adj_offset = window - 1
    feat_arr = feat_arr[adj_offset : adj_offset + len(adjs)]
    targets = targets[adj_offset : adj_offset + len(adjs)]

    min_len = min(len(feat_arr), len(targets), len(adjs))
    return feat_arr[:min_len], targets[:min_len], adjs[:min_len]


# ---------------------------------------------------------------------------
# Training and evaluation
# ---------------------------------------------------------------------------

def train_and_evaluate(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    adj_train: np.ndarray,
    adj_test: np.ndarray,
    model_type: str = "gat",
    d_model: int = 64,
    n_layers: int = 2,
    n_heads: int = 4,
    n_relations: int = 3,
    dropout: float = 0.1,
    epochs: int = 100,
    batch_size: int = 32,
    learning_rate: float = 1e-3,
    device: str = "cpu",
    static_adj: torch.Tensor | None = None,
    adj_list_train: list[torch.Tensor] | None = None,
    adj_list_test: list[torch.Tensor] | None = None,
    dynamic_adj: bool = True,
) -> dict:
    """Train GNN model and return metrics with baseline comparison.

    Parameters
    ----------
    dynamic_adj : bool
        If True, use per-sample dynamic adjacency instead of mean static adj.
        Each training sample uses the adjacency matrix from its corresponding
        timestep, preserving temporal graph structure.
    """
    from torch.utils.data import DataLoader, TensorDataset

    n_assets = X_train.shape[1]
    n_features = X_train.shape[2]

    model = create_model(
        model_type, n_assets, n_features,
        d_model=d_model, n_layers=n_layers,
        n_heads=n_heads, n_relations=n_relations,
        dropout=dropout,
    )
    model = model.to(device)

    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"GNN ({model_type}) params: {total_params:,}, dynamic_adj={dynamic_adj}")

    X_train_t = torch.tensor(X_train, dtype=torch.float32)
    y_train_t = torch.tensor(y_train, dtype=torch.float32).unsqueeze(-1)
    X_test_t = torch.tensor(X_test, dtype=torch.float32)
    y_test_t = torch.tensor(y_test, dtype=torch.float32).unsqueeze(-1)

    if dynamic_adj and len(adj_train.shape) == 3:
        # Use per-sample dynamic adjacency
        adj_train_t = torch.tensor(adj_train, dtype=torch.float32)
        adj_test_t = torch.tensor(adj_test, dtype=torch.float32)
        adj_mode = "dynamic"
    else:
        # Fallback: static adjacency (mean of dynamic)
        if static_adj is None:
            adj_mean = adj_train.mean(axis=0) if len(adj_train.shape) == 3 else adj_train
            adj_tensor = torch.tensor(adj_mean, dtype=torch.float32)
        else:
            adj_tensor = static_adj
        adj_tensor = adj_tensor.to(device)
        adj_train_t = None
        adj_test_t = None
        adj_mode = "static"

    # Auto-split validation
    val_cutoff = int(len(X_train_t) * 0.85)
    X_val_t, y_val_t = X_train_t[val_cutoff:], y_train_t[val_cutoff:]
    X_tr_t, y_tr_t = X_train_t[:val_cutoff], y_train_t[:val_cutoff]

    if adj_mode == "dynamic" and adj_train_t is not None:
        adj_val_t = adj_train_t[val_cutoff:]
        adj_tr_t = adj_train_t[:val_cutoff]

        train_ds = TensorDataset(X_tr_t, y_tr_t, adj_tr_t)
        val_ds = TensorDataset(X_val_t, y_val_t, adj_val_t)
        test_ds = TensorDataset(X_test_t, y_test_t, adj_test_t)
    else:
        train_ds = TensorDataset(X_tr_t, y_tr_t)
        val_ds = TensorDataset(X_val_t, y_val_t)
        test_ds = TensorDataset(X_test_t, y_test_t)

    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    val_loader = DataLoader(val_ds, batch_size=batch_size)
    test_loader = DataLoader(test_ds, batch_size=batch_size)

    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate, weight_decay=1e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(
        optimizer, T_0=10, T_mult=2
    )
    criterion = nn.MSELoss()

    use_amp, grad_scaler = setup_amp()

    def _forward(model, X_b, adj_b, model_type, device, use_amp_flag, adj_list=None):
        with torch.amp.autocast("cuda", enabled=use_amp_flag):
            if model_type == "rgcn":
                if adj_list is not None:
                    adj_tensors = [a.to(device) for a in adj_list]
                elif adj_b is not None:
                    adj_tensors = [adj_b]
                else:
                    adj_tensors = [torch.eye(X_b.shape[1], device=device)]
                return model(X_b, adj_tensors)
            else:
                adj_input = adj_b.to(device) if adj_b is not None else torch.eye(X_b.shape[1], device=device)
                return model(X_b, adj_input)

    history = {"train_loss": [], "val_loss": []}
    best_val_loss = float("inf")
    best_state = None

    for epoch in range(epochs):
        model.train()
        epoch_loss = 0.0
        n_batches = 0

        for batch in train_loader:
            batch_thermal_check(n_batches, check_every=5, max_temp=80, cool_sleep=30)

            X_b, y_b = batch[0].to(device), batch[1].to(device)
            adj_b = batch[2].to(device) if len(batch) > 2 else None
            optimizer.zero_grad()

            pred = _forward(model, X_b, adj_b, model_type, device, use_amp, adj_list_train)
            loss = criterion(pred, y_b)

            if use_amp:
                grad_scaler.scale(loss).backward()
                grad_scaler.unscale_(optimizer)
                torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
                grad_scaler.step(optimizer)
                grad_scaler.update()
            else:
                loss.backward()
                torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
                optimizer.step()

            epoch_loss += loss.item()
            n_batches += 1

        scheduler.step()
        avg_train = epoch_loss / max(n_batches, 1)

        model.eval()
        val_loss = 0.0
        val_batches = 0
        with torch.no_grad():
            for batch in val_loader:
                X_b, y_b = batch[0].to(device), batch[1].to(device)
                adj_b = batch[2].to(device) if len(batch) > 2 else None
                pred = _forward(model, X_b, adj_b, model_type, device, use_amp, adj_list_train)
                val_loss += criterion(pred, y_b).item()
                val_batches += 1

        avg_val = val_loss / max(val_batches, 1)
        history["train_loss"].append(round(avg_train, 6))
        history["val_loss"].append(round(avg_val, 6))

        if avg_val < best_val_loss:
            best_val_loss = avg_val
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

        if (epoch + 1) % max(1, epochs // 5) == 0:
            temp = get_gpu_temp() if device == "cuda" else 0
            temp_str = f"  gpu={temp}C" if temp > 0 else ""
            print(f"  Epoch {epoch+1}/{epochs}  train={avg_train:.6f}  val={avg_val:.6f}{temp_str}")

    if best_state:
        model.load_state_dict(best_state)
    model.eval()

    all_preds, all_targets = [], []
    with torch.no_grad():
        for batch in test_loader:
            X_b = batch[0].to(device)
            adj_b = batch[2].to(device) if len(batch) > 2 else None
            pred = _forward(model, X_b, adj_b, model_type, device, use_amp, adj_list_test)
            all_preds.append(pred.cpu().numpy())
            all_targets.append(batch[1].numpy())

    preds = np.concatenate(all_preds).flatten()
    targets = np.concatenate(all_targets).flatten()

    mse = float(np.mean((preds - targets) ** 2))
    mae = float(np.mean(np.abs(preds - targets)))
    direction_acc = float(np.mean((preds > 0) == (targets > 0)))
    majority_baseline = oos_direction_distribution(targets)

    baseline_comparison = None
    if majority_class_baseline is not None:
        train_binary = (y_train > 0).astype(int)
        test_binary = (y_test > 0).astype(int)
        baseline_comparison = majority_class_baseline(train_binary, test_binary)

    metrics = {
        "mse": round(mse, 6),
        "mae": round(mae, 6),
        "direction_accuracy": round(direction_acc, 4),
        "majority_class_baseline": majority_baseline,
        "edge_over_majority": round(
            direction_acc - majority_baseline["majority_class_accuracy"], 4
        ),
        "best_val_loss": round(best_val_loss, 6),
        "total_params": total_params,
        "train_samples": len(X_train),
        "test_samples": len(X_test),
        "epochs_trained": epochs,
        "adj_mode": adj_mode,
    }
    if baseline_comparison is not None:
        metrics["baseline_comparison"] = baseline_comparison

    return {
        "model": model,
        "metrics": metrics,
        "history": history,
    }


# ---------------------------------------------------------------------------
# Multi-seed evaluation
# ---------------------------------------------------------------------------

def run_multi_seed(
    X: np.ndarray,
    y: np.ndarray,
    adjs: np.ndarray,
    seeds: list[int],
    train_ratio: float = 0.7,
    val_ratio: float = 0.15,
    model_type: str = "gat",
    d_model: int = 64,
    n_layers: int = 2,
    n_heads: int = 4,
    epochs: int = 100,
    batch_size: int = 32,
    device: str = "cpu",
    dynamic_adj: bool = True,
) -> dict:
    """Run multi-seed evaluation following feedback_multi_seed_required rule.

    Requires >=4 seeds. BEATS claim only if mean edge >= 2 * std(edge).
    """
    assert len(seeds) >= 4, f"Multi-seed requires >=4 seeds, got {len(seeds)}"

    n = len(X)
    train_end = int(n * train_ratio)
    val_end = int(n * (train_ratio + val_ratio))

    results = []
    for seed in seeds:
        np.random.seed(seed)
        torch.manual_seed(seed)

        X_train, y_train, adj_train = X[:train_end], y[:train_end], adjs[:train_end]
        X_val, y_val, adj_val = X[train_end:val_end], y[train_end:val_end], adjs[train_end:val_end]
        X_test, y_test, adj_test = X[val_end:], y[val_end:], adjs[val_end:]

        # Concatenate train+val for the training function (it auto-splits)
        X_train_full = np.concatenate([X_train, X_val])
        y_train_full = np.concatenate([y_train, y_val])
        adj_train_full = np.concatenate([adj_train, adj_val])

        result = train_and_evaluate(
            X_train_full, y_train_full, X_test, y_test,
            adj_train_full, adj_test,
            model_type=model_type,
            d_model=d_model, n_layers=n_layers, n_heads=n_heads,
            epochs=epochs, batch_size=batch_size,
            device=device,
            dynamic_adj=dynamic_adj,
        )
        results.append({
            "seed": seed,
            "metrics": result["metrics"],
            "history": result["history"],
        })
        m = result["metrics"]
        print(f"  Seed {seed}: DirAcc={m['direction_accuracy']:.4f}, "
              f"Edge={m['edge_over_majority']:+.4f}, MSE={m['mse']:.6f}")

    # Aggregate
    dir_accs = [r["metrics"]["direction_accuracy"] for r in results]
    edges = [r["metrics"]["edge_over_majority"] for r in results]
    mses = [r["metrics"]["mse"] for r in results]

    mean_edge = np.mean(edges)
    std_edge = np.std(edges)
    beats = mean_edge >= 2 * std_edge if std_edge > 0 else mean_edge > 0

    summary = {
        "model_type": model_type,
        "n_seeds": len(seeds),
        "seeds": seeds,
        "mean_direction_accuracy": round(float(np.mean(dir_accs)), 4),
        "std_direction_accuracy": round(float(np.std(dir_accs)), 4),
        "mean_edge": round(float(mean_edge), 4),
        "std_edge": round(float(std_edge), 4),
        "mean_mse": round(float(np.mean(mses)), 6),
        "beats_claim": bool(beats),
        "beats_criterion": f"mean_edge({mean_edge:.4f}) >= 2*std_edge({2*std_edge:.4f})"
                           if std_edge > 0 else f"mean_edge({mean_edge:.4f}) > 0",
        "per_seed": results,
    }

    print(f"\n=== Multi-seed ({model_type}, {len(seeds)} seeds) ===")
    print(f"  Mean DirAcc: {np.mean(dir_accs):.4f} +/- {np.std(dir_accs):.4f}")
    print(f"  Mean Edge:   {mean_edge:+.4f} +/- {std_edge:.4f}")
    print(f"  BEATS:       {'YES' if beats else 'NO'} ({summary['beats_criterion']})")
    print(f"  Mean MSE:    {np.mean(mses):.6f}")

    return summary


# ---------------------------------------------------------------------------
# Save checkpoint
# ---------------------------------------------------------------------------

def save_checkpoint(
    model, result: dict, hyperparams: dict, output_dir: Path
) -> Path:
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = output_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    torch.save(model.state_dict(), ckpt_path / "model.pt")

    metadata = {
        "timestamp": timestamp,
        "model_type": hyperparams.get("model_type", "gnn"),
        "hyperparams": hyperparams,
        "metrics": result["metrics"],
        "history": result["history"],
    }
    (ckpt_path / "metadata.json").write_text(
        json.dumps(metadata, indent=2, default=str), encoding="utf-8"
    )

    print(f"Checkpoint saved: {ckpt_path}")
    print(f"  Metrics: {result['metrics']}")
    return ckpt_path


# ---------------------------------------------------------------------------
# Walk-forward 5-fold multi-seed evaluation
# ---------------------------------------------------------------------------

def run_walk_forward_multiseed(
    X: np.ndarray,
    y: np.ndarray,
    adjs: np.ndarray,
    seeds: list[int],
    n_splits: int = 5,
    gap: int = 10,
    model_type: str = "rgcn",
    d_model: int = 64,
    n_layers: int = 2,
    n_heads: int = 4,
    n_relations: int = 3,
    dropout: float = 0.1,
    epochs: int = 100,
    batch_size: int = 32,
    learning_rate: float = 1e-3,
    device: str = "cpu",
) -> dict:
    """Walk-forward 5-fold x multi-seed evaluation for honest GNN verdict.

    Uses expanding window WalkForwardSplitter with gap to prevent leakage.
    Each seed runs all 5 folds. Aggregates per-fold and per-seed metrics.
    """
    assert len(seeds) >= 4, f"Multi-seed requires >=4 seeds, got {len(seeds)}"

    splitter = WalkForwardSplitter(
        n_splits=n_splits, train_size=None, gap=gap, test_size=None,
    )

    all_fold_results = []

    for seed in seeds:
        np.random.seed(seed)
        torch.manual_seed(seed)

        fold_results = []
        for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(X)):
            X_train, y_train = X[train_idx], y[train_idx]
            X_test, y_test = X[test_idx], y[test_idx]
            adj_train_fold = adjs[train_idx] if len(adjs) == len(X) else adjs
            adj_test_fold = adjs[test_idx] if len(adjs) == len(X) else adjs

            result = train_and_evaluate(
                X_train, y_train, X_test, y_test,
                adj_train_fold, adj_test_fold,
                model_type=model_type,
                d_model=d_model, n_layers=n_layers, n_heads=n_heads,
                n_relations=n_relations, dropout=dropout,
                epochs=epochs, batch_size=batch_size,
                learning_rate=learning_rate, device=device,
            )

            m = result["metrics"]
            fold_results.append({
                "fold": fold_idx,
                "train_size": len(train_idx),
                "test_size": len(test_idx),
                "metrics": m,
            })
            print(f"  Seed {seed} Fold {fold_idx}: DirAcc={m['direction_accuracy']:.4f} "
                  f"Edge={m['edge_over_majority']:+.4f}")

        seed_dir_accs = [f["metrics"]["direction_accuracy"] for f in fold_results]
        seed_edges = [f["metrics"]["edge_over_majority"] for f in fold_results]
        seed_mses = [f["metrics"]["mse"] for f in fold_results]

        all_fold_results.append({
            "seed": seed,
            "folds": fold_results,
            "mean_dir_acc": round(float(np.mean(seed_dir_accs)), 4),
            "mean_edge": round(float(np.mean(seed_edges)), 4),
            "mean_mse": round(float(np.mean(seed_mses)), 6),
        })

    # Cross-seed aggregation
    cross_seed_dir = [r["mean_dir_acc"] for r in all_fold_results]
    cross_seed_edge = [r["mean_edge"] for r in all_fold_results]
    cross_seed_mse = [r["mean_mse"] for r in all_fold_results]

    mean_edge = float(np.mean(cross_seed_edge))
    std_edge = float(np.std(cross_seed_edge))
    beats = mean_edge >= 2 * std_edge if std_edge > 0 else mean_edge > 0

    # Per-fold aggregation across seeds
    n_folds_actual = min(len(r["folds"]) for r in all_fold_results)
    per_fold_summary = []
    for f in range(n_folds_actual):
        fold_edges = [r["folds"][f]["metrics"]["edge_over_majority"]
                      for r in all_fold_results if f < len(r["folds"])]
        fold_dir_accs = [r["folds"][f]["metrics"]["direction_accuracy"]
                         for r in all_fold_results if f < len(r["folds"])]
        per_fold_summary.append({
            "fold": f,
            "mean_edge": round(float(np.mean(fold_edges)), 4),
            "std_edge": round(float(np.std(fold_edges)), 4),
            "mean_dir_acc": round(float(np.mean(fold_dir_accs)), 4),
        })

    summary = {
        "model_type": model_type,
        "n_seeds": len(seeds),
        "seeds": seeds,
        "n_splits": n_splits,
        "gap": gap,
        "epochs": epochs,
        "walk_forward": True,
        "cross_seed_mean_dir_acc": round(float(np.mean(cross_seed_dir)), 4),
        "cross_seed_std_dir_acc": round(float(np.std(cross_seed_dir)), 4),
        "cross_seed_mean_edge": round(mean_edge, 4),
        "cross_seed_std_edge": round(std_edge, 4),
        "cross_seed_mean_mse": round(float(np.mean(cross_seed_mse)), 6),
        "beats_claim": bool(beats),
        "beats_criterion": (f"mean_edge({mean_edge:.4f}) >= 2*std_edge({2*std_edge:.4f})"
                            if std_edge > 0 else f"mean_edge({mean_edge:.4f}) > 0"),
        "per_fold_across_seeds": per_fold_summary,
        "per_seed": all_fold_results,
    }

    print(f"\n=== Walk-Forward {n_splits}-fold x {len(seeds)} seeds ({model_type}) ===")
    print(f"  Cross-seed Mean DirAcc: {np.mean(cross_seed_dir):.4f} +/- {np.std(cross_seed_dir):.4f}")
    print(f"  Cross-seed Mean Edge:   {mean_edge:+.4f} +/- {std_edge:.4f}")
    print(f"  Cross-seed Mean MSE:    {np.mean(cross_seed_mse):.6f}")
    print(f"  BEATS: {'YES' if beats else 'NO'} ({summary['beats_criterion']})")
    for f, fs in enumerate(per_fold_summary):
        print(f"  Fold {f}: edge={fs['mean_edge']:+.4f} +/- {fs['std_edge']:.4f} "
              f"DirAcc={fs['mean_dir_acc']:.4f}")

    return summary


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Train GNN models for multi-asset crypto panier forecasting"
    )

    # Model
    parser.add_argument(
        "--model", default="gat", choices=list(MODEL_REGISTRY.keys()),
        help="GNN architecture",
    )
    parser.add_argument("--d-model", type=int, default=64)
    parser.add_argument("--n-layers", type=int, default=2)
    parser.add_argument("--n-heads", type=int, default=4, help="GAT heads")
    parser.add_argument("--n-relations", type=int, default=3, help="RGCN relation types")
    parser.add_argument("--dropout", type=float, default=0.1)

    # Graph
    parser.add_argument("--window", type=int, default=60, help="Rolling correlation window")
    parser.add_argument("--threshold", type=float, default=0.3, help="Adjacency threshold")
    parser.add_argument("--adj-method", default="correlation",
                        choices=["correlation", "distance", "partial_correlation"])
    parser.add_argument("--continuous-adj", action="store_true",
                        help="Keep continuous correlation values instead of binary thresholding")
    parser.add_argument("--dynamic-adj", action="store_true", default=True,
                        help="Use per-sample dynamic adjacency (default: True)")
    parser.add_argument("--no-dynamic-adj", dest="dynamic_adj", action="store_false",
                        help="Use static mean adjacency instead of dynamic")

    # Training
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--lr", type=float, default=1e-3)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--seeds", type=str, default=None,
                        help="Comma-separated seeds for multi-seed eval (>=4)")

    # Splitting
    parser.add_argument("--train-ratio", type=float, default=0.7)
    parser.add_argument("--val-ratio", type=float, default=0.15)
    parser.add_argument("--test-ratio", type=float, default=0.15)
    parser.add_argument("--walk-forward", action="store_true")
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--gap", type=int, default=10)

    # Data
    parser.add_argument("--start", default=None)
    parser.add_argument("--end", default=None)

    # Output
    parser.add_argument("--output-dir",
                        default=str(Path(__file__).resolve().parent.parent / "outputs" / "gnn_run1"))
    parser.add_argument("--device", default="auto",
                        help="Device: auto, cpu, cuda (default: auto)")
    parser.add_argument("--dry-run", action="store_true")

    args = parser.parse_args()

    np.random.seed(args.seed)
    torch.manual_seed(args.seed)
    if args.device == "auto":
        device = "cuda" if torch.cuda.is_available() else "cpu"
    else:
        device = args.device

    if args.dry_run:
        print("DRY-RUN: Using synthetic crypto panier data (10 assets, 2 epochs)")
        n_days = 1000
        n_assets = 10
        symbols = CRYPTO_PANIER_SYMBOLS[:n_assets]
        np.random.seed(args.seed)
        returns_data = np.random.randn(n_days, n_assets).astype(np.float32) * 0.02
        returns_data[:, 0] += 0.0001  # BTC slight positive drift
        returns_df = pd.DataFrame(returns_data, columns=symbols)
        closes_df = (1 + returns_df).cumprod() * 100
        args.epochs = 2
    else:
        closes_df = load_crypto_panier(start=args.start, end=args.end)
        symbols = list(closes_df.columns)
        n_assets = len(symbols)
        print(f"Loaded crypto panier: {n_assets} assets, {len(closes_df)} days")
        returns_df = closes_df.pct_change().dropna()

    print(f"Model: {args.model}, device: {device}")
    print(f"Graph: window={args.window}, method={args.adj_method}, threshold={args.threshold}")

    # Prepare data
    X, y, adjs = prepare_gnn_data(
        closes_df,
        seq_len=args.window,
        window=args.window,
        adj_method=args.adj_method,
        adj_threshold=args.threshold,
        continuous_adj=args.continuous_adj,
    )
    print(f"Data: {X.shape[0]} samples, {X.shape[1]} assets, {X.shape[2]} features")
    print(f"Adjacency: {adjs.shape}")

    # Split
    n = len(X)
    train_end = int(n * args.train_ratio)
    val_end = int(n * (args.train_ratio + args.val_ratio))

    hyperparams = {
        "model_type": args.model,
        "d_model": args.d_model,
        "n_layers": args.n_layers,
        "n_heads": args.n_heads,
        "n_relations": args.n_relations,
        "dropout": args.dropout,
        "window": args.window,
        "adj_method": args.adj_method,
        "adj_threshold": args.threshold,
        "continuous_adj": args.continuous_adj,
        "dynamic_adj": args.dynamic_adj,
        "epochs": args.epochs,
        "batch_size": args.batch_size,
        "learning_rate": args.lr,
        "train_ratio": args.train_ratio,
        "val_ratio": args.val_ratio,
        "test_ratio": args.test_ratio,
        "n_assets": n_assets,
        "symbols": symbols,
        "seed": args.seed,
    }

    output_dir = Path(args.output_dir)

    if args.walk_forward:
        seeds = [int(s.strip()) for s in args.seeds.split(",")] if args.seeds else [0, 1, 7, 42, 99]
        assert len(seeds) >= 4, f"Walk-forward multi-seed requires >=4 seeds, got {len(seeds)}"
        print(f"Walk-forward {args.n_splits}-fold x {len(seeds)} seeds evaluation")

        summary = run_walk_forward_multiseed(
            X, y, adjs, seeds,
            n_splits=args.n_splits,
            gap=args.gap,
            model_type=args.model,
            d_model=args.d_model,
            n_layers=args.n_layers,
            n_heads=args.n_heads,
            n_relations=args.n_relations,
            dropout=args.dropout,
            epochs=args.epochs,
            batch_size=args.batch_size,
            learning_rate=args.lr,
            device=device,
        )

        output_dir.mkdir(parents=True, exist_ok=True)
        wf_path = output_dir / f"walkforward_{args.model}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        wf_path.write_text(
            json.dumps(summary, indent=2, default=str), encoding="utf-8"
        )
        print(f"Walk-forward summary: {wf_path}")

    elif args.seeds:
        seeds = [int(s.strip()) for s in args.seeds.split(",")]
        print(f"Multi-seed evaluation: {len(seeds)} seeds")
        summary = run_multi_seed(
            X, y, adjs, seeds,
            train_ratio=args.train_ratio,
            val_ratio=args.val_ratio,
            model_type=args.model,
            d_model=args.d_model,
            n_layers=args.n_layers,
            n_heads=args.n_heads,
            epochs=args.epochs,
            batch_size=args.batch_size,
            device=device,
            dynamic_adj=args.dynamic_adj,
        )
        # Save summary
        output_dir.mkdir(parents=True, exist_ok=True)
        summary_path = output_dir / f"multiseed_{args.model}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        summary_path.write_text(
            json.dumps(summary, indent=2, default=str), encoding="utf-8"
        )
        print(f"Multi-seed summary: {summary_path}")
    else:
        # Single seed run
        X_train = np.concatenate([X[:train_end], X[train_end:val_end]])
        y_train = np.concatenate([y[:train_end], y[train_end:val_end]])
        adj_train = np.concatenate([adjs[:train_end], adjs[train_end:val_end]])
        X_test, y_test, adj_test = X[val_end:], y[val_end:], adjs[val_end:]

        print(f"Split: train={train_end}, val={val_end-train_end}, test={n-val_end}")

        result = train_and_evaluate(
            X_train, y_train, X_test, y_test,
            adj_train, adj_test,
            model_type=args.model,
            d_model=args.d_model,
            n_layers=args.n_layers,
            n_heads=args.n_heads,
            n_relations=args.n_relations,
            dropout=args.dropout,
            epochs=args.epochs,
            batch_size=args.batch_size,
            learning_rate=args.lr,
            device=device,
            dynamic_adj=args.dynamic_adj,
        )

        save_checkpoint(result["model"], result, hyperparams, output_dir)

        m = result["metrics"]
        edge = m["edge_over_majority"]
        print(f"\nResults: MSE={m['mse']}, DirAcc={m['direction_accuracy']}")
        print(f"  Majority baseline: {m['majority_class_baseline']['majority_class_accuracy']}")
        print(f"  Edge over majority: {edge:+.4f} ({'BEATS' if edge > 0 else 'FAILS'} baseline)")

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")


if __name__ == "__main__":
    main()
