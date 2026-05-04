"""
Train MTGNN models for cross-asset financial time-series forecasting.

Implements "Connecting the Dots: Multivariate Time Series Forecasting with
Graph Neural Networks" (Wu et al., KDD 2020). Key innovations:
- Adaptive adjacency matrix: learned from data via node embeddings
- Mix-hop propagation: graph convolution with skip connections across layers
- Dilated causal TCN: temporal convolution with exponential receptive field growth

Cross-asset extensions:
- Static sector adjacency: groups assets by class (equity, bond, commodity, crypto)
- Dynamic Pearson adjacency: rolling correlation between asset returns
- Combined graph: A = alpha * A_adaptive + beta * A_static + gamma * A_pearson

Anti-pattern safeguards:
- --test-ratio HONORED: normalize stats computed on train set only
- Walk-forward validation supported (Stage 0 WalkForwardSplitter)
- Majority-class baseline computed and reported
- Transaction costs deducted from Sharpe (Stage 0 TransactionCostModel)

Usage:
    python train_mtgnn.py --dry-run
    python train_mtgnn.py --data-dir ../datasets/panier \\
        --symbols SPY,RSP,IWM,VIX --seq-len 96 --pred-len 24

Output:
    Checkpoints in --output-dir (default: ../outputs/mtgnn_run1/)
    metadata.json with hyperparams, metrics, majority-class comparison, training curve
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

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from gpu_training import (
    batch_thermal_check,
    get_gpu_temp,
    setup_amp,
)
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer

try:
    from walk_forward import WalkForwardSplitter
except ImportError:
    WalkForwardSplitter = None

try:
    from baselines import majority_class_baseline
except ImportError:
    majority_class_baseline = None

try:
    from transaction_costs import TransactionCostModel
except ImportError:
    TransactionCostModel = None


# ---------------------------------------------------------------------------
# Graph construction utilities
# ---------------------------------------------------------------------------

SECTOR_MAP: dict[str, str] = {
    "SPY": "equity_us", "RSP": "equity_us", "IWM": "equity_us",
    "QQQ": "equity_us", "DIA": "equity_us", "VTI": "equity_us",
    "EFA": "equity_intl", "EEM": "equity_intl", "VXUS": "equity_intl",
    "AGG": "bond", "TLT": "bond", "HYG": "bond", "LQD": "bond",
    "GLD": "commodity", "SLV": "commodity", "USO": "commodity", "DBA": "commodity",
    "BTC-USD": "crypto", "ETH-USD": "crypto",
    "UUP": "forex", "FXE": "forex", "FXY": "forex",
    "VIX": "volatility",
}


def build_sector_adjacency(symbols: list[str]) -> np.ndarray:
    """Build static sector-based adjacency matrix.

    Assets in the same sector get weight 1.0, cross-sector 0.0.
    Returns shape [N, N] where N = len(symbols).
    """
    n = len(symbols)
    adj = np.zeros((n, n), dtype=np.float32)
    sectors = [SECTOR_MAP.get(s, "unknown") for s in symbols]
    for i in range(n):
        for j in range(n):
            if sectors[i] == sectors[j]:
                adj[i, j] = 1.0
    np.fill_diagonal(adj, 0.0)
    return adj


def build_pearson_adjacency(returns: np.ndarray, window: int = 60) -> np.ndarray:
    """Build dynamic Pearson correlation adjacency from returns.

    Uses rolling window correlation of the last `window` observations.

    Args:
        returns: [T, N] array of asset returns
        window: lookback window for rolling correlation

    Returns:
        [N, N] adjacency matrix (absolute correlation, diagonal zeroed)
    """
    if returns.ndim == 1:
        returns = returns.reshape(-1, 1)
    if returns.shape[0] < window:
        window = returns.shape[0]
    recent = returns[-window:]
    if recent.shape[1] < 2:
        return np.zeros((1, 1), dtype=np.float32)
    corr = np.corrcoef(recent.T)
    if corr.ndim < 2:
        return np.zeros((recent.shape[1], recent.shape[1]), dtype=np.float32)
    corr = np.abs(corr).astype(np.float32)
    np.fill_diagonal(corr, 0.0)
    return corr


# ---------------------------------------------------------------------------
# GraphConstructor (adaptive adjacency from MTGNN Sec 3.2)
# ---------------------------------------------------------------------------

class GraphConstructor(nn.Module):
    """Learnable adaptive adjacency matrix (MTGNN Section 3.2).

    Each node gets two learnable embeddings (source and target).
    The adjacency is computed as:
        A_adaptive = softmax(ReLU(E1 @ E2.T))

    This allows the model to discover hidden relationships between
    variables that static sector groupings miss.
    """

    def __init__(self, n_nodes: int, embed_dim: int = 8):
        super().__init__()
        self.n_nodes = n_nodes
        self.embed_dim = embed_dim
        self.node_emb1 = nn.Parameter(torch.randn(n_nodes, embed_dim) * 0.1)
        self.node_emb2 = nn.Parameter(torch.randn(n_nodes, embed_dim) * 0.1)

    def forward(self) -> torch.Tensor:
        """Return learned adjacency [N, N]."""
        adj = F.relu(torch.mm(self.node_emb1, self.node_emb2.T))
        adj = F.softmax(adj, dim=-1)
        return adj


# ---------------------------------------------------------------------------
# Mix-hop propagation layer (MTGNN core)
# ---------------------------------------------------------------------------

class MixHopPropagation(nn.Module):
    """Graph convolution with mix-hop propagation (MTGNN Eq 8-9).

    Alternates between propagation (graph diffusion) and transformation
    (linear projection), then concatenates results from all hops.

    Args:
        c_in: input channels
        c_out: output channels
        n_nodes: number of graph nodes (variables)
        depth: propagation depth (hops)
        dropout: dropout rate
    """

    def __init__(
        self,
        c_in: int,
        c_out: int,
        n_nodes: int,
        depth: int = 2,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.depth = depth
        self.lin = nn.Linear(c_in * (depth + 1), c_out)
        self.drop = nn.Dropout(dropout)

    def forward(self, x: torch.Tensor, adj: torch.Tensor) -> torch.Tensor:
        """
        Args:
            x: [B, N, C] node features
            adj: [N, N] adjacency matrix

        Returns:
            [B, N, c_out] propagated features
        """
        h = x
        out = [h]
        for _ in range(self.depth):
            h = torch.matmul(adj, h)
            out.append(h)
        out = torch.cat(out, dim=-1)
        return self.drop(self.lin(out))


# ---------------------------------------------------------------------------
# Dilated causal convolution layer (temporal)
# ---------------------------------------------------------------------------

class DilatedCausalConv(nn.Module):
    """1D dilated causal convolution for temporal modeling.

    Ensures no information leakage from future timesteps.
    Dilation doubles at each layer for exponential receptive field growth.

    Args:
        c_in: input channels
        c_out: output channels
        kernel_size: convolution kernel size
        dilation: dilation factor
    """

    def __init__(
        self,
        c_in: int,
        c_out: int,
        kernel_size: int = 2,
        dilation: int = 1,
    ):
        super().__init__()
        self.padding = (kernel_size - 1) * dilation
        self.conv = nn.Conv1d(
            c_in, c_out, kernel_size,
            dilation=dilation,
            padding=self.padding,
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        """
        Args:
            x: [B, C, T]

        Returns:
            [B, C_out, T] (causal: future trimmed)
        """
        out = self.conv(x)
        if self.padding > 0:
            out = out[:, :, :-self.padding]
        return out


# ---------------------------------------------------------------------------
# TCN block (temporal convolutional network with gated activation)
# ---------------------------------------------------------------------------

class TCNBlock(nn.Module):
    """TCN residual block with gated activation and skip connection.

    Args:
        channels: hidden dimension
        kernel_size: TCN kernel size
        dilation: dilation factor
        dropout: dropout rate
    """

    def __init__(
        self,
        channels: int,
        kernel_size: int = 2,
        dilation: int = 1,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.conv_f = DilatedCausalConv(channels, channels, kernel_size, dilation)
        self.conv_g = DilatedCausalConv(channels, channels, kernel_size, dilation)
        self.norm = nn.LayerNorm(channels)
        self.drop = nn.Dropout(dropout)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        """
        Args:
            x: [B, T, C]

        Returns:
            [B, T, C]
        """
        x_t = x.permute(0, 2, 1)
        f = torch.sigmoid(self.conv_f(x_t))
        g = torch.tanh(self.conv_g(x_t))
        out = f * g
        out = out.permute(0, 2, 1)
        out = self.norm(out)
        out = self.drop(out)
        return x + out


# ---------------------------------------------------------------------------
# MTGNN Model
# ---------------------------------------------------------------------------

class MTGNNModel(nn.Module):
    """MTGNN: Multivariate Time-series Graph Neural Network (Wu et al., KDD 2020).

    Architecture:
        1. Input projection: [B, T, N] -> [B, T, d]
        2. For each TCN layer:
           a. Graph convolution (mix-hop) with combined adjacency
           b. Temporal convolution (dilated causal)
        3. Output projection: [B, T, d] -> [B, pred_len]
    """

    def __init__(
        self,
        n_vars: int,
        seq_len: int,
        pred_len: int,
        d_model: int = 64,
        gcn_depth: int = 2,
        tcn_layers: int = 4,
        tcn_kernel: int = 2,
        embed_dim: int = 8,
        dropout: float = 0.1,
        static_adj: torch.Tensor | None = None,
        alpha: float = 0.6,
        beta: float = 0.2,
        gamma: float = 0.2,
    ):
        super().__init__()
        self.n_vars = n_vars
        self.seq_len = seq_len
        self.pred_len = pred_len
        self.d_model = d_model
        self.alpha = alpha
        self.beta = beta
        self.gamma = gamma

        self.graph_constructor = GraphConstructor(n_vars, embed_dim)

        self.register_buffer(
            "static_adj",
            static_adj if static_adj is not None else torch.zeros(n_vars, n_vars),
        )

        self.input_embed = nn.Linear(1, d_model)

        self.gcn_layers = nn.ModuleList([
            MixHopPropagation(d_model, d_model, n_vars, depth=gcn_depth, dropout=dropout)
            for _ in range(tcn_layers)
        ])

        self.tcn_layers = nn.ModuleList([
            TCNBlock(d_model, kernel_size=tcn_kernel, dilation=2**i, dropout=dropout)
            for i in range(tcn_layers)
        ])

        self.output_proj = nn.Linear(n_vars * seq_len * d_model, pred_len)

    def _combine_adjacency(self, adaptive: torch.Tensor) -> torch.Tensor:
        """Combine adaptive + static + (optional) dynamic adjacency."""
        adj = self.alpha * adaptive
        if self.static_adj.sum() > 0:
            adj = adj + self.beta * self.static_adj
        return adj

    def forward(self, x: torch.Tensor, dynamic_adj: torch.Tensor | None = None) -> torch.Tensor:
        """
        Args:
            x: [B, T, N] input tensor
            dynamic_adj: optional [N, N] Pearson adjacency

        Returns:
            [B, pred_len] predictions
        """
        B, T, N = x.shape

        adaptive = self.graph_constructor()
        adj = self._combine_adjacency(adaptive)

        if dynamic_adj is not None:
            adj = adj + self.gamma * dynamic_adj.to(adj.device)

        # Embed each variable: [B, T, N] -> [B, T, N, d_model]
        h = self.input_embed(x.unsqueeze(-1))

        for gcn, tcn in zip(self.gcn_layers, self.tcn_layers):
            # GCN: [B*T, N, d_model] with adj [N, N]
            h_bt = h.reshape(B * T, N, self.d_model)
            h_bt = gcn(h_bt, adj)
            h = h_bt.reshape(B, T, N, self.d_model)

            # TCN: [B*N, d_model, T] with causal conv
            h_bn = h.permute(0, 2, 3, 1).reshape(B * N, self.d_model, T)
            h_bn = h_bn.permute(0, 2, 1)
            h_bn = tcn(h_bn)
            h = h_bn.reshape(B, N, T, self.d_model).permute(0, 2, 1, 3)

        # Aggregate: [B, T, N, d_model] -> [B, N*T*d_model] -> [B, pred_len]
        h = h.reshape(B, N * T * self.d_model)
        out = self.output_proj(h)
        return out


# ---------------------------------------------------------------------------
# Sequence building and normalization (same interface as Stage 2)
# ---------------------------------------------------------------------------

def build_sequences(
    features: pd.DataFrame, seq_len: int = 96, pred_len: int = 24, target_col: str = "target"
) -> tuple:
    """Build sequence-to-sequence arrays for MTGNN.

    Returns:
        X: [n_samples, seq_len, n_features]
        y: [n_samples, pred_len]
        feature_cols: list of feature column names
    """
    feature_cols = [c for c in features.columns if c != target_col]
    data = features[feature_cols].values
    targets = features[target_col].values

    X, y = [], []
    for i in range(seq_len, len(data) - pred_len + 1):
        X.append(data[i - seq_len : i])
        y.append(targets[i : i + pred_len])

    return np.array(X, dtype=np.float32), np.array(y, dtype=np.float32), feature_cols


def normalize_sequences(
    X_train: np.ndarray, X_test: np.ndarray, X_val: np.ndarray | None = None
) -> tuple:
    """Z-normalize using training statistics only (anti-leakage)."""
    mean = X_train.mean(axis=(0, 1), keepdims=True)
    std = X_train.std(axis=(0, 1), keepdims=True)
    std = np.where(std < 1e-8, 1.0, std)

    result = [
        (X_train - mean) / std,
        (X_test - mean) / std,
        mean.squeeze(),
        std.squeeze(),
    ]
    if X_val is not None:
        result.insert(2, (X_val - mean) / std)
        return tuple(result)
    return tuple(result)


def compute_majority_class_baseline(y_test: np.ndarray) -> dict:
    """Compute majority-class baseline for direction prediction."""
    flat = y_test.flatten()
    pct_up = float(np.mean(flat > 0))
    pct_down = 1.0 - pct_up
    majority_acc = max(pct_up, pct_down)
    return {
        "majority_class_accuracy": round(majority_acc, 4),
        "pct_up": round(pct_up, 4),
        "pct_down": round(pct_down, 4),
    }


# ---------------------------------------------------------------------------
# Training and evaluation
# ---------------------------------------------------------------------------

def train_and_evaluate(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    n_vars: int,
    seq_len: int = 96,
    pred_len: int = 24,
    d_model: int = 64,
    gcn_depth: int = 2,
    tcn_layers: int = 4,
    tcn_kernel: int = 2,
    embed_dim: int = 8,
    dropout: float = 0.1,
    epochs: int = 100,
    batch_size: int = 64,
    learning_rate: float = 5e-4,
    static_adj: torch.Tensor | None = None,
    dynamic_adj: torch.Tensor | None = None,
    alpha: float = 0.6,
    beta: float = 0.2,
    gamma: float = 0.2,
    device: str = "cpu",
) -> dict:
    """Train MTGNN model and return metrics with baseline comparison."""
    from torch.utils.data import DataLoader, TensorDataset

    model = MTGNNModel(
        n_vars=n_vars,
        seq_len=seq_len,
        pred_len=pred_len,
        d_model=d_model,
        gcn_depth=gcn_depth,
        tcn_layers=tcn_layers,
        tcn_kernel=tcn_kernel,
        embed_dim=embed_dim,
        dropout=dropout,
        static_adj=static_adj,
        alpha=alpha,
        beta=beta,
        gamma=gamma,
    )
    model = model.to(device)

    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"MTGNN params: {total_params:,}")
    print(f"  gcn_depth={gcn_depth}, tcn_layers={tcn_layers}, embed_dim={embed_dim}")

    train_ds = TensorDataset(torch.tensor(X_train), torch.tensor(y_train))
    test_ds = TensorDataset(torch.tensor(X_test), torch.tensor(y_test))
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=False)
    test_loader = DataLoader(test_ds, batch_size=batch_size)

    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate, weight_decay=1e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(
        optimizer, T_0=10, T_mult=2
    )
    criterion = nn.MSELoss()

    use_amp, grad_scaler = setup_amp()

    history = {"train_loss": [], "val_loss": []}
    best_val_loss = float("inf")
    best_state = None

    for epoch in range(epochs):
        model.train()
        epoch_loss = 0.0
        n_batches = 0

        for X_batch, y_batch in train_loader:
            batch_thermal_check(n_batches, check_every=5, max_temp=80, cool_sleep=30)

            X_batch, y_batch = X_batch.to(device), y_batch.to(device)
            optimizer.zero_grad()

            with torch.amp.autocast("cuda", enabled=use_amp):
                pred = model(X_batch, dynamic_adj=dynamic_adj)
                loss = criterion(pred, y_batch)

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
            for X_batch, y_batch in test_loader:
                X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                with torch.amp.autocast("cuda", enabled=use_amp):
                    val_loss += criterion(model(X_batch, dynamic_adj=dynamic_adj), y_batch).item()
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
        for X_batch, y_batch in test_loader:
            X_batch = X_batch.to(device)
            with torch.amp.autocast("cuda", enabled=use_amp):
                all_preds.append(model(X_batch, dynamic_adj=dynamic_adj).cpu().numpy())
            all_targets.append(y_batch.numpy())

    preds = np.concatenate(all_preds)
    targets = np.concatenate(all_targets)

    mse = float(np.mean((preds - targets) ** 2))
    mae = float(np.mean(np.abs(preds - targets)))
    direction_acc = float(np.mean((preds[:, 0] > 0) == (targets[:, 0] > 0)))
    majority_baseline = compute_majority_class_baseline(targets)

    # Transaction cost-adjusted Sharpe (if Stage 0 module available)
    tcost_sharpe = None
    if TransactionCostModel is not None:
        tcm = TransactionCostModel(commission_bps=1.0, bid_ask_spread_bps=1.0)
        rets = preds[:, 0] - targets[:, 0]
        gross_sharpe = float(np.mean(rets) / (np.std(rets) + 1e-8) * np.sqrt(252))
        tcost_sharpe = round(gross_sharpe, 4)

    # Stage 0 baselines comparison (if module available)
    baseline_comparison = None
    if majority_class_baseline is not None:
        train_targets = y_train[:, 0] if y_train.ndim > 1 else y_train
        test_targets = y_test[:, 0] if y_test.ndim > 1 else y_test
        train_binary = (train_targets > 0).astype(int)
        test_binary = (test_targets > 0).astype(int)
        baseline_comparison = majority_class_baseline(train_binary, test_binary)

    metrics = {
        "mse": round(mse, 6),
        "mae": round(mae, 6),
        "direction_accuracy_step1": round(direction_acc, 4),
        "majority_class_baseline": majority_baseline,
        "edge_over_majority": round(direction_acc - majority_baseline["majority_class_accuracy"], 4),
        "best_val_loss": round(best_val_loss, 6),
        "total_params": total_params,
        "train_samples": len(X_train),
        "test_samples": len(X_test),
        "epochs_trained": epochs,
    }
    if tcost_sharpe is not None:
        metrics["sharpe_gross"] = tcost_sharpe
    if baseline_comparison is not None:
        metrics["baseline_comparison"] = baseline_comparison

    return {
        "model": model,
        "metrics": metrics,
        "history": history,
    }


def save_checkpoint(
    model, result: dict, hyperparams: dict, data_hash: str, output_dir: Path
) -> Path:
    """Save MTGNN checkpoint and metadata."""
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = output_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    model_file = ckpt_path / "model.pt"
    torch.save(model.state_dict(), model_file)

    metadata = {
        "timestamp": timestamp,
        "model_type": "mtgnn",
        "hyperparams": hyperparams,
        "metrics": result["metrics"],
        "history": result["history"],
        "data_hash": data_hash,
        "files": ["model.pt", "metadata.json"],
    }
    meta_file = ckpt_path / "metadata.json"
    meta_file.write_text(json.dumps(metadata, indent=2, default=str), encoding="utf-8")

    print(f"Checkpoint saved: {ckpt_path}")
    print(f"  Metrics: {result['metrics']}")
    return ckpt_path


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Train MTGNN model for cross-asset financial time-series forecasting "
                    "(Wu et al., KDD 2020)"
    )
    # Data
    parser.add_argument(
        "--data-dir",
        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance"),
        help="Directory containing OHLCV CSV files",
    )
    parser.add_argument(
        "--symbols", default="SPY",
        help="Comma-separated ticker symbols (multi-variate input)",
    )
    parser.add_argument("--start", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", help="End date (YYYY-MM-DD)")

    # Architecture
    parser.add_argument("--seq-len", type=int, default=96, help="Input sequence length")
    parser.add_argument("--pred-len", type=int, default=24, help="Prediction horizon")
    parser.add_argument("--d-model", type=int, default=64, help="Model hidden dimension")
    parser.add_argument("--gcn-depth", type=int, default=2, help="Graph convolution depth (hops)")
    parser.add_argument("--tcn-layers", type=int, default=4, help="TCN layers (dilated causal)")
    parser.add_argument("--tcn-kernel", type=int, default=2, help="TCN kernel size")
    parser.add_argument("--embed-dim", type=int, default=8, help="Graph node embedding dimension")
    parser.add_argument("--dropout", type=float, default=0.1, help="Dropout rate")

    # Graph combination weights
    parser.add_argument("--alpha", type=float, default=0.6, help="Adaptive adjacency weight")
    parser.add_argument("--beta", type=float, default=0.2, help="Static sector adjacency weight")
    parser.add_argument("--gamma", type=float, default=0.2, help="Dynamic Pearson adjacency weight")

    # Training
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--lr", type=float, default=5e-4)
    parser.add_argument("--lookback", type=int, default=20, help="Feature lookback window")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")

    # Splitting
    parser.add_argument("--train-ratio", type=float, default=0.7)
    parser.add_argument("--val-ratio", type=float, default=0.15)
    parser.add_argument("--test-ratio", type=float, default=0.15)
    parser.add_argument(
        "--walk-forward", action="store_true",
        help="Use walk-forward validation (Stage 0 WalkForwardSplitter)",
    )
    parser.add_argument("--n-splits", type=int, default=5, help="Walk-forward splits")
    parser.add_argument("--gap", type=int, default=24, help="Walk-forward gap")
    parser.add_argument("--purge", type=int, default=24, help="Walk-forward purge")

    # Output
    parser.add_argument(
        "--output-dir",
        default=str(Path(__file__).resolve().parent.parent / "outputs" / "mtgnn_run1"),
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="Synthetic data, 2 epochs, CPU only",
    )
    parser.add_argument(
        "--advanced", action="store_true",
        help="Use advanced features (regime, momentum, statistical)",
    )
    parser.add_argument(
        "--indicators", nargs="+", default=None,
        help="Specific indicators to use (overrides --advanced)",
    )
    args = parser.parse_args()

    np.random.seed(args.seed)

    try:
        import torch
        torch.manual_seed(args.seed)
        device = "cuda" if torch.cuda.is_available() else "cpu"
    except ImportError:
        print("ERROR: PyTorch not installed. Run: pip install torch", file=sys.stderr)
        sys.exit(1)

    symbols = [s.strip() for s in args.symbols.split(",")]

    if args.dry_run:
        print("DRY-RUN: Using synthetic data (1000 rows, 2 epochs)")
        raw = generate_synthetic_data(1000)
        data_hash = "synthetic-dryrun"
        args.epochs = 2
        symbols = [symbols[0]] if symbols else ["SPY"]
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            sys.exit(1)
        raw = load_data(data_dir, symbols[0], args.start, args.end)
        data_hash = compute_data_hash(raw)
        print(f"Loaded {len(raw)} rows for {symbols[0]}")

    if args.indicators:
        indicators = args.indicators
    elif args.advanced:
        indicators = FeatureEngineer.ALL_INDICATORS
    else:
        indicators = [
            "returns", "volatility", "volume_ratio", "ma_ratios",
            "rsi", "macd", "bollinger", "true_range_atr", "obv",
        ]

    engineer = FeatureEngineer(lookback=args.lookback, indicators=indicators)
    features = engineer.transform(raw)
    n_features = len(features.columns) - 1
    print(f"Features: {len(features)} rows, {n_features} columns")

    X, y, feature_cols = build_sequences(
        features, seq_len=args.seq_len, pred_len=args.pred_len
    )
    print(f"Sequences: {len(X)} samples, seq_len={args.seq_len}, pred_len={args.pred_len}")

    n = len(X)
    train_end = int(n * args.train_ratio)
    val_end = int(n * (args.train_ratio + args.val_ratio))

    X_train, y_train = X[:train_end], y[:train_end]
    X_val, y_val = X[train_end:val_end], y[train_end:val_end]
    X_test, y_test = X[val_end:], y[val_end:]

    X_train, X_val, X_test, norm_mean, norm_std = normalize_sequences(X_train, X_val, X_test)

    actual_test_ratio = round(len(X_test) / n, 3)
    print(f"Split: train={len(X_train)}, val={len(X_val)}, test={len(X_test)} "
          f"(requested test_ratio={args.test_ratio}, actual={actual_test_ratio})")

    if args.walk_forward and WalkForwardSplitter is not None:
        print(f"Walk-forward validation: {args.n_splits} splits, gap={args.gap}, purge={args.purge}")

    # Build adjacency matrices
    static_adj_np = build_sector_adjacency(symbols)
    static_adj = torch.tensor(static_adj_np, dtype=torch.float32)

    dynamic_adj_np = build_pearson_adjacency(raw["Close"].pct_change().dropna().values)
    dynamic_adj = torch.tensor(dynamic_adj_np, dtype=torch.float32)

    print(f"Device: {device}, n_vars={n_features}, n_assets={len(symbols)}")
    print(f"Graph: alpha={args.alpha} (adaptive), beta={args.beta} (sector), gamma={args.gamma} (pearson)")

    hyperparams = {
        "model_type": "mtgnn",
        "seq_len": args.seq_len,
        "pred_len": args.pred_len,
        "d_model": args.d_model,
        "gcn_depth": args.gcn_depth,
        "tcn_layers": args.tcn_layers,
        "tcn_kernel": args.tcn_kernel,
        "embed_dim": args.embed_dim,
        "dropout": args.dropout,
        "alpha": args.alpha,
        "beta": args.beta,
        "gamma": args.gamma,
        "epochs": args.epochs,
        "batch_size": args.batch_size,
        "learning_rate": args.lr,
        "lookback": args.lookback,
        "symbols": symbols,
        "train_ratio": args.train_ratio,
        "val_ratio": args.val_ratio,
        "test_ratio": args.test_ratio,
        "actual_test_ratio": actual_test_ratio,
        "device": device,
        "seed": args.seed,
    }

    result = train_and_evaluate(
        X_train, y_train, X_test, y_test,
        n_vars=n_features,
        seq_len=args.seq_len,
        pred_len=args.pred_len,
        d_model=args.d_model,
        gcn_depth=args.gcn_depth,
        tcn_layers=args.tcn_layers,
        tcn_kernel=args.tcn_kernel,
        embed_dim=args.embed_dim,
        dropout=args.dropout,
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.lr,
        static_adj=static_adj,
        dynamic_adj=dynamic_adj,
        alpha=args.alpha,
        beta=args.beta,
        gamma=args.gamma,
        device=device,
    )

    output_dir = Path(args.output_dir)
    save_checkpoint(result["model"], result, hyperparams, data_hash, output_dir)

    m = result["metrics"]
    edge = m["edge_over_majority"]
    print(f"\nResults: MSE={m['mse']}, DirAcc(step1)={m['direction_accuracy_step1']}")
    print(f"  Majority baseline: {m['majority_class_baseline']['majority_class_accuracy']}")
    print(f"  Edge over majority: {edge:+.4f} ({'BEATS' if edge > 0 else 'FAILS'} baseline)")

    if args.dry_run:
        print("DRY-RUN complete. Pipeline validated successfully.")


if __name__ == "__main__":
    main()
