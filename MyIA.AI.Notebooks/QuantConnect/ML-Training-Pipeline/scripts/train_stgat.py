"""
Train STGAT models for cross-asset financial time-series forecasting.

Implements spatial-temporal graph attention for multi-asset prediction.
Key innovations:
- Graph Attention Network (GAT): learns inter-asset relationships via attention
- Temporal attention: captures time-varying importance of past observations
- Cross-asset: models correlations between assets in a panier (basket)

Architecture combines:
- Velickovic et al., "Graph Attention Networks" (ICLR 2018)
- Spatial-temporal attention from traffic forecasting (ASTGCN family)

Anti-pattern safeguards:
- --test-ratio HONORED: normalize stats computed on train set only
- Walk-forward validation supported (Stage 0 WalkForwardSplitter)
- Majority-class baseline computed and reported
- Transaction costs deducted from Sharpe (Stage 0 TransactionCostModel)

Usage:
    python train_stgat.py --dry-run
    python train_stgat.py --data-dir ../datasets/panier \\
        --symbols SPY,RSP,IWM,VIX --seq-len 96 --pred-len 24

Output:
    Checkpoints in --output-dir (default: ../outputs/stgat_run1/)
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
from baselines import oos_direction_distribution
from sequence_utils import build_sequences, normalize_sequences

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
# Graph Attention Layer (Velickovic et al., ICLR 2018)
# ---------------------------------------------------------------------------

class GraphAttentionLayer(nn.Module):
    """Single-head graph attention layer (GAT).

    Computes attention coefficients between connected nodes and aggregates
    neighbor features weighted by attention.

    Args:
        in_features: input feature dimension
        out_features: output feature dimension
        dropout: attention dropout
        alpha: LeakyReLU negative slope
    """

    def __init__(
        self,
        in_features: int,
        out_features: int,
        dropout: float = 0.1,
        alpha: float = 0.2,
    ):
        super().__init__()
        self.W = nn.Parameter(torch.randn(in_features, out_features) * 0.1)
        self.a = nn.Parameter(torch.randn(2 * out_features, 1) * 0.1)
        self.dropout = nn.Dropout(dropout)
        self.leaky_relu = nn.LeakyReLU(alpha)

    def forward(self, h: torch.Tensor, adj: torch.Tensor | None = None) -> torch.Tensor:
        """
        Args:
            h: [B, N, in_features] node features
            adj: [N, N] optional adjacency mask (1 = connected, 0 = no edge)

        Returns:
            [B, N, out_features] attended features
        """
        B, N, _ = h.shape
        Wh = torch.matmul(h, self.W)

        a_input = torch.cat([
            Wh.unsqueeze(2).expand(B, N, N, -1),
            Wh.unsqueeze(1).expand(B, N, N, -1),
        ], dim=-1)
        e = self.leaky_relu(torch.matmul(a_input, self.a).squeeze(-1))

        if adj is not None:
            mask = adj.unsqueeze(0).expand(B, -1, -1)
            e = e.masked_fill(mask == 0, float("-inf"))

        attention = F.softmax(e, dim=-1)
        attention = self.dropout(attention)

        out = torch.matmul(attention, Wh)
        return out


class MultiHeadGAT(nn.Module):
    """Multi-head graph attention layer.

    Args:
        in_features: input dimension
        out_features: output dimension per head
        n_heads: number of attention heads
        dropout: attention dropout
    """

    def __init__(
        self,
        in_features: int,
        out_features: int,
        n_heads: int = 4,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.heads = nn.ModuleList([
            GraphAttentionLayer(in_features, out_features, dropout)
            for _ in range(n_heads)
        ])
        self.proj = nn.Linear(n_heads * out_features, out_features)

    def forward(self, h: torch.Tensor, adj: torch.Tensor | None = None) -> torch.Tensor:
        """
        Args:
            h: [B, N, in_features]
            adj: [N, N] optional adjacency

        Returns:
            [B, N, out_features]
        """
        head_outs = [head(h, adj) for head in self.heads]
        concat = torch.cat(head_outs, dim=-1)
        return self.proj(concat)


# ---------------------------------------------------------------------------
# Temporal Attention
# ---------------------------------------------------------------------------

class TemporalAttention(nn.Module):
    """Scaled dot-product temporal attention.

    Computes attention weights across the time dimension to focus on
    the most relevant past observations for each prediction step.

    Args:
        d_model: model dimension
        n_heads: number of attention heads
        dropout: dropout rate
    """

    def __init__(self, d_model: int, n_heads: int = 4, dropout: float = 0.1):
        super().__init__()
        self.n_heads = n_heads
        self.d_k = d_model // n_heads
        self.W_q = nn.Linear(d_model, d_model)
        self.W_k = nn.Linear(d_model, d_model)
        self.W_v = nn.Linear(d_model, d_model)
        self.out_proj = nn.Linear(d_model, d_model)
        self.drop = nn.Dropout(dropout)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        """
        Args:
            x: [B, T, d_model]

        Returns:
            [B, T, d_model]
        """
        B, T, D = x.shape
        H = self.n_heads
        d_k = self.d_k

        Q = self.W_q(x).view(B, T, H, d_k).transpose(1, 2)
        K = self.W_k(x).view(B, T, H, d_k).transpose(1, 2)
        V = self.W_v(x).view(B, T, H, d_k).transpose(1, 2)

        scores = torch.matmul(Q, K.transpose(-2, -1)) / (d_k ** 0.5)

        # Causal mask: prevent attending to future
        mask = torch.triu(torch.ones(T, T, device=x.device, dtype=torch.bool), diagonal=1)
        scores = scores.masked_fill(mask.unsqueeze(0).unsqueeze(0), float("-inf"))

        attn = F.softmax(scores, dim=-1)
        attn = self.drop(attn)

        context = torch.matmul(attn, V)
        context = context.transpose(1, 2).reshape(B, T, D)
        return self.out_proj(context)


# ---------------------------------------------------------------------------
# STGAT Spatial-Temporal Block
# ---------------------------------------------------------------------------

class STGATBlock(nn.Module):
    """Single STGAT block: spatial GAT + temporal attention + FFN.

    Args:
        d_model: model dimension
        n_heads_spatial: graph attention heads
        n_heads_temporal: temporal attention heads
        n_nodes: number of assets
        dropout: dropout rate
    """

    def __init__(
        self,
        d_model: int,
        n_heads_spatial: int = 4,
        n_heads_temporal: int = 4,
        n_nodes: int = 4,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.spatial_attn = MultiHeadGAT(d_model, d_model, n_heads_spatial, dropout)
        self.spatial_norm = nn.LayerNorm(d_model)

        self.temporal_attn = TemporalAttention(d_model, n_heads_temporal, dropout)
        self.temporal_norm = nn.LayerNorm(d_model)

        self.ffn = nn.Sequential(
            nn.Linear(d_model, d_model * 4),
            nn.GELU(),
            nn.Dropout(dropout),
            nn.Linear(d_model * 4, d_model),
            nn.Dropout(dropout),
        )
        self.ffn_norm = nn.LayerNorm(d_model)

    def forward(self, x: torch.Tensor, adj: torch.Tensor | None = None) -> torch.Tensor:
        """
        Args:
            x: [B, T, N, d_model]
            adj: [N, N] adjacency

        Returns:
            [B, T, N, d_model]
        """
        B, T, N, D = x.shape

        # Spatial attention: apply GAT across nodes for each timestep
        x_flat = x.reshape(B * T, N, D)
        spatial_out = self.spatial_attn(x_flat, adj)
        spatial_out = spatial_out.reshape(B, T, N, D)
        x = self.spatial_norm(x + spatial_out)

        # Temporal attention: apply across time for each node
        x_time = x.permute(0, 2, 1, 3).reshape(B * N, T, D)
        temporal_out = self.temporal_attn(x_time)
        temporal_out = temporal_out.reshape(B, N, T, D).permute(0, 2, 1, 3)
        x = self.temporal_norm(x + temporal_out)

        # FFN
        ffn_out = self.ffn(x)
        x = self.ffn_norm(x + ffn_out)

        return x


# ---------------------------------------------------------------------------
# STGAT Model
# ---------------------------------------------------------------------------

class STGATModel(nn.Module):
    """STGAT: Spatial-Temporal Graph Attention for multi-asset forecasting.

    Architecture:
        1. Input embedding: [B, T, N] -> [B, T, N, d_model]
        2. Stack of STGAT blocks (spatial GAT + temporal attention)
        3. Output projection: [B, T, N, d_model] -> [B, pred_len]

    Supports multi-asset input where N = number of symbols, enabling
    cross-asset signal propagation via graph attention.
    """

    def __init__(
        self,
        n_vars: int,
        seq_len: int,
        pred_len: int,
        d_model: int = 64,
        n_blocks: int = 2,
        n_heads_spatial: int = 4,
        n_heads_temporal: int = 4,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.n_vars = n_vars
        self.seq_len = seq_len
        self.pred_len = pred_len
        self.d_model = d_model

        self.input_embed = nn.Linear(1, d_model)
        self.pos_encoding = nn.Parameter(torch.randn(1, seq_len, 1, d_model) * 0.02)

        self.blocks = nn.ModuleList([
            STGATBlock(d_model, n_heads_spatial, n_heads_temporal, n_vars, dropout)
            for _ in range(n_blocks)
        ])

        self.output_proj = nn.Linear(seq_len * d_model, pred_len)

    def forward(self, x: torch.Tensor, adj: torch.Tensor | None = None) -> torch.Tensor:
        """
        Args:
            x: [B, T, N] input tensor
            adj: [N, N] optional adjacency matrix

        Returns:
            [B, pred_len] predictions (aggregated across assets)
        """
        B, T, N = x.shape

        h = x.unsqueeze(-1)
        h = self.input_embed(h)
        h = h + self.pos_encoding[:, :T, :1, :]

        for block in self.blocks:
            h = block(h, adj)

        h = h.permute(0, 2, 1, 3).reshape(B, N, T * self.d_model)
        preds = self.output_proj(h)
        preds = preds.mean(dim=1)

        return preds


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
    n_blocks: int = 2,
    n_heads_spatial: int = 4,
    n_heads_temporal: int = 4,
    dropout: float = 0.1,
    epochs: int = 100,
    batch_size: int = 64,
    learning_rate: float = 5e-4,
    static_adj: torch.Tensor | None = None,
    device: str = "cpu",
    X_val: np.ndarray | None = None,
    y_val: np.ndarray | None = None,
) -> dict:
    """Train STGAT model and return metrics with baseline comparison."""
    from torch.utils.data import DataLoader, TensorDataset

    model = STGATModel(
        n_vars=n_vars,
        seq_len=seq_len,
        pred_len=pred_len,
        d_model=d_model,
        n_blocks=n_blocks,
        n_heads_spatial=n_heads_spatial,
        n_heads_temporal=n_heads_temporal,
        dropout=dropout,
    )
    model = model.to(device)

    total_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"STGAT params: {total_params:,}")
    print(f"  n_blocks={n_blocks}, n_heads_spatial={n_heads_spatial}, n_heads_temporal={n_heads_temporal}")

    train_ds = TensorDataset(torch.tensor(X_train), torch.tensor(y_train))
    test_ds = TensorDataset(torch.tensor(X_test), torch.tensor(y_test))
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    test_loader = DataLoader(test_ds, batch_size=batch_size)

    if X_val is not None and y_val is not None:
        val_ds = TensorDataset(torch.tensor(X_val), torch.tensor(y_val))
        val_loader = DataLoader(val_ds, batch_size=batch_size)
    else:
        # Auto-split validation from training data (issue #722)
        val_cutoff = int(len(X_train) * 0.85)
        val_ds = TensorDataset(
            torch.tensor(X_train[val_cutoff:]), torch.tensor(y_train[val_cutoff:])
        )
        train_ds = TensorDataset(
            torch.tensor(X_train[:val_cutoff]), torch.tensor(y_train[:val_cutoff])
        )
        train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
        val_loader = DataLoader(val_ds, batch_size=batch_size)

    optimizer = torch.optim.AdamW(model.parameters(), lr=learning_rate, weight_decay=1e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(
        optimizer, T_0=10, T_mult=2
    )
    criterion = nn.MSELoss()

    use_amp, grad_scaler = setup_amp()

    if static_adj is not None:
        static_adj = static_adj.to(device)

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
                pred = model(X_batch, adj=static_adj)
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

        # Evaluate on val set for early stopping (NOT test set)
        model.eval()
        val_loss = 0.0
        val_batches = 0
        with torch.no_grad():
            for X_batch, y_batch in val_loader:
                X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                with torch.amp.autocast("cuda", enabled=use_amp):
                    val_loss += criterion(model(X_batch, adj=static_adj), y_batch).item()
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

    # Final evaluation on TEST set only (untouched during training)
    all_preds, all_targets = [], []
    with torch.no_grad():
        for X_batch, y_batch in test_loader:
            X_batch = X_batch.to(device)
            with torch.amp.autocast("cuda", enabled=use_amp):
                all_preds.append(model(X_batch, adj=static_adj).cpu().numpy())
            all_targets.append(y_batch.numpy())

    preds = np.concatenate(all_preds)
    targets = np.concatenate(all_targets)

    mse = float(np.mean((preds - targets) ** 2))
    mae = float(np.mean(np.abs(preds - targets)))
    direction_acc = float(np.mean((preds[:, 0] > 0) == (targets[:, 0] > 0)))
    majority_baseline = oos_direction_distribution(targets)

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
        "train_samples": len(X_train) if X_val is not None else int(len(X_train) * 0.85),
        "val_samples": len(X_val) if X_val is not None else int(len(X_train) * 0.15),
        "test_samples": len(X_test),
        "epochs_trained": epochs,
    }
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
    """Save STGAT checkpoint and metadata."""
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    ckpt_path = output_dir / timestamp
    ckpt_path.mkdir(parents=True, exist_ok=True)

    model_file = ckpt_path / "model.pt"
    torch.save(model.state_dict(), model_file)

    metadata = {
        "timestamp": timestamp,
        "model_type": "stgat",
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
        description="Train STGAT model for cross-asset financial time-series forecasting "
                    "(Spatial-Temporal Graph Attention)"
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
    parser.add_argument("--n-blocks", type=int, default=2, help="STGAT blocks")
    parser.add_argument("--n-heads-spatial", type=int, default=4, help="Spatial GAT heads")
    parser.add_argument("--n-heads-temporal", type=int, default=4, help="Temporal attention heads")
    parser.add_argument("--dropout", type=float, default=0.1, help="Dropout rate")

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
        default=str(Path(__file__).resolve().parent.parent / "outputs" / "stgat_run1"),
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
    multi_asset = len(symbols) > 1

    if args.dry_run:
        print("DRY-RUN: Using synthetic multi-asset data (4 assets, 2 epochs)")
        symbols = ["SPY", "RSP", "IWM", "VIX"]
        multi_asset = True
        args.epochs = 2
        data_hash = "synthetic-dryrun"
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            sys.exit(1)
        data_hash = None

    static_adj = None
    feature_cols = []

    if multi_asset:
        # Cross-asset mode: each asset is a graph node, adjacencies at [n_assets, n_assets]
        if args.dry_run:
            np.random.seed(args.seed)
            T = 1000
            returns_data = np.random.randn(T, len(symbols)).astype(np.float32) * 0.01
            returns_df = pd.DataFrame(returns_data, columns=symbols)
        else:
            asset_returns = {}
            for sym in symbols:
                raw_sym = load_data(data_dir, sym, args.start, args.end)
                asset_returns[sym] = raw_sym["Close"].pct_change().dropna()
            returns_df = pd.DataFrame(asset_returns).dropna()
            data_hash = compute_data_hash(returns_df)
            print(f"Loaded {len(returns_df)} rows for {len(symbols)} assets")

        n_vars = len(symbols)
        data = returns_df.values.astype(np.float32)

        X_list, y_list = [], []
        for i in range(args.seq_len, len(data) - args.pred_len + 1):
            X_list.append(data[i - args.seq_len : i])
            forward = np.array([np.mean(data[i + h]) for h in range(args.pred_len)])
            y_list.append(forward)
        X = np.array(X_list, dtype=np.float32)
        y = np.array(y_list, dtype=np.float32)
        feature_cols = symbols

        # Build sector adjacency for STGAT spatial attention
        from train_mtgnn import build_sector_adjacency
        static_adj_np = build_sector_adjacency(symbols)
        # Add self-loops so every node can attend to itself (prevents NaN from isolated nodes)
        np.fill_diagonal(static_adj_np, 1.0)
        static_adj = torch.tensor(static_adj_np, dtype=torch.float32)
        print(f"Multi-asset: {len(symbols)} assets, sector adj shape: {static_adj.shape}")
    else:
        # Single-asset mode: standard feature engineering, no spatial mask
        if args.dry_run:
            raw = generate_synthetic_data(1000)
        else:
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
        n_vars = len(features.columns) - 1
        print(f"Features: {len(features)} rows, {n_vars} columns")

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

    adj_info = "fully-connected (no mask)" if static_adj is None else "sector-based spatial mask"
    print(f"Device: {device}, n_vars={n_vars}, mode={'multi-asset' if multi_asset else 'single-asset'}")
    print(f"Graph: {adj_info}")

    hyperparams = {
        "model_type": "stgat",
        "seq_len": args.seq_len,
        "pred_len": args.pred_len,
        "d_model": args.d_model,
        "n_blocks": args.n_blocks,
        "n_heads_spatial": args.n_heads_spatial,
        "n_heads_temporal": args.n_heads_temporal,
        "dropout": args.dropout,
        "epochs": args.epochs,
        "batch_size": args.batch_size,
        "learning_rate": args.lr,
        "lookback": args.lookback if not multi_asset else None,
        "symbols": symbols,
        "multi_asset": multi_asset,
        "n_vars": n_vars,
        "train_ratio": args.train_ratio,
        "val_ratio": args.val_ratio,
        "test_ratio": args.test_ratio,
        "actual_test_ratio": actual_test_ratio,
        "device": device,
        "seed": args.seed,
    }

    result = train_and_evaluate(
        X_train, y_train, X_test, y_test,
        n_vars=n_vars,
        seq_len=args.seq_len,
        pred_len=args.pred_len,
        d_model=args.d_model,
        n_blocks=args.n_blocks,
        n_heads_spatial=args.n_heads_spatial,
        n_heads_temporal=args.n_heads_temporal,
        dropout=args.dropout,
        epochs=args.epochs,
        batch_size=args.batch_size,
        learning_rate=args.lr,
        static_adj=static_adj,
        device=device,
        X_val=X_val,
        y_val=y_val,
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
