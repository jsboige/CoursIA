"""
Volatility forecasting via GARCH+DL hybrid (Epic NN #754 pivot).

Pipeline:
    1. GARCH(1,1) baseline on log-returns → conditional variance σ²_t
    2. DL correction on GARCH residuals → δ_t
    3. Hybrid prediction: vol_t = σ²_t + δ_t

DL models: LSTM (baseline), Transformer (attention), TFT (temporal fusion).
  - LSTM: best for h=1d short-range patterns
  - Transformer: multi-head attention for h=5d/h=20d longer-range dependencies
  - TFT: variable selection + gated residual for multi-horizon

Target: MSE -15% vs GARCH-only on OOS walk-forward 5-folds.
Assets: SPY, BTC-USD, GLD (bonus: EFA, EEM).
Horizons: 1d, 5d, 20d realized volatility.

Multi-seed mandatory (>=4 seeds, edge >= 2*std for BEATS claims).

Usage:
    python train_volatility_garch_dl.py --asset SPY --horizon 5
    python train_volatility_garch_dl.py --asset SPY --horizon 5 --model transformer
    python train_volatility_garch_dl.py --asset SPY --horizon 5 --seeds 0 1 7 42 123
    python train_volatility_garch_dl.py --all-assets --all-horizons --model lstm
    python train_volatility_garch_dl.py --all-assets --all-horizons --model transformer

References:
    - Hansen & Lunde (2005): "A forecast comparison of volatility models"
    - Hands-On AI Trading with Python, Pik et al., Wiley 2025
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd

# Local imports
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from data_sources import fetch_data
from walk_forward import WalkForwardSplitter

RESULTS_DIR = SCRIPT_DIR.parent / "results" / "volatility_garch_dl"
RESULTS_DIR.mkdir(parents=True, exist_ok=True)

EQUITY_ASSETS = ["SPY", "BTC-USD", "GLD", "EFA", "EEM"]
CRYPTO_PANIER = ["BTC-USD", "ETH-USD", "SOL-USD", "ADA-USD", "AVAX-USD"]
HORIZONS = [1, 5, 20]
DEFAULT_SEEDS = [0, 1, 7, 42, 123]
DATA_START = "2010-01-01"
MODEL_TYPES = ["lstm", "transformer", "tft"]


# ---------------------------------------------------------------------------
# Data loading
# ---------------------------------------------------------------------------

def load_returns(symbol: str, start: str = DATA_START) -> pd.Series:
    """Load log-returns for a symbol via data_sources."""
    df = fetch_data(symbol, start=start)
    if df is None or df.empty:
        raise ValueError(f"No data fetched for {symbol}")
    close = df["Close"].sort_index()
    close = close[~close.index.duplicated(keep="first")]
    log_ret = np.log(close / close.shift(1)).dropna()
    log_ret.name = symbol
    return log_ret


def compute_realized_vol(returns: pd.Series, horizon: int) -> pd.Series:
    """Realized volatility: rolling sum of squared returns over horizon.

    rv_t = sum(r_{t-h+1:t}²)  (realized variance)
    Target for prediction = log(rv_{t+horizon}) to stabilize variance.
    """
    rv = returns.pow(2).rolling(horizon).sum().shift(-horizon)
    log_rv = np.log(rv.clip(lower=1e-12))
    log_rv.name = f"log_rv_{horizon}d"
    return log_rv


# ---------------------------------------------------------------------------
# GARCH(1,1) baseline
# ---------------------------------------------------------------------------

def fit_garch(returns: pd.Series, horizon: int = 1) -> pd.Series:
    """Fit GARCH(1,1) and return h-step ahead conditional variance forecast.

    Uses the `arch` library. Returns a Series aligned with returns index,
    containing the variance forecast for horizon steps ahead.
    """
    from arch import arch_model

    # Scale returns to percentage for numerical stability
    scaled = returns * 100
    am = arch_model(scaled.dropna(), vol="Garch", p=1, q=1, dist="normal", rescale=False)
    res = am.fit(disp="off", show_warning=False)

    # Get 1-step ahead conditional variance forecasts (rolling)
    cond_var = res.conditional_volatility ** 2

    # For h-step ahead, scale by h (assumes variance persistence)
    # σ²_{t+h} ≈ σ²_t * h for short horizons under GARCH(1,1)
    if horizon > 1:
        cond_var = cond_var * horizon

    # Rescale back
    cond_var = cond_var / 10000
    cond_var.index = returns.index[:len(cond_var)]
    return cond_var


def compute_garch_residuals(returns: pd.Series, cond_var: pd.Series, horizon: int) -> pd.Series:
    """Compute standardized residuals from GARCH fit."""
    aligned = pd.DataFrame({"ret": returns, "var": cond_var}).dropna()
    residuals = aligned["ret"].pow(2) - aligned["var"]
    return residuals


# ---------------------------------------------------------------------------
# Feature engineering for DL correction
# ---------------------------------------------------------------------------

def build_dl_features(returns: pd.Series, cond_var: pd.Series, lookback: int = 60) -> pd.DataFrame:
    """Build feature matrix for DL correction model.

    Features: past returns, past conditional variance, realized vol windows,
    return squaured (innovation magnitude), volatility of variance.
    """
    df = pd.DataFrame({"ret": returns, "garch_var": cond_var}).dropna()

    # Realized vol at multiple windows
    for w in [5, 10, 20, 60]:
        df[f"rv_{w}"] = df["ret"].pow(2).rolling(w).sum()

    # Innovation magnitude
    df["ret_sq"] = df["ret"] ** 2

    # Volatility of variance (vol-of-vol)
    df["vol_of_vol"] = df["garch_var"].rolling(20).std()

    # GARCH residual
    df["garch_resid"] = df["ret_sq"] - df["garch_var"]

    # Lagged features
    for lag in [1, 2, 3, 5]:
        df[f"resid_lag_{lag}"] = df["garch_resid"].shift(lag)
        df[f"var_lag_{lag}"] = df["garch_var"].shift(lag)

    return df.dropna()


def build_sequences_dl(
    features: pd.DataFrame,
    target: pd.Series,
    lookback: int = 60,
) -> tuple[np.ndarray, np.ndarray]:
    """Build sliding window sequences for DL model.

    Returns
    -------
    X : ndarray (n_samples, lookback, n_features)
    y : ndarray (n_samples,) — log realized volatility target
    """
    aligned = pd.DataFrame(features).copy()
    aligned["target"] = target
    aligned = aligned.dropna()

    feature_cols = [c for c in aligned.columns if c != "target"]
    data = aligned[feature_cols].values
    targets = aligned["target"].values

    X, y = [], []
    for i in range(lookback, len(data)):
        X.append(data[i - lookback : i])
        y.append(targets[i])

    return np.array(X, dtype=np.float32), np.array(y, dtype=np.float32)


# ---------------------------------------------------------------------------
# LSTM correction model
# ---------------------------------------------------------------------------

def create_lstm_model(
    input_dim: int,
    hidden_dim: int = 64,
    num_layers: int = 2,
    dropout: float = 0.2,
    lr: float = 1e-3,
) -> "torch.nn.Module":
    """Create LSTM model for volatility correction."""
    import torch
    import torch.nn as nn

    class VolatilityLSTM(nn.Module):
        def __init__(self, input_dim, hidden_dim, num_layers, dropout):
            super().__init__()
            self.lstm = nn.LSTM(
                input_dim, hidden_dim, num_layers,
                batch_first=True, dropout=dropout if num_layers > 1 else 0,
            )
            self.fc = nn.Sequential(
                nn.Linear(hidden_dim, 32),
                nn.ReLU(),
                nn.Dropout(dropout),
                nn.Linear(32, 1),
            )

        def forward(self, x):
            lstm_out, _ = self.lstm(x)
            last_hidden = lstm_out[:, -1, :]
            return self.fc(last_hidden).squeeze(-1)

    model = VolatilityLSTM(input_dim, hidden_dim, num_layers, dropout)
    return model


# ---------------------------------------------------------------------------
# Transformer correction model (multi-head self-attention)
# ---------------------------------------------------------------------------

def create_transformer_model(
    input_dim: int,
    hidden_dim: int = 64,
    n_heads: int = 4,
    n_layers: int = 2,
    dropout: float = 0.2,
    lr: float = 1e-3,
) -> "torch.nn.Module":
    """Create Transformer model for volatility correction."""
    import torch
    import torch.nn as nn
    import math

    class PositionalEncoding(nn.Module):
        def __init__(self, d_model: int, max_len: int = 500):
            super().__init__()
            pe = torch.zeros(max_len, d_model)
            position = torch.arange(0, max_len, dtype=torch.float).unsqueeze(1)
            div_term = torch.exp(torch.arange(0, d_model, 2).float() * (-math.log(10000.0) / d_model))
            pe[:, 0::2] = torch.sin(position * div_term)
            pe[:, 1::2] = torch.cos(position * div_term)
            self.register_buffer("pe", pe.unsqueeze(0))

        def forward(self, x):
            return x + self.pe[:, :x.size(1)]

    class VolatilityTransformer(nn.Module):
        def __init__(self, input_dim, hidden_dim, n_heads, n_layers, dropout):
            super().__init__()
            self.input_proj = nn.Linear(input_dim, hidden_dim)
            self.pos_enc = PositionalEncoding(hidden_dim)
            encoder_layer = nn.TransformerEncoderLayer(
                d_model=hidden_dim, nhead=n_heads,
                dim_feedforward=hidden_dim * 4, dropout=dropout,
                batch_first=True,
            )
            self.encoder = nn.TransformerEncoder(encoder_layer, num_layers=n_layers)
            self.fc = nn.Sequential(
                nn.Linear(hidden_dim, 32),
                nn.ReLU(),
                nn.Dropout(dropout),
                nn.Linear(32, 1),
            )

        def forward(self, x):
            x = self.input_proj(x)
            x = self.pos_enc(x)
            x = self.encoder(x)
            return self.fc(x[:, -1, :]).squeeze(-1)

    model = VolatilityTransformer(input_dim, hidden_dim, n_heads, n_layers, dropout)
    return model


# ---------------------------------------------------------------------------
# TFT (Temporal Fusion Transformer) lite correction model
# ---------------------------------------------------------------------------

def create_tft_model(
    input_dim: int,
    hidden_dim: int = 64,
    n_heads: int = 4,
    dropout: float = 0.2,
    lr: float = 1e-3,
) -> "torch.nn.Module":
    """Create lite TFT model with variable selection and gated residual network."""
    import torch
    import torch.nn as nn

    class GatedResidualNetwork(nn.Module):
        def __init__(self, input_size: int, hidden_size: int, output_size: int, dropout: float):
            super().__init__()
            self.fc1 = nn.Linear(input_size, hidden_size)
            self.fc2 = nn.Linear(hidden_size, output_size)
            self.gate = nn.Linear(output_size, output_size)
            self.layer_norm = nn.LayerNorm(output_size)
            self.dropout = nn.Dropout(dropout)
            self.skip = nn.Linear(input_size, output_size) if input_size != output_size else nn.Identity()

        def forward(self, x):
            residual = self.skip(x)
            h = self.dropout(torch.relu(self.fc1(x)))
            h = self.fc2(h)
            g = torch.sigmoid(self.gate(h))
            return self.layer_norm(residual + g * h)

    class VariableSelectionNetwork(nn.Module):
        def __init__(self, input_size: int, hidden_size: int, dropout: float):
            super().__init__()
            self.grn = GatedResidualNetwork(input_size, hidden_size, input_size, dropout)
            self.softmax = nn.Softmax(dim=-1)

        def forward(self, x):
            weights = self.softmax(self.grn(x))
            return x * weights

    class TFTLite(nn.Module):
        def __init__(self, input_dim, hidden_dim, n_heads, dropout):
            super().__init__()
            self.vsn = VariableSelectionNetwork(input_dim, hidden_dim, dropout)
            self.input_proj = nn.Linear(input_dim, hidden_dim)
            encoder_layer = nn.TransformerEncoderLayer(
                d_model=hidden_dim, nhead=n_heads,
                dim_feedforward=hidden_dim * 2, dropout=dropout,
                batch_first=True,
            )
            self.encoder = nn.TransformerEncoder(encoder_layer, num_layers=1)
            self.grn_out = GatedResidualNetwork(hidden_dim, hidden_dim, 32, dropout)
            self.fc_out = nn.Linear(32, 1)

        def forward(self, x):
            # Variable selection per timestep
            b, t, f = x.shape
            x_selected = self.vsn(x.reshape(-1, f)).reshape(b, t, f)
            x_proj = self.input_proj(x_selected)
            x_enc = self.encoder(x_proj)
            context = x_enc[:, -1, :]
            h = self.grn_out(context)
            return self.fc_out(h).squeeze(-1)

    model = TFTLite(input_dim, hidden_dim, n_heads, dropout)
    return model


def create_model(model_type: str, input_dim: int, **kwargs):
    """Factory to create DL model by type."""
    # Extract common params, map to model-specific names
    hidden_dim = kwargs.get("hidden_dim", 64)
    dropout = kwargs.get("dropout", 0.2)
    lr = kwargs.get("lr", 1e-3)
    num_layers = kwargs.get("num_layers", 2)

    if model_type == "lstm":
        return create_lstm_model(input_dim, hidden_dim=hidden_dim, num_layers=num_layers, dropout=dropout, lr=lr)
    elif model_type == "transformer":
        return create_transformer_model(input_dim, hidden_dim=hidden_dim, n_layers=num_layers, dropout=dropout, lr=lr)
    elif model_type == "tft":
        return create_tft_model(input_dim, hidden_dim=hidden_dim, dropout=dropout, lr=lr)
    else:
        raise ValueError(f"Unknown model type: {model_type}. Use {MODEL_TYPES}")


def train_model(
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_val: np.ndarray,
    y_val: np.ndarray,
    seed: int,
    model_type: str = "lstm",
    hidden_dim: int = 64,
    num_layers: int = 2,
    dropout: float = 0.2,
    lr: float = 1e-3,
    epochs: int = 100,
    batch_size: int = 64,
    patience: int = 15,
    device: str = "cpu",
) -> tuple:
    """Train DL model with early stopping. Returns (model, train_losses, val_losses)."""
    import torch
    import torch.nn as nn
    from torch.utils.data import DataLoader, TensorDataset

    torch.manual_seed(seed)
    np.random.seed(seed)

    input_dim = X_train.shape[2]
    model = create_model(
        model_type, input_dim,
        hidden_dim=hidden_dim, num_layers=num_layers,
        dropout=dropout, lr=lr,
    )
    model = model.to(device)

    criterion = nn.MSELoss()
    optimizer = torch.optim.Adam(model.parameters(), lr=lr, weight_decay=1e-5)
    scheduler = torch.optim.lr_scheduler.ReduceLROnPlateau(optimizer, patience=5, factor=0.5)

    train_ds = TensorDataset(
        torch.tensor(X_train, dtype=torch.float32),
        torch.tensor(y_train, dtype=torch.float32),
    )
    val_ds = TensorDataset(
        torch.tensor(X_val, dtype=torch.float32),
        torch.tensor(y_val, dtype=torch.float32),
    )
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    val_loader = DataLoader(val_ds, batch_size=batch_size)

    best_val_loss = float("inf")
    best_state = None
    patience_counter = 0
    train_losses, val_losses = [], []

    for epoch in range(epochs):
        model.train()
        epoch_loss = 0
        for X_batch, y_batch in train_loader:
            X_batch, y_batch = X_batch.to(device), y_batch.to(device)
            optimizer.zero_grad()
            pred = model(X_batch)
            loss = criterion(pred, y_batch)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            epoch_loss += loss.item() * len(X_batch)
        train_losses.append(epoch_loss / len(train_ds))

        model.eval()
        val_loss = 0
        with torch.no_grad():
            for X_batch, y_batch in val_loader:
                X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                pred = model(X_batch)
                val_loss += criterion(pred, y_batch).item() * len(X_batch)
        val_losses.append(val_loss / len(val_ds))

        scheduler.step(val_losses[-1])

        if val_losses[-1] < best_val_loss:
            best_val_loss = val_losses[-1]
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}
            patience_counter = 0
        else:
            patience_counter += 1

        if patience_counter >= patience:
            break

    model.load_state_dict(best_state)
    return model, train_losses, val_losses


# ---------------------------------------------------------------------------
# Evaluation metrics
# ---------------------------------------------------------------------------

def compute_metrics(y_true: np.ndarray, y_pred: np.ndarray) -> dict:
    """Compute volatility forecasting metrics."""
    mse = np.mean((y_true - y_pred) ** 2)
    mae = np.mean(np.abs(y_true - y_pred))
    # QLIKE: asymmetric loss penalizing under-prediction of variance
    # QLIKE = mean(y_true/y_pred - log(y_true/y_pred) - 1)
    eps = 1e-8
    ratio = y_true / (y_pred + eps)
    qlike = np.mean(ratio - np.log(ratio + eps) - 1)
    # HMSE: heteroskedasticity-adjusted MSE
    hmse = np.mean(((y_true - y_pred) ** 2) / (y_true ** 2 + eps))

    return {
        "mse": float(mse),
        "mae": float(mae),
        "qlike": float(qlike),
        "hmse": float(hmse),
        "n_samples": int(len(y_true)),
    }


# ---------------------------------------------------------------------------
# Walk-forward experiment
# ---------------------------------------------------------------------------

def run_single_experiment(
    symbol: str,
    horizon: int,
    seed: int,
    model_type: str = "lstm",
    n_splits: int = 5,
    lookback: int = 60,
    hidden_dim: int = 64,
    num_layers: int = 2,
    dropout: float = 0.2,
    lr: float = 1e-3,
    epochs: int = 100,
    batch_size: int = 64,
    patience: int = 15,
    device: str = "cpu",
) -> dict:
    """Run single walk-forward experiment for one asset/horizon/seed."""
    import torch

    print(f"  [{symbol} h={horizon}d seed={seed}] Loading data...")
    returns = load_returns(symbol)
    target = compute_realized_vol(returns, horizon).dropna()

    print(f"  [{symbol} h={horizon}d seed={seed}] Fitting GARCH(1,1) baseline...")
    cond_var = fit_garch(returns, horizon)

    # Build DL features
    features = build_dl_features(returns, cond_var, lookback)

    # Align all data
    combined = features.join(target, how="inner").dropna()
    if len(combined) < lookback + 200:
        print(f"  [{symbol} h={horizon}d seed={seed}] Insufficient data ({len(combined)} rows)")
        return None

    target_col = f"log_rv_{horizon}d"
    feature_cols = [c for c in combined.columns if c != target_col]

    # Normalize features
    data = combined[feature_cols].values.astype(np.float32)
    targets = combined[target_col].values.astype(np.float32)

    # Build sequences from FULL dataset first, then split by index
    # This avoids the lookback-eats-test-data problem
    X_all, y_all = [], []
    for i in range(lookback, len(data)):
        X_all.append(data[i - lookback : i])
        y_all.append(targets[i])
    X_all = np.array(X_all, dtype=np.float32)
    y_all = np.array(y_all, dtype=np.float32)

    # GARCH baseline: log(garch_var) at each timestep
    garch_col_idx = feature_cols.index("garch_var")
    garch_baseline_all = np.log(
        np.clip(data[lookback:, garch_col_idx].astype(np.float32), 1e-12, None)
    )

    # Walk-forward splits on the sequence indices
    n_seq = len(X_all)
    splitter = WalkForwardSplitter(n_splits=n_splits, gap=horizon, test_size=252)
    fold_results = []
    all_garch_preds = []
    all_hybrid_preds = []
    all_targets = []

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(np.arange(n_seq))):
        # Carve validation from last 15% of train
        val_size = max(1, int(len(train_idx) * 0.15))
        val_idx = train_idx[-val_size:]
        train_idx_inner = train_idx[:-val_size]

        if len(train_idx_inner) < 100 or len(test_idx) < 30:
            continue

        X_train, y_train = X_all[train_idx_inner], y_all[train_idx_inner]
        X_val, y_val = X_all[val_idx], y_all[val_idx]
        X_test, y_test = X_all[test_idx], y_all[test_idx]

        # Normalize using train stats only (anti-leakage)
        mean = X_train.mean(axis=(0, 1), keepdims=True)
        std = X_train.std(axis=(0, 1), keepdims=True)
        std = np.where(std < 1e-8, 1.0, std)
        X_train_n = (X_train - mean) / std
        X_val_n = (X_val - mean) / std
        X_test_n = (X_test - mean) / std

        # Train DL model to predict log(rv) directly (includes GARCH features)
        print(
            f"  [{symbol} h={horizon}d seed={seed}] "
            f"Fold {fold_idx+1}/{n_splits} "
            f"(train={len(X_train)}, val={len(X_val)}, test={len(X_test)})..."
        )
        model, _, _ = train_model(
            X_train_n, y_train, X_val_n, y_val, seed,
            model_type=model_type,
            hidden_dim=hidden_dim, num_layers=num_layers, dropout=dropout,
            lr=lr, epochs=epochs, batch_size=batch_size, patience=patience, device=device,
        )

        # Predict
        model.eval()
        with torch.no_grad():
            dl_pred = model(
                torch.tensor(X_test_n, dtype=torch.float32).to(device)
            ).cpu().numpy()

        # GARCH baseline for this fold
        garch_only = garch_baseline_all[test_idx]
        actual_targets = y_test

        min_len = min(len(dl_pred), len(garch_only), len(actual_targets))
        if min_len < 10:
            continue

        hybrid_preds = dl_pred[:min_len]
        garch_only = garch_only[:min_len]
        actual_targets = actual_targets[:min_len]

        garch_metrics = compute_metrics(actual_targets, garch_only)
        hybrid_metrics = compute_metrics(actual_targets, hybrid_preds)
        mse_improvement = (
            (garch_metrics["mse"] - hybrid_metrics["mse"])
            / garch_metrics["mse"] * 100
        )

        fold_results.append({
            "fold": fold_idx,
            "garch_mse": garch_metrics["mse"],
            "hybrid_mse": hybrid_metrics["mse"],
            "mse_improvement_pct": mse_improvement,
            "garch_metrics": garch_metrics,
            "hybrid_metrics": hybrid_metrics,
            "n_train": len(X_train),
            "n_test": min_len,
        })

        all_garch_preds.append(garch_only)
        all_hybrid_preds.append(hybrid_preds)
        all_targets.append(actual_targets)

    if not fold_results:
        print(f"  [{symbol} h={horizon}d seed={seed}] No valid folds produced")
        return None

    # Aggregate across folds
    all_targets_cat = np.concatenate(all_targets)
    all_garch_cat = np.concatenate(all_garch_preds)
    all_hybrid_cat = np.concatenate(all_hybrid_preds)

    agg_garch = compute_metrics(all_targets_cat, all_garch_cat)
    agg_hybrid = compute_metrics(all_targets_cat, all_hybrid_cat)
    mse_improvement = (
        (agg_garch["mse"] - agg_hybrid["mse"]) / agg_garch["mse"] * 100
    )

    return {
        "symbol": symbol,
        "horizon": horizon,
        "seed": seed,
        "model_type": model_type,
        "n_folds": len(fold_results),
        "garch_baseline": agg_garch,
        "hybrid": agg_hybrid,
        "mse_improvement_pct": round(mse_improvement, 4),
        "folds": fold_results,
        "timestamp": datetime.now().isoformat(),
    }


def _build_fold_sequences(
    data: np.ndarray, targets: np.ndarray, lookback: int
) -> tuple[np.ndarray, np.ndarray]:
    """Build sequences from a single fold's data slice."""
    if len(data) <= lookback:
        return np.array([]), np.array([])
    X = np.array([data[i - lookback : i] for i in range(lookback, len(data))], dtype=np.float32)
    y = targets[lookback:].astype(np.float32)
    # Align: y should have same length as X
    min_len = min(len(X), len(y))
    return X[:min_len], y[:min_len]


# ---------------------------------------------------------------------------
# Multi-seed orchestration
# ---------------------------------------------------------------------------

def run_multi_seed(
    symbol: str,
    horizon: int,
    seeds: list[int] | None = None,
    model_type: str = "lstm",
    device: str = "cpu",
    **kwargs,
) -> dict:
    """Run experiment across multiple seeds and aggregate results."""
    if seeds is None:
        seeds = DEFAULT_SEEDS

    results = []
    for seed in seeds:
        print(f"\n{'='*60}")
        print(f"Running {symbol} h={horizon}d seed={seed}")
        print(f"{'='*60}")
        r = run_single_experiment(symbol, horizon, seed, model_type=model_type, device=device, **kwargs)
        if r is not None:
            results.append(r)

    if not results:
        return {"symbol": symbol, "horizon": horizon, "status": "FAILED", "seeds": seeds}

    # Aggregate across seeds
    mse_improvements = [r["mse_improvement_pct"] for r in results]
    mean_imp = np.mean(mse_improvements)
    std_imp = np.std(mse_improvements)
    n_beats = sum(1 for m in mse_improvements if m > 0)

    # Edge test: mean - 2*std > 0 → statistically significant improvement
    edge = mean_imp - 2 * std_imp

    summary = {
        "symbol": symbol,
        "horizon": horizon,
        "n_seeds": len(results),
        "seeds": seeds,
        "mean_mse_improvement_pct": round(float(mean_imp), 4),
        "std_mse_improvement_pct": round(float(std_imp), 4),
        "edge_mse_improvement_pct": round(float(edge), 4),
        "n_beats": n_beats,
        "beats_target_15pct": bool(mean_imp >= 15.0),
        "significant": bool(edge > 0),
        "per_seed_results": results,
        "timestamp": datetime.now().isoformat(),
    }

    # Save
    fname = f"vol_{symbol}_h{horizon}d_{model_type}_multiseed.json"
    out_path = RESULTS_DIR / fname
    with open(out_path, "w") as f:
        json.dump(summary, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    return summary


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args():
    parser = argparse.ArgumentParser(description="Volatility forecasting GARCH+DL hybrid")
    parser.add_argument("--asset", type=str, default="SPY", help="Asset symbol")
    parser.add_argument("--horizon", type=int, default=5, help="Prediction horizon (days)")
    parser.add_argument("--seeds", type=int, nargs="+", default=DEFAULT_SEEDS, help="Random seeds")
    parser.add_argument("--model", type=str, default="lstm", choices=MODEL_TYPES, help="DL model type")
    parser.add_argument("--all-assets", action="store_true", help="Run all equity assets")
    parser.add_argument("--crypto-panier", action="store_true",
                        help="Run crypto panier (BTC, ETH, SOL, ADA, AVAX)")
    parser.add_argument("--all-horizons", action="store_true", help="Run all horizons")
    parser.add_argument("--n-splits", type=int, default=5, help="Walk-forward folds")
    parser.add_argument("--lookback", type=int, default=60, help="Sequence lookback")
    parser.add_argument("--hidden-dim", type=int, default=64, help="Hidden dimension")
    parser.add_argument("--epochs", type=int, default=100, help="Max training epochs")
    parser.add_argument("--device", type=str, default="auto", help="Device (auto/cpu/cuda)")
    return parser.parse_args()


def main():
    args = parse_args()

    if args.device == "auto":
        import torch
        device = "cuda" if torch.cuda.is_available() else "cpu"
    else:
        device = args.device

    print(f"Device: {device}")
    print(f"Model: {args.model}")
    print(f"Results dir: {RESULTS_DIR}")

    if args.crypto_panier:
        assets = CRYPTO_PANIER
        print(f"Mode: CRYPTO PANIER ({len(assets)} assets)")
    elif args.all_assets:
        assets = EQUITY_ASSETS
    else:
        assets = [args.asset]
    horizons = HORIZONS if args.all_horizons else [args.horizon]

    all_summaries = []
    for symbol in assets:
        for horizon in horizons:
            print(f"\n{'#'*70}")
            print(f"# {symbol} h={horizon}d {args.model} — {len(args.seeds)} seeds")
            print(f"{'#'*70}")

            summary = run_multi_seed(
                symbol, horizon, seeds=args.seeds, model_type=args.model, device=device,
                n_splits=args.n_splits, lookback=args.lookback,
                hidden_dim=args.hidden_dim, epochs=args.epochs,
            )
            all_summaries.append(summary)

            # Print summary
            imp = summary.get("mean_mse_improvement_pct", 0)
            sig = summary.get("significant", False)
            beats = summary.get("beats_target_15pct", False)
            print(f"\n  Result: MSE improvement = {imp:.2f}% | Significant: {sig} | BEATS 15%: {beats}")

    # Final summary table
    print(f"\n{'='*70}")
    print("FINAL RESULTS")
    print(f"{'='*70}")
    print(f"{'Asset':<10} {'Horizon':<10} {'MSE Imp%':<12} {'Std':<10} {'BEATS':<8} {'Sig':<6}")
    print("-" * 56)
    for s in all_summaries:
        if "mean_mse_improvement_pct" in s:
            print(
                f"{s['symbol']:<10} {s['horizon']}d{'':<7} "
                f"{s['mean_mse_improvement_pct']:>8.2f}%  "
                f"{s.get('std_mse_improvement_pct', 0):>6.2f}%  "
                f"{'YES' if s.get('beats_target_15pct') else 'no':<8} "
                f"{'YES' if s.get('significant') else 'no':<6}"
            )

    # Save combined results
    combined_path = RESULTS_DIR / f"vol_all_results_{args.model}.json"
    with open(combined_path, "w") as f:
        json.dump(all_summaries, f, indent=2, default=str)
    print(f"\nCombined results saved to {combined_path}")


if __name__ == "__main__":
    main()
