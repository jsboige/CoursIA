"""
Mixture-of-Experts with regime-aware routing using DL experts (LSTM/GRU/Transformer).

Each market regime (bull/bear/neutral) gets its own PyTorch DL expert model.
A router classifies the current regime and delegates prediction to the
corresponding expert. This specialization lets each expert learn simpler
patterns than a single model handling all regimes.

Architecture:
    1. Regime detector (price-based or HMM) -> label each timestep
    2. Per-regime DL expert (LSTM/GRU/Transformer) trained on regime-filtered sequences
    3. Router dispatches new samples to the appropriate expert
    4. Walk-forward evaluation with expanding window

Combines:
    - regime_detector.py -> regime labeling
    - features.py -> OHLCV feature engineering
    - sequence_utils.py -> sliding-window sequence building
    - train_lstm.py / train_transformer.py -> model architectures
    - gpu_training -> thermal-safe GPU training with AMP
    - walk_forward.py -> walk-forward splitting

Usage:
    # Dry-run (CPU, synthetic data)
    python train_moe_regimes.py --dry-run

    # LSTM experts with price-based regimes
    python train_moe_regimes.py --data-dir ../datasets/yfinance --symbol SPY \
        --expert lstm --regime-method price --epochs 50

    # Transformer experts with HMM regimes (for RTX 4090)
    python train_moe_regimes.py --data-dir ../datasets/yfinance --symbol SPY \
        --expert transformer --regime-method hmm --epochs 100 \
        --hidden-size 256 --num-layers 4

    # Multi-seed evaluation
    python train_moe_regimes.py --data-dir ../datasets/yfinance --symbol SPY \
        --expert lstm --seeds 0 1 7 42 123 --epochs 50

Issue #754 Phase B: MoE+régimes DL approach.
"""

from __future__ import annotations

import argparse
import json
import logging
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
SHARED_DIR = Path(__file__).resolve().parent.parent.parent / "shared"
# Scripts dir FIRST to avoid shadowing by shared/ package
sys.path.insert(0, str(SCRIPTS_DIR))
if str(SHARED_DIR) not in sys.path:
    sys.path.append(str(SHARED_DIR))

import importlib

def _import_from_scripts(name: str):
    spec = importlib.util.spec_from_file_location(
        name, SCRIPTS_DIR / f"{name}.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

# Scripts-only modules (must come from scripts/, not shared/)
_mod_feat = _import_from_scripts("features")
FeatureEngineer = _mod_feat.FeatureEngineer
_mod_seq = _import_from_scripts("sequence_utils")
build_sequences = _mod_seq.build_sequences
_mod_wf = _import_from_scripts("walk_forward")
WalkForwardSplitter = _mod_wf.WalkForwardSplitter
_mod_du = _import_from_scripts("data_utils")
compute_data_hash = _mod_du.compute_data_hash
generate_synthetic_data = _mod_du.generate_synthetic_data
load_data = _mod_du.load_data

# These exist only in scripts/ — direct import is fine
from regime_detector import detect_regimes
from gpu_training import batch_thermal_check, get_gpu_temp, setup_amp

log = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# DL Expert Model Factory
# ---------------------------------------------------------------------------

def build_expert_model(
    expert_type: str,
    input_size: int,
    hidden_size: int = 128,
    num_layers: int = 2,
    dropout: float = 0.2,
    nhead: int = 4,
    dim_feedforward: int = 512,
    seq_len: int = 20,
) -> "torch.nn.Module":
    """Build a DL expert model for a single regime.

    Supports: lstm, gru, transformer.
    """
    import torch
    import torch.nn as nn

    if expert_type in ("lstm", "gru"):
        rnn_cls = nn.LSTM if expert_type == "lstm" else nn.GRU

        class RNNDirectionExpert(nn.Module):
            def __init__(self):
                super().__init__()
                self.rnn = rnn_cls(
                    input_size=input_size,
                    hidden_size=hidden_size,
                    num_layers=num_layers,
                    batch_first=True,
                    dropout=dropout if num_layers > 1 else 0.0,
                )
                self.head = nn.Sequential(
                    nn.Linear(hidden_size, 32),
                    nn.ReLU(),
                    nn.Dropout(dropout),
                    nn.Linear(32, 1),
                )

            def forward(self, x):
                out, _ = self.rnn(x)
                return self.head(out[:, -1, :])

        return RNNDirectionExpert()

    elif expert_type == "transformer":
        d_model = hidden_size

        class TransformerDirectionExpert(nn.Module):
            def __init__(self):
                super().__init__()
                self.input_proj = nn.Linear(input_size, d_model)
                # Sinusoidal positional encoding
                self.register_buffer(
                    "pe",
                    torch.tensor(_sinusoidal_pe(seq_len, d_model), dtype=torch.float32),
                )
                encoder_layer = nn.TransformerEncoderLayer(
                    d_model=d_model,
                    nhead=nhead,
                    dim_feedforward=dim_feedforward,
                    dropout=dropout,
                    batch_first=True,
                )
                self.encoder = nn.TransformerEncoder(encoder_layer, num_layers=num_layers)
                self.head = nn.Sequential(
                    nn.Linear(d_model, 32),
                    nn.ReLU(),
                    nn.Dropout(dropout),
                    nn.Linear(32, 1),
                )

            def forward(self, x):
                x = self.input_proj(x) + self.pe[:x.size(1)]
                x = self.encoder(x)
                return self.head(x[:, -1, :])

        return TransformerDirectionExpert()

    else:
        raise ValueError(f"Unknown expert type: {expert_type}. Use lstm/gru/transformer.")


def _sinusoidal_pe(seq_len: int, d_model: int) -> np.ndarray:
    pe = np.zeros((seq_len, d_model))
    pos = np.arange(0, seq_len).reshape(-1, 1)
    div = np.exp(np.arange(0, d_model, 2) * -(np.log(10000.0) / d_model))
    pe[:, 0::2] = np.sin(pos * div)
    pe[:, 1::2] = np.cos(pos * div[:d_model // 2])
    return pe.astype(np.float32)


# ---------------------------------------------------------------------------
# Single expert training
# ---------------------------------------------------------------------------

def train_expert(
    model: "torch.nn.Module",
    X_train: np.ndarray,
    y_train: np.ndarray,
    epochs: int = 50,
    batch_size: int = 32,
    lr: float = 1e-3,
    device: str = "cpu",
    val_ratio: float = 0.15,
    verbose: bool = False,
) -> dict:
    """Train a single DL expert model.

    Returns dict with model, train/val loss history.
    """
    import torch
    import torch.nn as nn
    from torch.utils.data import DataLoader, TensorDataset

    val_cut = int(len(X_train) * (1 - val_ratio))
    X_tr, X_val = X_train[:val_cut], X_train[val_cut:]
    y_tr, y_val = y_train[:val_cut], y_train[val_cut:]

    train_ds = TensorDataset(
        torch.tensor(X_tr, dtype=torch.float32),
        torch.tensor(y_tr, dtype=torch.float32).unsqueeze(1),
    )
    val_ds = TensorDataset(
        torch.tensor(X_val, dtype=torch.float32),
        torch.tensor(y_val, dtype=torch.float32).unsqueeze(1),
    )
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    val_loader = DataLoader(val_ds, batch_size=batch_size)

    model = model.to(device)
    optimizer = torch.optim.Adam(model.parameters(), lr=lr, weight_decay=1e-5)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=epochs)
    criterion = nn.MSELoss()

    use_amp, grad_scaler = setup_amp()

    best_val_loss = float("inf")
    best_state = None
    history = {"train_loss": [], "val_loss": []}

    for epoch in range(epochs):
        model.train()
        epoch_loss, n_batch = 0.0, 0
        for X_batch, y_batch in train_loader:
            batch_thermal_check(n_batch, check_every=5, max_temp=80, cool_sleep=30)
            X_batch, y_batch = X_batch.to(device), y_batch.to(device)
            optimizer.zero_grad()
            with torch.amp.autocast("cuda", enabled=use_amp):
                pred = model(X_batch)
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
            n_batch += 1
        scheduler.step()
        avg_train = epoch_loss / max(n_batch, 1)

        # Validation
        model.eval()
        val_loss, val_batch = 0.0, 0
        with torch.no_grad():
            for X_batch, y_batch in val_loader:
                X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                val_loss += criterion(model(X_batch), y_batch).item()
                val_batch += 1
        avg_val = val_loss / max(val_batch, 1)

        history["train_loss"].append(round(avg_train, 6))
        history["val_loss"].append(round(avg_val, 6))

        if avg_val < best_val_loss:
            best_val_loss = avg_val
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

        if verbose and (epoch + 1) % max(1, epochs // 5) == 0:
            print(f"    Epoch {epoch+1}/{epochs}  train={avg_train:.6f}  val={avg_val:.6f}")

    if best_state:
        model.load_state_dict(best_state)

    return {"model": model, "history": history, "best_val_loss": best_val_loss}


# ---------------------------------------------------------------------------
# Regime-aware sequence building
# ---------------------------------------------------------------------------

def build_regime_sequences(
    features_df: pd.DataFrame,
    regime_labels: pd.Series,
    target_col: str = "target",
    seq_len: int = 20,
) -> dict[str, tuple[np.ndarray, np.ndarray]]:
    """Build per-regime sequence datasets.

    Returns dict mapping regime name -> (X_sequences, y_targets).
    """
    feature_cols = [c for c in features_df.columns if c != target_col]
    results = {}

    for regime in regime_labels.unique():
        regime_mask = regime_labels == regime
        regime_features = features_df.loc[regime_mask].copy()

        if len(regime_features) < seq_len + 10:
            log.warning(f"Regime '{regime}': only {len(regime_features)} rows, skipping")
            continue

        X, y, _ = build_sequences(regime_features, seq_len=seq_len, target_col=target_col)
        if len(X) > 0:
            results[regime] = (X, y)
            log.info(f"Regime '{regime}': {len(X)} sequences")

    return results


# ---------------------------------------------------------------------------
# MoE DL walk-forward training
# ---------------------------------------------------------------------------

def train_moe_regimes_walk_forward(
    X: np.ndarray,
    y: np.ndarray,
    regime_labels: np.ndarray,
    expert_type: str = "lstm",
    hidden_size: int = 128,
    num_layers: int = 2,
    nhead: int = 4,
    dim_feedforward: int = 512,
    dropout: float = 0.2,
    seq_len: int = 20,
    n_folds: int = 5,
    epochs: int = 50,
    batch_size: int = 32,
    lr: float = 1e-3,
    device: str = "cpu",
    min_samples: int = 50,
) -> list[dict]:
    """Walk-forward MoE-DL training with expanding window.

    For each fold:
    1. Split by time (train/test)
    2. Group train samples by regime
    3. Train one DL expert per regime with enough samples
    4. Route test samples to appropriate expert for prediction
    5. Compute per-fold metrics
    """
    import torch

    n = len(X)
    fold_size = n // (n_folds + 1)
    fold_results = []
    input_size = X.shape[2]

    for fold in range(n_folds):
        train_end = fold_size * (fold + 1)
        test_end = min(train_end + fold_size, n)
        if test_end <= train_end:
            break

        X_train, y_train = X[:train_end], y[:train_end]
        X_test, y_test = X[train_end:test_end], y[train_end:test_end]
        reg_train = regime_labels[:train_end]
        reg_test = regime_labels[train_end:test_end]

        # Per-fold normalization (train-only statistics)
        mean = X_train.mean(axis=(0, 1), keepdims=True)
        std = X_train.std(axis=(0, 1), keepdims=True)
        std = np.where(std < 1e-8, 1.0, std)
        X_train_norm = (X_train - mean) / std
        X_test_norm = (X_test - mean) / std

        # Train per-regime experts
        experts = {}
        expert_stats = {}
        unique_regimes = np.unique(reg_train)

        for regime in unique_regimes:
            mask = reg_train == regime
            X_reg = X_train_norm[mask]
            y_reg = y_train[mask]

            if len(X_reg) < min_samples:
                log.warning(f"Fold {fold}: regime '{regime}' has {len(X_reg)} samples, skipping")
                continue

            model = build_expert_model(
                expert_type, input_size, hidden_size, num_layers,
                dropout, nhead, dim_feedforward, seq_len,
            )
            result = train_expert(
                model, X_reg, y_reg, epochs=epochs, batch_size=batch_size,
                lr=lr, device=device,
            )
            experts[regime] = result["model"]
            expert_stats[regime] = {
                "n_train": len(X_reg),
                "best_val_loss": result["best_val_loss"],
            }

        # Predict on test set using regime routing
        oos_preds = np.zeros(len(X_test_norm))
        regime_pred_counts = {}

        for regime in np.unique(reg_test):
            mask = reg_test == regime
            if regime in experts:
                expert = experts[regime]
                expert.eval()
                with torch.no_grad():
                    X_t = torch.tensor(X_test_norm[mask], dtype=torch.float32).to(device)
                    preds = expert(X_t).squeeze(-1).cpu().numpy()
                oos_preds[mask] = preds
                regime_pred_counts[regime] = int(mask.sum())
            elif experts:
                # Fallback to first available expert
                fallback = next(iter(experts.values()))
                fallback.eval()
                with torch.no_grad():
                    X_t = torch.tensor(X_test_norm[mask], dtype=torch.float32).to(device)
                    preds = fallback(X_t).squeeze(-1).cpu().numpy()
                oos_preds[mask] = preds
                regime_pred_counts[f"fallback_for_{regime}"] = int(mask.sum())
            else:
                oos_preds[mask] = 0.0

        # Metrics
        dir_acc = float(np.mean((oos_preds > 0) == (y_test > 0)))
        mse = float(np.mean((oos_preds - y_test) ** 2))

        fold_results.append({
            "fold": fold,
            "train_end": train_end,
            "test_size": len(X_test),
            "direction_accuracy": round(dir_acc, 4),
            "mse": round(mse, 6),
            "n_experts": len(experts),
            "expert_regimes": list(experts.keys()),
            "expert_stats": expert_stats,
            "regime_pred_counts": regime_pred_counts,
        })

        log.info(
            f"Fold {fold}: diracc={dir_acc:.4f}  mse={mse:.6f}  "
            f"experts={len(experts)}  test={len(X_test)}"
        )

    return fold_results


# ---------------------------------------------------------------------------
# Full pipeline
# ---------------------------------------------------------------------------

def train_moe_regimes_pipeline(
    symbol: str = "SPY",
    data_dir: str | None = None,
    regime_method: str = "price",
    expert_type: str = "lstm",
    hidden_size: int = 128,
    num_layers: int = 2,
    nhead: int = 4,
    dim_feedforward: int = 512,
    dropout: float = 0.2,
    seq_len: int = 20,
    lookback: int = 20,
    n_folds: int = 5,
    epochs: int = 50,
    batch_size: int = 32,
    lr: float = 1e-3,
    min_samples: int = 50,
    seed: int = 42,
    start: str = "2015-01-01",
    end: str = "2025-01-01",
    output_dir: str | None = None,
    raw_data: pd.DataFrame | None = None,
) -> dict:
    """Run full MoE-DL training pipeline.

    Returns dict with walk-forward results, baseline comparison, config.
    """
    import torch

    np.random.seed(seed)
    t0 = time.time()
    device = "cuda" if torch.cuda.is_available() else "cpu"

    # Load data
    if raw_data is not None:
        raw = raw_data
        log.info(f"Using preloaded data: {len(raw)} rows")
    else:
        log.info(f"Loading data for {symbol}...")
        data_path = Path(data_dir) if data_dir else SCRIPTS_DIR.parent / "datasets" / "yfinance"
        raw = load_data(data_path, symbol, start, end)
    data_hash = compute_data_hash(raw)
    log.info(f"Data: {len(raw)} rows for {symbol} ({data_hash[:8]})")

    if len(raw) < 500:
        raise ValueError(f"Insufficient data: {len(raw)} rows (need >= 500)")

    # Features
    engineer = FeatureEngineer(lookback=lookback)
    features = engineer.transform(raw)
    log.info(f"Features: {len(features)} rows, {len(features.columns) - 1} cols")

    # Sequences
    X, y, feature_cols = build_sequences(features, seq_len=seq_len)
    log.info(f"Sequences: {len(X)} samples, shape={X.shape}")

    # Regime detection on aligned price series
    aligned_prices = raw["Close"].iloc[lookback:lookback + len(y)]
    regime_series = detect_regimes(aligned_prices, method=regime_method)

    # Align regime labels to sequences (trim first seq_len labels)
    regime_labels = regime_series.iloc[-len(y):].values

    regime_counts = pd.Series(regime_labels).value_counts()
    log.info(f"Regime distribution:\n{regime_counts.to_string()}")

    # Walk-forward MoE-DL training
    log.info(f"Starting MoE-DL walk-forward ({n_folds} folds, expert={expert_type})...")
    wf_results = train_moe_regimes_walk_forward(
        X, y, regime_labels,
        expert_type=expert_type,
        hidden_size=hidden_size,
        num_layers=num_layers,
        nhead=nhead,
        dim_feedforward=dim_feedforward,
        dropout=dropout,
        seq_len=seq_len,
        n_folds=n_folds,
        epochs=epochs,
        batch_size=batch_size,
        lr=lr,
        device=device,
        min_samples=min_samples,
    )

    # Majority baseline
    majority_class = 1 if np.mean(y > 0) > 0.5 else 0
    majority_acc = float(np.mean((y > 0).astype(int) == majority_class))

    # Aggregate
    fold_diraccs = [r["direction_accuracy"] for r in wf_results]
    mean_diracc = np.mean(fold_diraccs) if fold_diraccs else 0.0
    std_diracc = np.std(fold_diraccs) if len(fold_diraccs) > 1 else 0.0
    beats_majority = mean_diracc > majority_acc
    elapsed = time.time() - t0

    result = {
        "symbol": symbol,
        "expert_type": expert_type,
        "regime_method": regime_method,
        "device": device,
        "data_hash": data_hash[:12],
        "n_folds": len(wf_results),
        "n_samples": len(X),
        "n_features": X.shape[2],
        "seq_len": seq_len,
        "majority_baseline_acc": round(majority_acc, 4),
        "majority_class": majority_class,
        "target_balance": round(float(np.mean(y > 0)), 4),
        "moe_mean_diracc": round(mean_diracc, 4),
        "moe_std_diracc": round(std_diracc, 4),
        "moe_fold_diraccs": [round(a, 4) for a in fold_diraccs],
        "beats_majority": bool(beats_majority),
        "regime_counts": {str(k): int(v) for k, v in regime_counts.items()},
        "config": {
            "hidden_size": hidden_size,
            "num_layers": num_layers,
            "nhead": nhead,
            "dim_feedforward": dim_feedforward,
            "dropout": dropout,
            "epochs": epochs,
            "batch_size": batch_size,
            "lr": lr,
            "lookback": lookback,
            "min_samples": min_samples,
            "seed": seed,
        },
        "fold_details": wf_results,
        "elapsed_seconds": round(elapsed, 1),
    }

    # Save
    if output_dir:
        out = Path(output_dir)
        out.mkdir(parents=True, exist_ok=True)
        rf = out / f"moe_regimes_{symbol}_{expert_type}_{regime_method}_seed{seed}.json"
        rf.write_text(json.dumps(result, indent=2, default=str), encoding="utf-8")
        log.info(f"Results saved to {rf}")

    log.info(
        f"\n{'='*60}\n"
        f"MoE-DL Results for {symbol} ({expert_type}, {regime_method} regimes)\n"
        f"{'='*60}\n"
        f"Folds: {len(wf_results)} | Samples: {len(X)} | Device: {device}\n"
        f"Majority baseline: {majority_acc:.4f}\n"
        f"MoE mean DirAcc: {mean_diracc:.4f} +/- {std_diracc:.4f}\n"
        f"BEATS MAJORITY: {'YES' if beats_majority else 'NO'}\n"
        f"Per fold: {[f'{a:.4f}' for a in fold_diraccs]}\n"
        f"Elapsed: {elapsed:.1f}s\n"
        f"{'='*60}"
    )

    return result


# ---------------------------------------------------------------------------
# Multi-seed evaluation
# ---------------------------------------------------------------------------

def run_multiseed(
    seeds: list[int] = (0, 1, 7, 42, 123),
    **kwargs,
) -> dict:
    """Run pipeline across multiple seeds for statistical significance."""
    all_results = []
    for seed in seeds:
        log.info(f"\n{'#'*60}\n# Seed {seed}\n{'#'*60}")
        result = train_moe_regimes_pipeline(seed=seed, **kwargs)
        all_results.append(result)

    diraccs = [r["moe_mean_diracc"] for r in all_results]
    mean = np.mean(diraccs)
    std = np.std(diraccs)

    majority = all_results[0]["majority_baseline_acc"]
    improvement = (mean - majority) / majority * 100 if majority > 0 else 0.0

    # One-sample t-test vs majority baseline
    from scipy import stats as sp_stats
    if len(diraccs) >= 3:
        t_stat, p_value = sp_stats.ttest_1samp(diraccs, majority)
        significant = p_value < 0.05
    else:
        t_stat, p_value = 0.0, 1.0
        significant = False

    summary = {
        "n_seeds": len(seeds),
        "seeds": list(seeds),
        "mean_diracc": round(mean, 4),
        "std_diracc": round(std, 4),
        "majority_baseline": round(majority, 4),
        "improvement_pct": round(improvement, 2),
        "t_stat": round(float(t_stat), 4),
        "p_value": round(float(p_value), 6),
        "significant": bool(significant),
        "per_seed_diraccs": [r["moe_mean_diracc"] for r in all_results],
        "expert_type": kwargs.get("expert_type", "lstm"),
        "regime_method": kwargs.get("regime_method", "price"),
        "symbol": kwargs.get("symbol", "SPY"),
    }

    # Save combined results
    output_dir = kwargs.get("output_dir")
    if output_dir:
        out = Path(output_dir)
        out.mkdir(parents=True, exist_ok=True)
        sym = kwargs.get("symbol", "SPY")
        et = kwargs.get("expert_type", "lstm")
        rm = kwargs.get("regime_method", "price")
        combined_file = out / f"moe_regimes_{sym}_{et}_{rm}_multiseed.json"
        combined_file.write_text(
            json.dumps({"summary": summary, "seeds": all_results}, indent=2, default=str),
            encoding="utf-8",
        )
        log.info(f"Combined results saved to {combined_file}")

    log.info(
        f"\n{'='*60}\n"
        f"MULTI-SEED RESULTS\n"
        f"{'='*60}\n"
        f"Mean DirAcc: {mean:.4f} +/- {std:.4f}\n"
        f"Improvement: {improvement:.2f}%\n"
        f"Significant: {significant} (p={p_value:.4f})\n"
        f"{'='*60}"
    )

    return summary


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="MoE-DL training pipeline with regime-aware routing"
    )
    parser.add_argument("--data-dir", default=None, help="Data directory")
    parser.add_argument("--symbol", default="SPY", help="Ticker symbol")
    parser.add_argument("--start", default="2015-01-01")
    parser.add_argument("--end", default="2025-01-01")
    parser.add_argument(
        "--expert", default="lstm", choices=["lstm", "gru", "transformer"],
        help="DL expert model type",
    )
    parser.add_argument(
        "--regime-method", default="price", choices=["price", "hmm"],
        help="Regime detection method",
    )
    parser.add_argument("--hidden-size", type=int, default=128)
    parser.add_argument("--num-layers", type=int, default=2)
    parser.add_argument("--nhead", type=int, default=4, help="Transformer heads")
    parser.add_argument("--dim-feedforward", type=int, default=512)
    parser.add_argument("--dropout", type=float, default=0.2)
    parser.add_argument("--seq-len", type=int, default=20)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--n-folds", type=int, default=5)
    parser.add_argument("--epochs", type=int, default=50)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--lr", type=float, default=1e-3)
    parser.add_argument("--min-samples", type=int, default=50)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--seeds", type=int, nargs="+", default=None,
                        help="Multiple seeds for significance testing")
    parser.add_argument("--output-dir", default=None)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("-v", "--verbose", action="store_true")

    args = parser.parse_args()

    level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(level=level, format="%(asctime)s %(levelname)-8s %(message)s", datefmt="%H:%M:%S")

    output_dir = args.output_dir or str(SCRIPTS_DIR.parent / "results" / "moe_regimes")

    if args.dry_run:
        log.info("DRY-RUN: Using synthetic data (500 rows, 2 epochs)")
        raw = generate_synthetic_data(500)
        args.epochs = 2
        args.n_folds = 2
    else:
        raw = None

    kwargs = dict(
        symbol=args.symbol,
        data_dir=args.data_dir,
        regime_method=args.regime_method,
        expert_type=args.expert,
        hidden_size=args.hidden_size,
        num_layers=args.num_layers,
        nhead=args.nhead,
        dim_feedforward=args.dim_feedforward,
        dropout=args.dropout,
        seq_len=args.seq_len,
        lookback=args.lookback,
        n_folds=args.n_folds,
        epochs=args.epochs,
        batch_size=args.batch_size,
        lr=args.lr,
        min_samples=args.min_samples,
        output_dir=output_dir,
        start=args.start,
        end=args.end,
        raw_data=raw,
    )

    if args.seeds:
        summary = run_multiseed(seeds=args.seeds, **kwargs)
        print(f"\nMulti-seed summary: {summary['mean_diracc']:.4f} +/- {summary['std_diracc']:.4f}")
        print(f"  Improvement vs majority: {summary['improvement_pct']:.2f}%")
        print(f"  Significant (p<0.05): {summary['significant']}")
    else:
        result = train_moe_regimes_pipeline(seed=args.seed, **kwargs)
        if args.dry_run:
            print("DRY-RUN complete. MoE-DL pipeline validated.")

    return 0


if __name__ == "__main__":
    sys.exit(main())
