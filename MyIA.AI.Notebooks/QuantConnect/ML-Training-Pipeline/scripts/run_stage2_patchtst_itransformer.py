"""
Stage 2: PatchTST + iTransformer baseline on crypto panier (10 coins).

Runs walk-forward 5-fold x 4 seeds for both PatchTST (Nie et al., ICLR 2023)
and iTransformer (Li et al., ICLR 2024) on the CRYPTO_PANIER_SYMBOLS universe.

Produces honest BEATS/NO BEATS/INCONCLUSIVE verdict per coin per model,
with direction accuracy edge over majority-class baseline (>= 2 sigma).

Usage:
    python run_stage2_patchtst_itransformer.py
    python run_stage2_patchtst_itransformer.py --dry-run
    python run_stage2_patchtst_itransformer.py --seeds 0,1,7 --symbols BTC-USD ETH-USD
    python run_stage2_patchtst_itransformer.py --model patchtst
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime
from pathlib import Path

import numpy as np
import torch

SCRIPT_DIR = Path(__file__).resolve().parent
CHECKPOINTS_DIR = SCRIPT_DIR.parent / "checkpoints"
DATA_DIR = SCRIPT_DIR.parent.parent / "datasets" / "yfinance" / "crypto_panier"

sys.path.insert(0, str(SCRIPT_DIR))
sys.path.append(str(SCRIPT_DIR.parent.parent / "shared"))

from graph_builder import CRYPTO_PANIER_SYMBOLS
from walk_forward import WalkForwardSplitter

from features import FeatureEngineer
from sequence_utils import build_sequences, normalize_sequences
from baselines import oos_direction_distribution
from gpu_training import setup_amp

from train_patchtst import PatchTSTModel
from train_itransformer import iTransformerModel

STAGE2_SEEDS = [0, 1, 7, 42]
STAGE2_N_SPLITS = 5
STAGE2_GAP = 5
STAGE2_SEQ_LEN = 20
STAGE2_PRED_LEN = 5
STAGE2_EPOCHS = 50

BASE_INDICATORS = [
    "returns", "volatility", "volume_ratio", "ma_ratios",
    "rsi", "macd", "bollinger", "true_range_atr", "obv",
]


def load_coin_data(symbol: str) -> "pd.DataFrame":
    import pandas as pd
    matches = list(DATA_DIR.glob(f"{symbol}_*.csv"))
    if not matches:
        raise FileNotFoundError(f"No data for {symbol} in {DATA_DIR}")
    df = pd.read_csv(matches[0], index_col=0, parse_dates=True)
    df.columns = [c.strip().capitalize() for c in df.columns]
    return df


def build_model(
    model_type: str,
    n_vars: int,
    seq_len: int,
    pred_len: int,
    device: str,
) -> torch.nn.Module:
    if model_type == "patchtst":
        patch_len = min(8, seq_len // 2)
        stride = max(1, patch_len // 2)
        return PatchTSTModel(
            n_vars=n_vars, seq_len=seq_len, pred_len=pred_len,
            patch_len=patch_len, stride=stride,
            d_model=64, n_heads=4, n_layers=2,
            dropout=0.2, fc_dropout=0.2,
            channel_independence=True,
        ).to(device)
    elif model_type == "itransformer":
        return iTransformerModel(
            n_vars=n_vars, seq_len=seq_len, pred_len=pred_len,
            d_model=64, n_heads=4, n_layers=2,
            dropout=0.2, ff_dropout=0.2,
        ).to(device)
    else:
        raise ValueError(f"Unknown model: {model_type}")


def train_single_fold(
    model_type: str,
    X_train: np.ndarray,
    y_train: np.ndarray,
    X_test: np.ndarray,
    y_test: np.ndarray,
    n_vars: int,
    seq_len: int,
    pred_len: int,
    seed: int,
    epochs: int,
    batch_size: int,
    device: str,
) -> dict:
    from torch.utils.data import DataLoader, TensorDataset

    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)

    # Internal train/val split (85/15)
    val_cutoff = int(len(X_train) * 0.85)
    X_tr, X_val = X_train[:val_cutoff], X_train[val_cutoff:]
    y_tr, y_val = y_train[:val_cutoff], y_train[val_cutoff:]

    # Normalize on train stats only
    X_tr_n, X_val_n, X_test_n, _, _ = normalize_sequences(X_tr, X_val, X_test)

    model = build_model(model_type, n_vars, seq_len, pred_len, device)

    train_ds = TensorDataset(
        torch.tensor(X_tr_n, dtype=torch.float32),
        torch.tensor(y_tr, dtype=torch.float32),
    )
    val_ds = TensorDataset(
        torch.tensor(X_val_n, dtype=torch.float32),
        torch.tensor(y_val, dtype=torch.float32),
    )
    test_ds = TensorDataset(
        torch.tensor(X_test_n, dtype=torch.float32),
        torch.tensor(y_test, dtype=torch.float32),
    )
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=False)
    val_loader = DataLoader(val_ds, batch_size=batch_size)
    test_loader = DataLoader(test_ds, batch_size=batch_size)

    optimizer = torch.optim.AdamW(model.parameters(), lr=5e-4, weight_decay=1e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingWarmRestarts(
        optimizer, T_0=10, T_mult=2
    )
    criterion = torch.nn.MSELoss()
    use_amp, grad_scaler = setup_amp()

    best_val_loss = float("inf")
    best_state = None

    for epoch in range(epochs):
        model.train()
        epoch_loss = 0.0
        n_batches = 0
        for X_batch, y_batch in train_loader:
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
            n_batches += 1
        scheduler.step()

        model.eval()
        val_loss = 0.0
        val_batches = 0
        with torch.no_grad():
            for X_batch, y_batch in val_loader:
                X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                with torch.amp.autocast("cuda", enabled=use_amp):
                    val_loss += criterion(model(X_batch), y_batch).item()
                val_batches += 1
        avg_val = val_loss / max(val_batches, 1)
        if avg_val < best_val_loss:
            best_val_loss = avg_val
            best_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

    if best_state:
        model.load_state_dict(best_state)
    model.eval()

    # OOS predictions
    all_preds, all_targets = [], []
    with torch.no_grad():
        for X_batch, y_batch in test_loader:
            X_batch = X_batch.to(device)
            with torch.amp.autocast("cuda", enabled=use_amp):
                all_preds.append(model(X_batch).cpu().numpy())
            all_targets.append(y_batch.numpy())

    preds = np.concatenate(all_preds)
    targets = np.concatenate(all_targets)

    mse = float(np.mean((preds - targets) ** 2))
    mae = float(np.mean(np.abs(preds - targets)))

    # Direction accuracy on first prediction step
    pred_s1 = preds[:, 0].flatten()
    target_s1 = targets[:, 0].flatten()
    diracc = float(np.mean((pred_s1 > 0) == (target_s1 > 0)))

    return {
        "mse": round(mse, 6),
        "mae": round(mae, 6),
        "diracc": round(diracc, 4),
        "preds": preds,
        "targets": targets,
        "n_test": len(preds),
    }


def run_walk_forward(
    model_type: str,
    X: np.ndarray,
    y: np.ndarray,
    n_vars: int,
    seed: int,
    n_splits: int,
    gap: int,
    seq_len: int,
    pred_len: int,
    epochs: int,
    batch_size: int,
    device: str,
) -> dict:
    splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
    fold_results = []
    oos_preds = np.full((len(y), pred_len), np.nan)
    oos_targets = np.full((len(y), pred_len), np.nan)

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(X)):
        if len(test_idx) == 0:
            continue

        result = train_single_fold(
            model_type, X[train_idx], y[train_idx],
            X[test_idx], y[test_idx],
            n_vars=n_vars, seq_len=seq_len, pred_len=pred_len,
            seed=seed, epochs=epochs, batch_size=batch_size, device=device,
        )

        oos_preds[test_idx[:len(result["preds"])]] = result["preds"]
        oos_targets[test_idx[:len(result["targets"])]] = result["targets"]
        fold_results.append({
            "fold": fold_idx,
            "mse": result["mse"],
            "diracc": result["diracc"],
            "train_size": len(train_idx),
            "test_size": len(test_idx),
        })

    # Aggregate OOS
    valid_mask = ~np.isnan(oos_preds[:, 0])
    valid_preds = oos_preds[valid_mask]
    valid_targets = oos_targets[valid_mask]

    if len(valid_preds) < 10:
        return {"seed": seed, "status": "insufficient_oos"}

    oos_mse = float(np.mean((valid_preds - valid_targets) ** 2))
    pred_s1 = valid_preds[:, 0].flatten()
    target_s1 = valid_targets[:, 0].flatten()
    oos_diracc = float(np.mean((pred_s1 > 0) == (target_s1 > 0)))

    majority_freq = float(np.mean(target_s1 > 0))
    majority_acc = max(majority_freq, 1.0 - majority_freq)
    edge = oos_diracc - majority_acc

    return {
        "seed": seed,
        "oos_mse": round(oos_mse, 6),
        "oos_diracc": round(oos_diracc, 4),
        "majority_acc": round(majority_acc, 4),
        "edge_vs_majority": round(edge, 4),
        "n_oos": int(valid_mask.sum()),
        "n_folds": len(fold_results),
        "fold_details": fold_results,
    }


def compute_verdict(seed_results: list[dict]) -> dict:
    edges = [r["edge_vs_majority"] for r in seed_results]
    mean_edge = float(np.mean(edges))
    std_edge = float(np.std(edges, ddof=1)) if len(edges) > 1 else 0.0
    t_stat = mean_edge / std_edge if std_edge > 1e-10 else 0.0

    diraccs = [r["oos_diracc"] for r in seed_results]
    mses = [r["oos_mse"] for r in seed_results]

    if mean_edge > 0 and t_stat > 2.0:
        verdict = "BEATS"
    elif mean_edge < 0:
        verdict = "NO BEATS"
    else:
        verdict = "INCONCLUSIVE"

    return {
        "verdict": verdict,
        "mean_edge_vs_majority": round(mean_edge, 4),
        "std_edge": round(std_edge, 4),
        "t_stat": round(t_stat, 4),
        "mean_diracc": round(float(np.mean(diraccs)), 4),
        "mean_mse": round(float(np.mean(mses)), 6),
        "seeds": seed_results,
    }


def run_single_coin(
    symbol: str,
    model_type: str,
    seeds: list[int],
    n_splits: int,
    gap: int,
    seq_len: int,
    pred_len: int,
    epochs: int,
    batch_size: int,
    lookback: int,
    device: str,
    dry_run: bool,
) -> dict:
    import pandas as pd

    print(f"\n{'='*60}")
    print(f"  {symbol} | {model_type}")
    print(f"{'='*60}")

    coin_df = load_coin_data(symbol)
    if dry_run:
        coin_df = coin_df.iloc[-500:]

    print(f"  Data: {len(coin_df)} rows ({coin_df.index.min().date()} -> {coin_df.index.max().date()})")

    # Features
    engineer = FeatureEngineer(lookback=lookback, indicators=BASE_INDICATORS)
    features = engineer.transform(coin_df, add_target=True)
    n_features = len(features.columns) - 1  # exclude target

    # Build sequences
    X, y, feature_cols = build_sequences(features, seq_len=seq_len, pred_len=pred_len)
    print(f"  Sequences: {len(X)} | seq_len={seq_len}, pred_len={pred_len}, n_vars={n_features}")

    # Multi-seed walk-forward
    seed_results = []
    for seed in seeds:
        t0 = time.time()
        result = run_walk_forward(
            model_type, X, y, n_vars=n_features,
            seed=seed, n_splits=n_splits, gap=gap,
            seq_len=seq_len, pred_len=pred_len,
            epochs=epochs, batch_size=batch_size, device=device,
        )
        elapsed = time.time() - t0
        if result.get("status") == "insufficient_oos":
            print(f"    seed={seed}: INSUFFICIENT OOS")
            continue
        seed_results.append(result)
        print(
            f"    seed={seed}: DirAcc={result['oos_diracc']:.4f}  "
            f"edge={result['edge_vs_majority']:+.4f}  "
            f"MSE={result['oos_mse']:.6f}  ({elapsed:.1f}s)"
        )

    if not seed_results:
        return {
            "coin": symbol, "model": model_type,
            "verdict": "ERROR", "error": "no valid seeds",
        }

    verdict_data = compute_verdict(seed_results)
    verdict_data["coin"] = symbol
    verdict_data["model"] = model_type
    verdict_data["n_features"] = n_features
    verdict_data["n_seeds"] = len(seed_results)
    verdict_data["n_splits"] = n_splits
    verdict_data["seq_len"] = seq_len
    verdict_data["pred_len"] = pred_len

    print(f"  VERDICT: {verdict_data['verdict']}")
    print(f"    mean_edge={verdict_data['mean_edge_vs_majority']:+.4f}  "
          f"t={verdict_data['t_stat']:.4f}  "
          f"mean_diracc={verdict_data['mean_diracc']:.4f}")

    return verdict_data


def main():
    parser = argparse.ArgumentParser(
        description="Stage 2: PatchTST + iTransformer on crypto panier 10 coins"
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--symbols", nargs="+", default=None)
    parser.add_argument("--model", choices=["patchtst", "itransformer", "both"], default="both")
    parser.add_argument("--seeds", type=str, default=None, help="Comma-separated seeds")
    parser.add_argument("--n-splits", type=int, default=STAGE2_N_SPLITS)
    parser.add_argument("--gap", type=int, default=STAGE2_GAP)
    parser.add_argument("--seq-len", type=int, default=STAGE2_SEQ_LEN)
    parser.add_argument("--pred-len", type=int, default=STAGE2_PRED_LEN)
    parser.add_argument("--epochs", type=int, default=STAGE2_EPOCHS)
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--lookback", type=int, default=20)
    parser.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    parser.add_argument("--output-dir", default=None)
    args = parser.parse_args()

    symbols = args.symbols or CRYPTO_PANIER_SYMBOLS
    seeds = [int(s) for s in args.seeds.split(",")] if args.seeds else STAGE2_SEEDS

    models = ["patchtst", "itransformer"] if args.model == "both" else [args.model]

    print("Stage 2: PatchTST + iTransformer Baseline")
    print(f"  Coins: {len(symbols)}, Models: {models}")
    print(f"  Seeds: {seeds}, Walk-forward: {args.n_splits} folds, gap={args.gap}")
    print(f"  Seq: {args.seq_len}, Pred: {args.pred_len}, Epochs: {args.epochs}")
    print(f"  Device: {args.device}")

    all_results = []
    for model_type in models:
        for symbol in symbols:
            result = run_single_coin(
                symbol=symbol,
                model_type=model_type,
                seeds=seeds,
                n_splits=args.n_splits,
                gap=args.gap,
                seq_len=args.seq_len,
                pred_len=args.pred_len,
                epochs=args.epochs,
                batch_size=args.batch_size,
                lookback=args.lookback,
                device=args.device,
                dry_run=args.dry_run,
            )
            all_results.append(result)

    # Summary table
    print(f"\n{'='*90}")
    print("STAGE 2 VERDICT TABLE")
    print(f"{'='*90}")
    print(
        f"{'Coin':10s} {'Model':14s} {'Verdict':14s} {'Edge':>8s} "
        f"{'t':>6s} {'DirAcc':>8s} {'MSE':>10s}"
    )
    print("-" * 90)

    for r in all_results:
        print(
            f"{r.get('coin','?'):10s} {r.get('model','?'):14s} "
            f"{r.get('verdict','?'):14s} "
            f"{r.get('mean_edge_vs_majority',0):+8.4f} "
            f"{r.get('t_stat',0):6.3f} "
            f"{r.get('mean_diracc',0):8.4f} "
            f"{r.get('mean_mse',0):10.6f}"
        )

    # Save results
    output_dir = Path(args.output_dir) if args.output_dir else CHECKPOINTS_DIR / "stage2_patchtst_itransformer"
    output_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_file = output_dir / f"stage2_results_{ts}.json"

    # Strip large arrays before saving
    save_results = []
    for r in all_results:
        sr = {k: v for k, v in r.items() if k != "seeds"}
        sr["seeds"] = []
        for s in r.get("seeds", []):
            sd = {k: v for k, v in s.items() if k not in ("fold_details",)}
            sr["seeds"].append(sd)
        save_results.append(sr)

    out_file.write_text(json.dumps(save_results, indent=2, default=str), encoding="utf-8")
    latest = output_dir / "stage2_latest.json"
    latest.write_text(json.dumps(save_results, indent=2, default=str), encoding="utf-8")
    print(f"\nResults saved: {out_file}")

    # Summary counts
    verdicts = [r.get("verdict", "ERROR") for r in all_results]
    print(f"\nSummary: BEATS={verdicts.count('BEATS')}  "
          f"NO BEATS={verdicts.count('NO BEATS')}  "
          f"INCONCLUSIVE={verdicts.count('INCONCLUSIVE')}  "
          f"ERROR={verdicts.count('ERROR')}")


if __name__ == "__main__":
    main()
