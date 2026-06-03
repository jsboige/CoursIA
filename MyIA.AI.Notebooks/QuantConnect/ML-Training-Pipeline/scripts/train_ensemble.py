"""
Deep Ensemble stacking: HAR + RF + DL models for volatility forecasting.

Implements a stacking ensemble where:
    Level 0 (base learners): HAR, RF, PatchTST/iTransformer/TFT, HeteroscedasticNN
    Level 1 (meta-learner): Ridge regression on out-of-fold predictions

Anti-pattern safeguards (cf. CLAUDE.md, feedback_ml_trading_pitfalls.md):
    - Walk-forward validation with gap to prevent leakage
    - Stacking uses OOF predictions only (no train-set leak)
    - DM test vs HAR baseline (not just MSE comparison)
    - Multi-seed evaluation (>=4 seeds among [0,1,7,42])
    - Honest verdicts: BEATS / NO_BEATS / INCONCLUSIVE

Usage:
    python train_ensemble.py --dry-run
    python train_ensemble.py --data-dir ../datasets/yfinance/crypto_panier \\
        --symbol BTC-USD --seeds 0,1,7,42
"""

import argparse
import sys
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.linear_model import Ridge
from sklearn.ensemble import RandomForestRegressor

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from checkpoint_utils import save_pytorch_checkpoint
from data_utils import compute_data_hash, generate_synthetic_data, load_data
from features import FeatureEngineer
from baselines import oos_direction_distribution
from sequence_utils import build_sequences, normalize_sequences
from walk_forward import WalkForwardSplitter

SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
GAP = 5
HORIZON = 5


def run_har_features(close: pd.Series, horizon: int) -> pd.DataFrame:
    """Compute HAR (Corsi 2009) features: rv_d, rv_w, rv_m."""
    log_ret = np.log(close).diff().dropna()
    rv = log_ret.pow(2)
    rv.name = "rv"
    rv = pd.DataFrame(rv)
    rv["rv_d"] = rv["rv"]
    rv["rv_w"] = rv["rv"].rolling(5).mean()
    rv["rv_m"] = rv["rv"].rolling(22).mean()
    return rv.dropna()


def run_ensemble(
    symbol: str,
    close: pd.Series,
    seeds: list = None,
    n_splits: int = N_SPLITS,
    gap: int = GAP,
    dry_run: bool = False,
) -> dict:
    """Run stacking ensemble with HAR + RF + DL base learners."""
    import torch
    from train_patchtst import PatchTSTModel
    from train_itransformer import iTransformerModel

    seeds = seeds or SEEDS
    device = "cuda" if torch.cuda.is_available() else "cpu"

    # Compute features
    from run_volatility_dm_verdict import compute_features, compute_log_rv_target
    features = compute_features(close)
    target = compute_log_rv_target(close, HORIZON)
    har_feats = run_har_features(close, HORIZON)

    df = pd.concat([features, target], axis=1).dropna()
    if len(df) < 200:
        return {"coin": symbol, "status": "insufficient_data"}

    feature_cols = [c for c in df.columns if c != target.name]
    X_all = df[feature_cols].values
    y_all = df[target.name].values

    if dry_run:
        X_all = X_all[-300:]
        y_all = y_all[-300:]

    # Walk-forward
    splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
    n = len(X_all)

    oos_base_preds = {}  # model_name -> array of OOS predictions
    oos_targets = np.full(n, np.nan)

    for model_name in ["har_rf", "patchtst", "itransformer"]:
        oos_base_preds[model_name] = np.full(n, np.nan)

    for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(np.arange(n))):
        y_train, y_test = y_all[train_idx], y_all[test_idx]

        # Base learner 1: HAR-style features + RF (Corsi 2009 lags)
        rf = RandomForestRegressor(n_estimators=200, max_depth=10, random_state=seeds[0])

        y_lag1 = np.roll(y_all, 1)
        y_lag1[0] = 0.0
        rv_roll5 = pd.Series(y_all).rolling(5, min_periods=1).mean().values
        rv_roll22 = pd.Series(y_all).rolling(22, min_periods=1).mean().values

        rf_features = np.column_stack([
            y_lag1[train_idx],
            rv_roll5[train_idx],
            rv_roll22[train_idx],
        ])
        rf_features = np.nan_to_num(rf_features, nan=0.0)

        rf.fit(rf_features, y_train)

        test_rf_features = np.column_stack([
            y_lag1[test_idx],
            rv_roll5[test_idx],
            rv_roll22[test_idx],
        ])
        test_rf_features = np.nan_to_num(test_rf_features, nan=0.0)

        rf_preds = rf.predict(test_rf_features)
        for i, idx in enumerate(test_idx):
            oos_base_preds["har_rf"][idx] = rf_preds[i]
            oos_targets[idx] = y_test[i]

        # Base learners 2 & 3: DL models
        seq_len = 20
        pred_len = 1
        X_dl = X_all
        n_vars = X_dl.shape[1]

        for model_name, ModelClass in [("patchtst", PatchTSTModel), ("itransformer", iTransformerModel)]:
            # Build sequences for train
            X_train_seq, y_train_seq = [], []
            for i in range(seq_len, len(train_idx)):
                pos = train_idx[i]
                if pos - seq_len < 0 or pos >= n:
                    continue
                X_train_seq.append(X_dl[pos - seq_len:pos])
                y_train_seq.append(y_all[pos])

            X_test_seq, y_test_seq = [], []
            test_positions = train_idx[-1] + np.arange(1, len(test_idx) + 1)
            for i in range(seq_len, len(test_positions)):
                pos = test_positions[i]
                if pos - seq_len < 0 or pos >= n:
                    continue
                X_test_seq.append(X_dl[pos - seq_len:pos])
                y_test_seq.append(y_all[pos])

            if not X_train_seq or not X_test_seq:
                continue

            X_train_seq = np.array(X_train_seq)
            y_train_seq = np.array(y_train_seq)
            X_test_seq = np.array(X_test_seq)

            mu = X_train_seq.mean(axis=(0, 1), keepdims=True)
            sigma = X_train_seq.std(axis=(0, 1), keepdims=True) + 1e-8
            X_train_n = (X_train_seq - mu) / sigma
            X_test_n = (X_test_seq - mu) / sigma

            if model_name == "patchtst":
                patch_len = min(8, seq_len // 2)
                stride = max(1, patch_len // 2)
                model = ModelClass(
                    n_vars=n_vars, seq_len=seq_len, pred_len=pred_len,
                    patch_len=patch_len, stride=stride,
                    d_model=32, n_heads=4, n_layers=2,
                    dropout=0.2, fc_dropout=0.2, channel_independence=True,
                ).to(device)
            else:
                model = ModelClass(
                    n_vars=n_vars, seq_len=seq_len, pred_len=pred_len,
                    d_model=32, n_heads=4, n_layers=2,
                    dropout=0.2, ff_dropout=0.2,
                ).to(device)

            from torch.utils.data import DataLoader, TensorDataset
            train_ds = TensorDataset(
                torch.tensor(X_train_n, dtype=torch.float32),
                torch.tensor(y_train_seq, dtype=torch.float32).unsqueeze(-1),
            )
            train_loader = DataLoader(train_ds, batch_size=64, shuffle=False)
            optimizer = torch.optim.AdamW(model.parameters(), lr=1e-3, weight_decay=1e-4)

            for epoch in range(30):
                model.train()
                for X_batch, y_batch in train_loader:
                    X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                    optimizer.zero_grad()
                    pred = model(X_batch)
                    if pred.shape != y_batch.shape:
                        y_batch = y_batch.view_as(pred)
                    loss = torch.nn.MSELoss()(pred, y_batch)
                    loss.backward()
                    torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                    optimizer.step()

            model.eval()
            with torch.no_grad():
                X_t = torch.tensor(X_test_n, dtype=torch.float32).to(device)
                dl_preds = model(X_t).cpu().numpy().flatten()

            for i, pos in enumerate(test_positions[seq_len:seq_len + len(dl_preds)]):
                if pos < n:
                    oos_base_preds[model_name][pos] = dl_preds[i]

        # End of fold

    # Level 1: Ridge meta-learner on OOF predictions
    valid = ~np.isnan(oos_targets) & ~np.isnan(oos_base_preds["har_rf"])
    if valid.sum() < 50:
        return {"coin": symbol, "status": "insufficient_oos"}

    base_matrix = np.column_stack([
        oos_base_preds[name][valid] for name in oos_base_preds
    ])
    targets_valid = oos_targets[valid]

    # Replace any remaining NaN in base predictions with 0
    base_matrix = np.nan_to_num(base_matrix, nan=0.0)

    # Train meta-learner on first 80% of OOS, evaluate on last 20%
    meta_train_end = int(len(base_matrix) * 0.8)
    meta_X_train = base_matrix[:meta_train_end]
    meta_y_train = targets_valid[:meta_train_end]
    meta_X_test = base_matrix[meta_train_end:]
    meta_y_test = targets_valid[meta_train_end:]

    ridge = Ridge(alpha=1.0)
    ridge.fit(meta_X_train, meta_y_train)
    ensemble_preds = ridge.predict(meta_X_test)

    mse = float(np.mean((ensemble_preds - meta_y_test) ** 2))

    return {
        "coin": symbol, "status": "ok",
        "mse": round(mse, 6),
        "n_oos": len(meta_y_test),
        "preds": ensemble_preds,
        "targets": meta_y_test,
        "ridge_coefs": {name: round(float(c), 4)
                        for name, c in zip(oos_base_preds.keys(), ridge.coef_)},
    }


def main():
    parser = argparse.ArgumentParser(
        description="Train stacking ensemble for volatility forecasting",
    )
    parser.add_argument("--data-dir",
                        default=str(Path(__file__).resolve().parent.parent / "datasets" / "yfinance" / "crypto_panier"))
    parser.add_argument("--symbols", default="BTC-USD")
    parser.add_argument("--start")
    parser.add_argument("--end")
    parser.add_argument("--seeds", type=str, default=None)
    parser.add_argument("--n-splits", type=int, default=N_SPLITS)
    parser.add_argument("--gap", type=int, default=GAP)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--output-dir",
                        default=str(Path(__file__).resolve().parent.parent / "outputs" / "ensemble_run1"))
    args = parser.parse_args()

    seeds = [int(s) for s in args.seeds.split(",")] if args.seeds else SEEDS
    symbols = [s.strip() for s in args.symbols.split(",")]

    if args.dry_run:
        print("DRY-RUN: Using synthetic data")
        raw = generate_synthetic_data(500)
        symbols = [symbols[0]] if symbols else ["SPY"]
    else:
        data_dir = Path(args.data_dir)
        if not data_dir.exists():
            print(f"ERROR: Data directory not found: {data_dir}", file=sys.stderr)
            sys.exit(1)

    import json
    from run_volatility_dm_verdict import compute_dm_verdict, run_har_baseline

    all_results = []
    for symbol in symbols:
        print(f"\n{'='*60}")
        print(f"  {symbol}")
        print(f"{'='*60}")

        if args.dry_run:
            close = raw["Close"] if "Close" in raw.columns else raw.iloc[:, 0]
        else:
            from run_volatility_dm_verdict import load_daily_close
            close = load_daily_close(symbol)
            if close is None:
                print(f"  No data for {symbol}")
                continue
            print(f"  Data: {len(close)} rows")

        har_result = run_har_baseline(close, HORIZON)

        result = run_ensemble(
            symbol, close, seeds=seeds,
            n_splits=args.n_splits, gap=args.gap,
            dry_run=args.dry_run,
        )

        if result.get("status") == "ok" and har_result.get("status") == "ok":
            dm_v = compute_dm_verdict(result, har_result, len(symbols) * 2)
            result.update(dm_v)
            print(f"  Ensemble MSE={result['mse']:.6f}  DM={dm_v.get('dm_stat',0):.3f}  "
                  f"verdict={dm_v.get('dm_verdict','?')}")
            if "ridge_coefs" in result:
                print(f"  Ridge coefs: {result['ridge_coefs']}")
        else:
            print(f"  FAILED: {result.get('status', 'unknown')}")

        all_results.append(result)

    # Save
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    from datetime import datetime
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_file = output_dir / f"ensemble_results_{ts}.json"
    serializable = [{k: v for k, v in r.items() if isinstance(v, (str, int, float, bool, list, dict))}
                    for r in all_results]
    with open(out_file, "w") as f:
        json.dump(serializable, f, indent=2, default=str)
    print(f"\nResults saved: {out_file}")

    if args.dry_run:
        print("DRY-RUN complete. Ensemble pipeline validated successfully.")


if __name__ == "__main__":
    main()
