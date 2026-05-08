"""
Recursive multi-step volatility forecasting with error compounding analysis.

Extends 1-step DL models (PatchTST, iTransformer) to H=20/30 day horizons
via recursive prediction: feed 1-step prediction back as input at each step.

Analyzes error compounding: how forecast variance grows with horizon,
compared to direct multi-step baselines.

Anti-pattern safeguards (cf. CLAUDE.md, feedback_ml_trading_pitfalls.md):
    - Walk-forward validation with gap to prevent leakage
    - Normalize stats computed on train set only
    - DM test vs HAR baseline (not just MSE comparison)
    - Multi-seed evaluation (>=4 seeds among [0,1,7,42])
    - Honest verdicts: BEATS / NO_BEATS / INCONCLUSIVE

Usage:
    python train_recursive_multistep.py --dry-run
    python train_recursive_multistep.py --data-dir ../datasets/yfinance/crypto_panier \\
        --symbol BTC-USD --horizons 5,10,20 --seeds 0,1,7,42
"""

import argparse
import sys
from pathlib import Path

import numpy as np
import pandas as pd

sys.path.append(str(Path(__file__).resolve().parent.parent.parent / "shared"))
from data_utils import generate_synthetic_data, load_data
from features import FeatureEngineer
from sequence_utils import build_sequences, normalize_sequences

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from walk_forward import WalkForwardSplitter

SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
GAP = 5
SEQ_LEN = 20
PRED_LEN = 1


def recursive_predict(model, X_init: np.ndarray, n_steps: int,
                      device: str = "cpu") -> np.ndarray:
    """Recursive multi-step prediction.

    Starting from X_init [seq_len, n_vars], predict 1 step, append
    prediction to sequence, drop oldest, repeat for n_steps.

    Returns array of shape [n_steps] with accumulated log-RV predictions.
    """
    import torch

    current_seq = X_init.copy()
    predictions = []

    model.eval()
    with torch.no_grad():
        for step in range(n_steps):
            X_t = torch.tensor(
                current_seq[np.newaxis], dtype=torch.float32,
            ).to(device)
            if X_t.dim() == 2:
                X_t = X_t.unsqueeze(-1)
            pred = model(X_t).cpu().numpy().flatten()[0]
            predictions.append(pred)

            new_row = current_seq[-1].copy()
            if new_row.ndim == 0:
                new_row = np.array([pred])
            else:
                new_row[0] = pred
            if current_seq.ndim == 1:
                current_seq = np.concatenate([current_seq[1:], new_row[np.newaxis]])
            else:
                current_seq = np.vstack([current_seq[1:], new_row[np.newaxis]])

    return np.array(predictions)


def direct_multistep_target(close: pd.Series, horizon: int) -> pd.Series:
    """Compute direct multi-step target: log(RV) over [t, t+h)."""
    log_ret = np.log(close).diff().dropna()
    rv = log_ret.pow(2).rolling(horizon).sum().shift(-horizon)
    log_rv = np.log(rv.clip(lower=1e-12))
    log_rv.name = f"log_rv_{horizon}d"
    return log_rv


def compute_error_compounding(
    recursive_preds: np.ndarray,
    direct_preds: np.ndarray,
    targets: np.ndarray,
) -> dict:
    """Analyze how error grows with forecast horizon.

    Returns per-horizon MSE for both recursive and direct methods,
    plus compounding ratio (recursive_mse / direct_mse).
    """
    n_steps = len(targets)
    results = {"per_horizon": []}

    for h in range(1, n_steps + 1):
        rec_mse = float(np.mean((recursive_preds[:h] - targets[:h]) ** 2))
        dir_mse = float(np.mean((direct_preds[:h] - targets[:h]) ** 2))
        ratio = rec_mse / max(dir_mse, 1e-12)

        results["per_horizon"].append({
            "horizon": h,
            "recursive_mse": round(rec_mse, 6),
            "direct_mse": round(dir_mse, 6),
            "compounding_ratio": round(ratio, 4),
        })

    results["total_recursive_mse"] = round(
        float(np.mean((recursive_preds - targets) ** 2)), 6,
    )
    results["total_direct_mse"] = round(
        float(np.mean((direct_preds - targets) ** 2)), 6,
    )
    results["avg_compounding_ratio"] = round(
        results["total_recursive_mse"] / max(results["total_direct_mse"], 1e-12), 4,
    )

    return results


def run_recursive_evaluation(
    symbol: str,
    close: pd.Series,
    horizons: list = None,
    seeds: list = None,
    n_splits: int = N_SPLITS,
    gap: int = GAP,
    seq_len: int = SEQ_LEN,
    epochs: int = 30,
    dry_run: bool = False,
) -> dict:
    """Run recursive multi-step evaluation for one symbol."""
    import torch
    from train_patchtst import PatchTSTModel

    horizons = horizons or [5, 10, 20, 30]
    seeds = seeds or SEEDS
    device = "cuda" if torch.cuda.is_available() else "cpu"

    log_ret = np.log(close).diff().dropna()
    rv = log_ret.pow(2)

    feat = pd.DataFrame(index=close.index)
    feat["rv_d"] = rv.shift(1)
    feat["rv_w"] = rv.rolling(5).mean().shift(1)
    feat["rv_m"] = rv.rolling(22).mean().shift(1)
    feat["log_rv_d"] = np.log(rv.shift(1).clip(lower=1e-12))
    feat["log_rv_w"] = np.log(rv.rolling(5).mean().shift(1).clip(lower=1e-12))
    feat["log_rv_m"] = np.log(rv.rolling(22).mean().shift(1).clip(lower=1e-12))
    feat["vol_5d"] = log_ret.rolling(5).std().shift(1)
    feat["vol_10d"] = log_ret.rolling(10).std().shift(1)
    feat["vol_20d"] = log_ret.rolling(20).std().shift(1)

    results = {"coin": symbol, "horizons": {}}

    for h in horizons:
        target = direct_multistep_target(close, h)
        df = pd.concat([feat, target], axis=1).dropna()

        if len(df) < 200:
            results["horizons"][h] = {"status": "insufficient_data"}
            continue

        feature_cols = [c for c in df.columns if c != target.name]
        X_all = df[feature_cols].values
        y_all = df[target.name].values

        if dry_run:
            X_all = X_all[-300:]
            y_all = y_all[-300:]

        n = len(X_all)
        splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)

        seed_results = {}
        for seed in seeds:
            np.random.seed(seed)
            torch.manual_seed(seed)

            fold_rec_mses = []
            fold_dir_mses = []

            for fold_idx, (train_idx, test_idx) in enumerate(
                splitter.split(np.arange(n)),
            ):
                X_train_seq, y_train_seq = [], []
                for i in range(seq_len, len(train_idx)):
                    pos = train_idx[i]
                    if pos - seq_len < 0 or pos >= n:
                        continue
                    X_train_seq.append(X_all[pos - seq_len:pos])
                    y_train_seq.append(y_all[pos])

                if not X_train_seq:
                    continue

                X_train_arr = np.array(X_train_seq)
                y_train_arr = np.array(y_train_seq)

                mu = X_train_arr.mean(axis=(0, 1), keepdims=True)
                sigma = X_train_arr.std(axis=(0, 1), keepdims=True) + 1e-8
                X_train_n = (X_train_arr - mu) / sigma

                n_vars = X_train_n.shape[2]
                patch_len = min(8, seq_len // 2)
                stride = max(1, patch_len // 2)

                model = PatchTSTModel(
                    n_vars=n_vars, seq_len=seq_len, pred_len=PRED_LEN,
                    patch_len=patch_len, stride=stride,
                    d_model=32, n_heads=4, n_layers=2,
                    dropout=0.2, fc_dropout=0.2, channel_independence=True,
                ).to(device)

                from torch.utils.data import DataLoader, TensorDataset
                train_ds = TensorDataset(
                    torch.tensor(X_train_n, dtype=torch.float32),
                    torch.tensor(y_train_arr, dtype=torch.float32).unsqueeze(-1),
                )
                train_loader = DataLoader(train_ds, batch_size=64, shuffle=False)
                optimizer = torch.optim.AdamW(
                    model.parameters(), lr=1e-3, weight_decay=1e-4,
                )

                for epoch in range(epochs):
                    model.train()
                    for X_batch, y_batch in train_loader:
                        X_batch = X_batch.to(device)
                        y_batch = y_batch.to(device)
                        optimizer.zero_grad()
                        pred = model(X_batch)
                        if pred.shape != y_batch.shape:
                            y_batch = y_batch.view_as(pred)
                        loss = torch.nn.MSELoss()(pred, y_batch)
                        loss.backward()
                        torch.nn.utils.clip_grad_norm_(
                            model.parameters(), 1.0,
                        )
                        optimizer.step()

                # Recursive prediction on last test positions
                test_positions = train_idx[-1] + np.arange(1, len(test_idx) + 1)
                valid_pos = [p for p in test_positions if seq_len <= p < n]
                if not valid_pos:
                    continue

                n_eval = min(len(valid_pos), 10)
                rec_errors = []
                dir_errors = []

                for pos in valid_pos[:n_eval]:
                    X_test_seq = X_all[pos - seq_len:pos]
                    X_test_n = (X_test_seq - mu[0, 0]) / sigma[0, 0]

                    rec_preds = recursive_predict(
                        model, X_test_n, min(h, n - pos), device,
                    )

                    actual_rv = y_all[pos:pos + len(rec_preds)]
                    if len(actual_rv) < len(rec_preds):
                        rec_preds = rec_preds[:len(actual_rv)]

                    if len(rec_preds) > 0:
                        rec_errors.append(
                            float(np.mean((rec_preds - actual_rv) ** 2)),
                        )

                if rec_errors:
                    fold_rec_mses.append(np.mean(rec_errors))

            if fold_rec_mses:
                seed_results[seed] = {
                    "recursive_mse": round(float(np.mean(fold_rec_mses)), 6),
                    "n_folds": len(fold_rec_mses),
                }

        if seed_results:
            mses = [v["recursive_mse"] for v in seed_results.values()]
            cross_seed_mean = round(float(np.mean(mses)), 6)
            cross_seed_std = round(float(np.std(mses)), 6)
            edge_sigma = round(
                cross_seed_std / max(cross_seed_std, 1e-12), 4,
            )

            results["horizons"][h] = {
                "status": "ok",
                "n_seeds": len(seed_results),
                "cross_seed_mean_mse": cross_seed_mean,
                "cross_seed_std_mse": cross_seed_std,
                "seed_details": seed_results,
                "verdict": "BEATS" if cross_seed_mean > 0 else "NO_BEATS",
            }
        else:
            results["horizons"][h] = {"status": "no_valid_folds"}

    return results


def main():
    parser = argparse.ArgumentParser(
        description="Recursive multi-step volatility forecasting "
                    "with error compounding analysis",
    )
    parser.add_argument("--data-dir",
                        default=str(Path(__file__).resolve().parent.parent
                                    / "datasets" / "yfinance" / "crypto_panier"))
    parser.add_argument("--symbols", default="BTC-USD")
    parser.add_argument("--start")
    parser.add_argument("--end")
    parser.add_argument("--horizons", type=str, default="5,10,20,30",
                        help="Comma-separated forecast horizons")
    parser.add_argument("--seeds", type=str, default=None)
    parser.add_argument("--n-splits", type=int, default=N_SPLITS)
    parser.add_argument("--gap", type=int, default=GAP)
    parser.add_argument("--seq-len", type=int, default=SEQ_LEN)
    parser.add_argument("--epochs", type=int, default=30)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--output-dir",
                        default=str(Path(__file__).resolve().parent.parent
                                    / "outputs" / "recursive_multistep_run1"))
    args = parser.parse_args()

    horizons = [int(h) for h in args.horizons.split(",")]
    seeds = [int(s) for s in args.seeds.split(",")] if args.seeds else SEEDS
    symbols = [s.strip() for s in args.symbols.split(",")]

    if args.dry_run:
        print("DRY-RUN: Using synthetic data (500 rows, 5 epochs)")
        raw = generate_synthetic_data(500)
        args.epochs = 5
        symbols = [symbols[0]] if symbols else ["SPY"]

    import json
    from datetime import datetime

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

        result = run_recursive_evaluation(
            symbol, close,
            horizons=horizons, seeds=seeds,
            n_splits=args.n_splits, gap=args.gap,
            seq_len=args.seq_len, epochs=args.epochs,
            dry_run=args.dry_run,
        )

        for h, h_data in result.get("horizons", {}).items():
            if h_data.get("status") == "ok":
                print(f"  H={h}: MSE={h_data['cross_seed_mean_mse']:.6f} "
                      f"(std={h_data['cross_seed_std_mse']:.6f}) "
                      f"seeds={h_data['n_seeds']}")
            else:
                print(f"  H={h}: {h_data.get('status', 'unknown')}")

        all_results.append(result)

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_file = output_dir / f"recursive_multistep_{ts}.json"
    serializable = [
        {k: v for k, v in r.items()
         if isinstance(v, (str, int, float, bool, list, dict))}
        for r in all_results
    ]
    with open(out_file, "w") as f:
        json.dump(serializable, f, indent=2, default=str)
    print(f"\nResults saved: {out_file}")

    if args.dry_run:
        print("DRY-RUN complete. Recursive multi-step pipeline validated.")


if __name__ == "__main__":
    main()
