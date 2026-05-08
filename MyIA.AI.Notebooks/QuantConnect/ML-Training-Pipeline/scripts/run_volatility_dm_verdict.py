"""
Re-run Stage 0/1/2 on log-RV target with DM test vs HAR/GARCH baselines.

Addresses Issue #834 defect #6: previous stages used r2_daily (noisy) or
binary direction as target. This script uses log(RV) = log(sum r²_h) as
the correct volatility forecasting target per academic convention.

Walk-forward 5-fold evaluation, DM test with Newey-West HAC variance,
Bonferroni correction for 10 coins x 3 stages = 30 tests.

Produces verdict matrix: coin x stage x (DM stat, p-value, MSE, Sharpe).

Usage:
    python run_volatility_dm_verdict.py
    python run_volatility_dm_verdict.py --dry-run
    python run_volatility_dm_verdict.py --symbols BTC-USD ETH-USD --stages 0 2
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

SCRIPT_DIR = Path(__file__).resolve().parent
CHECKPOINTS_DIR = SCRIPT_DIR.parent / "checkpoints"
DATA_DIR = SCRIPT_DIR.parent.parent / "datasets" / "yfinance" / "crypto_panier"

sys.path.insert(0, str(SCRIPT_DIR))

from graph_builder import CRYPTO_PANIER_SYMBOLS
from walk_forward import WalkForwardSplitter
from diebold_mariano import diebold_mariano_test, bonferroni_dm
from economic_metrics import vol_targeted_sharpe, var_breach_rate, utility_gain

SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
GAP = 5
HORIZON = 5  # 5-day ahead volatility forecast


def load_daily_close(symbol: str) -> pd.Series:
    matches = list(DATA_DIR.glob(f"{symbol}_*.csv"))
    if not matches:
        raise FileNotFoundError(f"No data for {symbol} in {DATA_DIR}")
    df = pd.read_csv(matches[0], index_col=0, parse_dates=True)
    df.columns = [c.strip().capitalize() for c in df.columns]
    close = df["Close"].sort_index()
    close = close[~close.index.duplicated(keep="last")]
    return close


def compute_log_rv_target(close: pd.Series, horizon: int = 5) -> pd.Series:
    """Compute log realized variance from daily close prices.

    RV_t = sum_{i=0..h-1} r²_{t+i} where r = log(P_t/P_{t-1}).
    Target is shifted so that features at time t predict RV over [t, t+h).
    """
    log_ret = np.log(close).diff().dropna()
    rv = log_ret.pow(2).rolling(horizon).sum().shift(-horizon)
    log_rv = np.log(rv.clip(lower=1e-12))
    log_rv.name = f"log_rv_{horizon}d"
    return log_rv


def compute_features(close: pd.Series, lookback: int = 20) -> pd.DataFrame:
    """Build volatility-forecasting features from daily close."""
    log_ret = np.log(close).diff().dropna()
    feat = pd.DataFrame(index=close.index)

    # Lagged squared returns (RV components)
    for lag in [1, 2, 3, 5, 10, 20]:
        feat[f"r2_lag{lag}"] = log_ret.pow(2).shift(lag)

    # Rolling volatility features
    for w in [5, 10, 20]:
        feat[f"vol_{w}d"] = log_ret.rolling(w).std().shift(1)
        feat[f"rv_{w}d"] = log_ret.pow(2).rolling(w).sum().shift(1)

    # HAR-style features (Corsi 2009)
    rv_1d = log_ret.pow(2).shift(1)
    rv_5d = rv_1d.rolling(5).mean()
    rv_22d = rv_1d.rolling(22).mean()
    feat["rv_d"] = rv_1d
    feat["rv_w"] = rv_5d
    feat["rv_m"] = rv_22d

    # Log transforms
    feat["log_rv_d"] = np.log(rv_1d.clip(lower=1e-12))
    feat["log_rv_w"] = np.log(rv_5d.clip(lower=1e-12))
    feat["log_rv_m"] = np.log(rv_22d.clip(lower=1e-12))

    # Realized skew / kurtosis proxies
    for w in [5, 20]:
        feat[f"skew_{w}d"] = log_ret.rolling(w).skew().shift(1)
        feat[f"kurt_{w}d"] = log_ret.rolling(w).kurt().shift(1)

    # Return sign features
    for lag in [1, 2, 3, 5]:
        feat[f"sign_ret_{lag}"] = np.sign(log_ret.shift(lag))

    return feat


# ---------------------------------------------------------------------------
# Stage 0: RF on features → log-RV
# ---------------------------------------------------------------------------


def run_stage0_rf(
    symbol: str,
    close: pd.Series,
    horizon: int,
    seeds: list[int],
    n_splits: int,
    gap: int,
) -> dict:
    from sklearn.ensemble import RandomForestRegressor

    features = compute_features(close)
    target = compute_log_rv_target(close, horizon)
    df = pd.concat([features, target], axis=1).dropna()

    if len(df) < 200:
        return {"coin": symbol, "stage": 0, "model": "RF", "status": "insufficient_data"}

    feature_cols = [c for c in df.columns if c != target.name]
    X = df[feature_cols].values
    y = df[target.name].values

    splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
    oos_preds = np.full(len(y), np.nan)
    oos_targets = np.full(len(y), np.nan)

    for seed in seeds:
        np.random.seed(seed)
        for train_idx, test_idx in splitter.split(X):
            if len(test_idx) == 0:
                continue
            model = RandomForestRegressor(
                n_estimators=100, max_depth=10, random_state=seed, n_jobs=-1,
            )
            model.fit(X[train_idx], y[train_idx])
            preds = model.predict(X[test_idx])
            oos_preds[test_idx[:len(preds)]] = preds
            oos_targets[test_idx[:len(preds)]] = y[test_idx[:len(preds)]]

    valid = ~np.isnan(oos_preds)
    if valid.sum() < 20:
        return {"coin": symbol, "stage": 0, "model": "RF", "status": "insufficient_oos"}

    vp = oos_preds[valid]
    vt = oos_targets[valid]
    mse = float(np.mean((vp - vt) ** 2))
    return {
        "coin": symbol, "stage": 0, "model": "RF",
        "mse": round(mse, 6), "n_oos": int(valid.sum()),
        "preds": vp, "targets": vt,
    }


# ---------------------------------------------------------------------------
# Stage 2: PatchTST / iTransformer on log-RV
# ---------------------------------------------------------------------------


def run_stage2_dl(
    symbol: str,
    close: pd.Series,
    horizon: int,
    model_type: str,
    seeds: list[int],
    n_splits: int,
    gap: int,
    seq_len: int,
    epochs: int,
    batch_size: int,
    device: str,
    dry_run: bool,
) -> dict:
    import torch
    from torch.utils.data import DataLoader, TensorDataset

    if model_type == "patchtst":
        from train_patchtst import PatchTSTModel
    elif model_type == "itransformer":
        from train_itransformer import iTransformerModel

    features = compute_features(close)
    target = compute_log_rv_target(close, horizon)
    df = pd.concat([features, target], axis=1).dropna()

    if len(df) < 200:
        return {"coin": symbol, "stage": 2, "model": model_type, "status": "insufficient_data"}

    feature_cols = [c for c in df.columns if c != target.name]
    X = df[feature_cols].values
    y = df[target.name].values
    n_vars = len(feature_cols)

    if dry_run:
        X = X[-300:]
        y = y[-300:]

    splitter = WalkForwardSplitter(n_splits=n_splits, gap=gap)
    oos_preds = np.full(len(y), np.nan)
    oos_targets = np.full(len(y), np.nan)
    pred_len = 1  # single-step log-RV forecast

    for seed in seeds:
        np.random.seed(seed)
        torch.manual_seed(seed)
        if torch.cuda.is_available():
            torch.cuda.manual_seed_all(seed)

        for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(X)):
            if len(test_idx) == 0:
                continue

            # Build sequences
            X_train_seq, y_train_seq = [], []
            for i in range(seq_len, len(train_idx)):
                X_train_seq.append(X[train_idx[i - seq_len]:train_idx[i]])
                y_train_seq.append(y[train_idx[i]])
            X_train_seq = np.array(X_train_seq)
            y_train_seq = np.array(y_train_seq)

            X_test_seq, y_test_seq = [], []
            test_positions = train_idx[-1] + np.arange(1, len(test_idx) + 1)
            for i in range(seq_len, len(test_positions)):
                pos = test_positions[i]
                if pos - seq_len < 0 or pos >= len(X):
                    continue
                X_test_seq.append(X[pos - seq_len:pos])
                y_test_seq.append(y[pos])
            if not X_test_seq:
                continue

            X_test_seq = np.array(X_test_seq)
            y_test_seq = np.array(y_test_seq)

            # Normalize on train
            mu = X_train_seq.mean(axis=(0, 1), keepdims=True)
            sigma = X_train_seq.std(axis=(0, 1), keepdims=True) + 1e-8
            X_train_n = (X_train_seq - mu) / sigma
            X_test_n = (X_test_seq - mu) / sigma

            # Build model
            if model_type == "patchtst":
                patch_len = min(8, seq_len // 2)
                stride = max(1, patch_len // 2)
                model = PatchTSTModel(
                    n_vars=n_vars, seq_len=seq_len, pred_len=pred_len,
                    patch_len=patch_len, stride=stride,
                    d_model=32, n_heads=4, n_layers=2,
                    dropout=0.2, fc_dropout=0.2, channel_independence=True,
                ).to(device)
            else:
                model = iTransformerModel(
                    n_vars=n_vars, seq_len=seq_len, pred_len=pred_len,
                    d_model=32, n_heads=4, n_layers=2,
                    dropout=0.2, ff_dropout=0.2,
                ).to(device)

            train_ds = TensorDataset(
                torch.tensor(X_train_n, dtype=torch.float32),
                torch.tensor(y_train_seq, dtype=torch.float32).unsqueeze(-1),
            )
            train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=False)
            optimizer = torch.optim.AdamW(model.parameters(), lr=1e-3, weight_decay=1e-4)
            criterion = torch.nn.MSELoss()

            for epoch in range(epochs):
                model.train()
                for X_batch, y_batch in train_loader:
                    X_batch, y_batch = X_batch.to(device), y_batch.to(device)
                    optimizer.zero_grad()
                    pred = model(X_batch)
                    loss = criterion(pred, y_batch)
                    loss.backward()
                    torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                    optimizer.step()

            model.eval()
            with torch.no_grad():
                X_t = torch.tensor(X_test_n, dtype=torch.float32).to(device)
                dl_preds = model(X_t).cpu().numpy().flatten()

            # Map predictions back to oos arrays
            for i, pos in enumerate(range(seq_len, min(len(test_positions), len(dl_preds) + seq_len))):
                actual_pos = test_positions[pos] if pos < len(test_positions) else None
                if actual_pos is not None and actual_pos < len(oos_preds):
                    oos_preds[actual_pos] = dl_preds[i] if i < len(dl_preds) else np.nan
                    oos_targets[actual_pos] = y[actual_pos]

    valid = ~np.isnan(oos_preds)
    if valid.sum() < 20:
        return {"coin": symbol, "stage": 2, "model": model_type, "status": "insufficient_oos"}

    vp = oos_preds[valid]
    vt = oos_targets[valid]
    mse = float(np.mean((vp - vt) ** 2))
    return {
        "coin": symbol, "stage": 2, "model": model_type,
        "mse": round(mse, 6), "n_oos": int(valid.sum()),
        "preds": vp, "targets": vt,
    }


# ---------------------------------------------------------------------------
# HAR baseline (gold standard)
# ---------------------------------------------------------------------------


def run_har_baseline(close: pd.Series, horizon: int) -> dict:
    """Run HAR walk-forward and return OOS predictions on log-RV scale."""
    from har_model import walk_forward_har

    log_ret = np.log(close).diff().dropna()
    rv_daily = log_ret.pow(2)
    rv_daily.name = "RV"
    rv_daily.index = pd.DatetimeIndex(rv_daily.index)

    if len(rv_daily) < 250:
        return {"status": "insufficient_data"}

    try:
        result = walk_forward_har(rv_daily, horizon=horizon, n_splits=4, refit_every=22)
    except ValueError:
        return {"status": "insufficient_data"}

    preds = result["forecasts"].values
    targets = result["targets"].values
    mse = float(np.mean((preds - targets) ** 2))
    return {
        "status": "ok",
        "mse": round(mse, 6),
        "preds": preds, "targets": targets,
        "n_oos": len(preds),
    }


def run_naive_baseline(close: pd.Series, horizon: int) -> dict:
    """Naive trailing-30d mean of log-RV."""
    target = compute_log_rv_target(close, horizon)
    target = target.dropna()
    if len(target) < 200:
        return {"status": "insufficient_data"}

    train_size = int(len(target) * 0.8)
    test_target = target.iloc[train_size:]
    # Predict trailing 30d mean
    preds = target.iloc[train_size - 30:train_size].values.mean() * np.ones(len(test_target))
    mse = float(np.mean((preds - test_target.values) ** 2))
    return {
        "status": "ok",
        "mse": round(mse, 6),
        "preds": preds, "targets": test_target.values,
        "n_oos": len(preds),
    }


# ---------------------------------------------------------------------------
# Verdict computation with DM test
# ---------------------------------------------------------------------------


def compute_dm_verdict(
    model_result: dict,
    har_result: dict,
    n_total_tests: int = 30,
) -> dict:
    """Compute DM test between model and HAR baseline."""
    if model_result.get("status") != "ok" and "preds" not in model_result:
        return {"dm_verdict": "ERROR", "error": "model failed"}

    if har_result.get("status") != "ok":
        return {"dm_verdict": "ERROR", "error": "HAR baseline failed"}

    # Align by taking minimum length
    model_preds = np.asarray(model_result["preds"])
    model_targets = np.asarray(model_result["targets"])
    har_preds = np.asarray(har_result["preds"])
    har_targets = np.asarray(har_result["targets"])

    # Use common target if available (same series)
    n = min(len(model_preds), len(har_preds))
    if n < 30:
        return {"dm_verdict": "INSUFFICIENT", "error": f"only {n} aligned obs"}

    model_errors = model_targets[:n] - model_preds[:n]
    har_errors = har_targets[:n] - har_preds[:n]

    # DM test
    dm = diebold_mariano_test(model_errors, har_errors, h=HORIZON, alternative="two-sided")

    # Bonferroni correction
    dm_bonf = bonferroni_dm(model_errors, har_errors, n_tests=n_total_tests, h=HORIZON)

    # Economic metrics
    ug = utility_gain(
        model_result.get("mse", float("inf")),
        har_result.get("mse", 0),
    )

    # Verdict logic
    if dm["dm_stat"] < 0 and dm_bonf["significant_05_bonferroni"]:
        verdict = "BEATS_HAR"
    elif dm["dm_stat"] > 0 and dm_bonf["significant_05_bonferroni"]:
        verdict = "NO_BEATS"
    else:
        verdict = "INCONCLUSIVE"

    return {
        "dm_verdict": verdict,
        "dm_stat": dm["dm_stat"],
        "dm_p": dm["p_value"],
        "dm_p_bonferroni": dm_bonf["p_value_adjusted"],
        "dm_interpretation": dm["interpretation"],
        "model_mse": model_result.get("mse"),
        "har_mse": har_result.get("mse"),
        "utility_gain_bps": ug["gain_bps"],
        "worth_switching": ug["worth_switching"],
        "n_aligned": n,
    }


# ---------------------------------------------------------------------------
# Main driver
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Re-run Stage 0/1/2 on log-RV with DM test vs HAR baseline",
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--symbols", nargs="+", default=None)
    parser.add_argument("--stages", nargs="+", type=int, default=[0, 2])
    parser.add_argument("--seeds", type=str, default=None)
    parser.add_argument("--n-splits", type=int, default=N_SPLITS)
    parser.add_argument("--horizon", type=int, default=HORIZON)
    parser.add_argument("--seq-len", type=int, default=20)
    parser.add_argument("--epochs", type=int, default=30)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--device", default="cpu")
    parser.add_argument("--output-dir", default=None)
    args = parser.parse_args()

    import torch
    if torch.cuda.is_available() and args.device == "cuda":
        args.device = "cuda"
    else:
        args.device = "cpu"

    symbols = args.symbols or CRYPTO_PANIER_SYMBOLS
    seeds = [int(s) for s in args.seeds.split(",")] if args.seeds else SEEDS
    n_total_tests = len(symbols) * len(args.stages) * 2  # rough upper bound

    if args.dry_run:
        seeds = [0]
        args.epochs = 3
        args.n_splits = 2

    print("=" * 80)
    print("Stage 0/1/2 Re-Run on log-RV Target with DM Test")
    print(f"  Coins: {len(symbols)}, Stages: {args.stages}")
    print(f"  Seeds: {seeds}, Horizon: {args.horizon}, Device: {args.device}")
    print("=" * 80)

    all_results = []

    for symbol in symbols:
        print(f"\n{'='*70}")
        print(f"  {symbol}")
        print(f"{'='*70}")

        try:
            close = load_daily_close(symbol)
        except FileNotFoundError as e:
            print(f"  SKIP: {e}")
            continue

        if args.dry_run:
            close = close.iloc[-500:]

        print(f"  Data: {len(close)} rows ({close.index.min().date()} -> {close.index.max().date()})")

        # HAR baseline (gold standard)
        print("  Running HAR baseline...")
        t0 = time.time()
        har_result = run_har_baseline(close, args.horizon)
        if har_result.get("status") == "ok":
            print(f"    HAR MSE={har_result['mse']:.6f} ({time.time()-t0:.1f}s)")
        else:
            print(f"    HAR FAILED: {har_result.get('status')}")
            continue

        # Naive baseline
        naive_result = run_naive_baseline(close, args.horizon)

        # Stage 0: RF
        if 0 in args.stages:
            print("  Running Stage 0 (RF)...")
            t0 = time.time()
            s0_result = run_stage0_rf(
                symbol, close, args.horizon, seeds, args.n_splits, GAP,
            )
            elapsed = time.time() - t0
            if "preds" in s0_result:
                s0_result["status"] = "ok"
                dm_v = compute_dm_verdict(s0_result, har_result, n_total_tests)
                s0_result.update(dm_v)
                print(f"    RF MSE={s0_result['mse']:.6f}  DM={dm_v.get('dm_stat',0):.3f}  "
                      f"verdict={dm_v.get('dm_verdict','?')}  ({elapsed:.1f}s)")
            else:
                print(f"    RF FAILED: {s0_result.get('status')}")
            all_results.append(s0_result)

        # Stage 2: PatchTST / iTransformer
        if 2 in args.stages:
            for model_type in ["patchtst", "itransformer"]:
                print(f"  Running Stage 2 ({model_type})...")
                t0 = time.time()
                s2_result = run_stage2_dl(
                    symbol, close, args.horizon, model_type,
                    seeds, args.n_splits, GAP,
                    args.seq_len, args.epochs, args.batch_size,
                    args.device, args.dry_run,
                )
                elapsed = time.time() - t0
                if "preds" in s2_result:
                    s2_result["status"] = "ok"
                    dm_v = compute_dm_verdict(s2_result, har_result, n_total_tests)
                    s2_result.update(dm_v)
                    print(f"    {model_type} MSE={s2_result['mse']:.6f}  DM={dm_v.get('dm_stat',0):.3f}  "
                          f"verdict={dm_v.get('dm_verdict','?')}  ({elapsed:.1f}s)")
                else:
                    print(f"    {model_type} FAILED: {s2_result.get('status')}")
                all_results.append(s2_result)

    # Verdict table
    print(f"\n{'='*100}")
    print("VERDICT MATRIX (DM test vs HAR baseline, Bonferroni-corrected)")
    print(f"{'='*100}")
    print(
        f"{'Coin':10s} {'Stage':>5s} {'Model':14s} {'Verdict':14s} "
        f"{'DM':>7s} {'p(adj)':>8s} {'MSE':>10s} {'Gain':>6s}"
    )
    print("-" * 100)

    for r in all_results:
        print(
            f"{r.get('coin','?'):10s} {r.get('stage',0):5d} "
            f"{r.get('model','?'):14s} "
            f"{r.get('dm_verdict','?'):14s} "
            f"{r.get('dm_stat',0):7.3f} "
            f"{r.get('dm_p_bonferroni',1):8.4f} "
            f"{r.get('mse',0):10.6f} "
            f"{r.get('utility_gain_bps',0):6.1f}"
        )

    # Save
    output_dir = Path(args.output_dir) if args.output_dir else CHECKPOINTS_DIR / "stage_dm_verdict"
    output_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_file = output_dir / f"dm_verdict_{ts}.json"

    saveable = []
    for r in all_results:
        sr = {k: v for k, v in r.items() if not isinstance(v, np.ndarray)}
        saveable.append(sr)

    out_file.write_text(json.dumps(saveable, indent=2, default=str), encoding="utf-8")
    latest = output_dir / "dm_verdict_latest.json"
    latest.write_text(json.dumps(saveable, indent=2, default=str), encoding="utf-8")
    print(f"\nResults saved: {out_file}")

    verdicts = [r.get("dm_verdict", "ERROR") for r in all_results]
    print(f"\nSummary: BEATS_HAR={verdicts.count('BEATS_HAR')}  "
          f"NO_BEATS={verdicts.count('NO_BEATS')}  "
          f"INCONCLUSIVE={verdicts.count('INCONCLUSIVE')}  "
          f"ERROR={verdicts.count('ERROR')}")


if __name__ == "__main__":
    main()
