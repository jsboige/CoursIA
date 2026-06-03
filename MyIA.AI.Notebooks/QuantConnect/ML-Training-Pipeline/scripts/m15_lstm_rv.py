"""M15 Log-LSTM RV -- Neural volatility forecasting on log-realized variance.

Question
--------
Does a small LSTM neural network beat HAR Classic for crypto volatility forecasting?

Architecture:
    Input:  sliding window W=22 days of [log(RV), returns, sign(returns)] -> (W, 3)
    Model:  LSTM(hidden=64, 1 layer) + FC(64, 1)
    Target: log(RV_{t+h}) where h in {1, 5, 10}
    Loss:   MSE on log-RV
    Forecast: exp(pred) -> RV level, then log(RV) for Kelly comparison

Walk-forward 5-fold expanding, 7 coins x 3 horizons x 4 seeds = 84 combos.
Kelly cap=1.0, fee=50bps, sign-test paired Sharpe-diff vs HAR Classic baseline.

Param count: LSTM(3, 64) = 4*(64*64 + 64*3 + 64*4) = 17,408
             + FC(64, 1) = 65
             Total ~17.5K params.
Also tested hidden=32: 4*(32*32 + 32*3 + 32*4) = 4,640 + 33 = ~4.7K params.

Output
------
- results/m15_lstm_rv/results.json
- results/m15_lstm_rv/m15_lstm_rv_results.csv
- docs/M15_LSTM_RV.md (verdict)

Env: conda coursia-ml-training (Python 3.11, PyTorch 2.x + CUDA).
"""

from __future__ import annotations

import argparse
import json
import sys
import time
import warnings
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from har_model import HARModel, walk_forward_har  # noqa: E402
from intraday_loader import load_yf_intraday  # noqa: E402
from m11g_fee_aware_kelly import (  # noqa: E402
    _binomial_pvalue_one_sided,
    _kelly_weights_and_returns,
    _load_one_coin,
    _net_at_fee,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from realized_variance import (  # noqa: E402
    daily_realized_variance,
    realized_variance_to_log,
)

COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS = [1, 5, 10]
SEEDS = [0, 1, 7, 42]
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 50
N_SPLITS = 5
REFIT_EVERY = 22
RESULTS_DIR = SCRIPT_DIR / "results" / "m15_lstm_rv"

# LSTM hyperparams
WINDOW = 22
HIDDEN_SIZE = 64
NUM_LAYERS = 1
DROPOUT = 0.0
LEARNING_RATE = 1e-3
MAX_EPOCHS = 100
PATIENCE = 10
BATCH_SIZE = 32


# -- LSTM Model ---------------------------------------------------------------

def build_lstm(input_size: int = 3, hidden_size: int = HIDDEN_SIZE,
               num_layers: int = NUM_LAYERS):
    """Build a minimal LSTM model for log-RV forecasting."""
    import torch
    import torch.nn as nn

    class LSTMVolModel(nn.Module):
        def __init__(self, inp_sz, hid_sz, n_layers):
            super().__init__()
            self.lstm = nn.LSTM(inp_sz, hid_sz, n_layers, batch_first=True)
            self.fc = nn.Linear(hid_sz, 1)

        def forward(self, x):
            out, _ = self.lstm(x)
            return self.fc(out[:, -1, :])

    model = LSTMVolModel(input_size, hidden_size, num_layers)
    return model


def count_params(model) -> int:
    import torch
    return sum(p.numel() for p in model.parameters())


# -- Data preparation ---------------------------------------------------------

def prepare_features(hourly_rets: pd.Series) -> tuple[pd.DataFrame, pd.Series]:
    """Build [log_RV, returns, sign_returns] features aligned to daily RV.

    Returns (features_df, rv_series) both indexed by date.
    """
    rv = daily_realized_variance(hourly_rets)
    log_rv = np.log(rv.clip(lower=1e-12))

    daily_rets = hourly_rets.groupby(hourly_rets.index.normalize()).sum()
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    daily_rets = daily_rets.rename("returns")

    sign_rets = np.sign(daily_rets).rename("sign_returns")

    features = pd.concat([log_rv.rename("log_rv"), daily_rets, sign_rets], axis=1, sort=False)
    features = features.dropna()

    rv = rv.reindex(features.index)
    return features, rv


def make_sequences(features: np.ndarray, targets: np.ndarray,
                   window: int) -> tuple[np.ndarray, np.ndarray]:
    """Create (X, y) sequences for LSTM training.

    X shape: (N - window, window, n_features)
    y shape: (N - window,)
    """
    X, y = [], []
    for i in range(len(features) - window):
        X.append(features[i:i + window])
        y.append(targets[i + window])
    return np.array(X), np.array(y)


# -- Walk-forward LSTM --------------------------------------------------------

def walk_forward_lstm(
    features: pd.DataFrame,
    rv: pd.Series,
    horizon: int = 1,
    n_splits: int = N_SPLITS,
    refit_every: int = REFIT_EVERY,
    window: int = WINDOW,
    hidden_size: int = HIDDEN_SIZE,
    seed: int = 0,
) -> dict:
    """Walk-forward LSTM with expanding window."""
    import torch
    import torch.nn as nn

    torch.manual_seed(seed)
    np.random.seed(seed)

    log_rv = np.log(rv.clip(lower=1e-12))

    # Target: mean of log(RV) over next h days
    target = log_rv.rolling(horizon).mean().shift(-horizon)
    target = target.reindex(features.index)

    feat_vals = features.values
    target_vals = target.values
    n = len(feat_vals)

    fold_size = n // (n_splits + 1)
    if fold_size < 30:
        raise ValueError(f"n={n} too small for {n_splits} splits")

    splits = []
    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)
        splits.append((train_end, test_start, test_end))

    preds: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []
    fold_results: list[dict] = []

    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        # Build training sequences
        train_feat = feat_vals[:train_end]
        train_target = target_vals[:train_end]

        # Normalize features (expanding: fit on train, apply to test)
        feat_mean = np.nanmean(train_feat, axis=0)
        feat_std = np.nanstd(train_feat, axis=0) + 1e-8
        train_feat_norm = (train_feat - feat_mean) / feat_std

        X_train, y_train = make_sequences(train_feat_norm, train_target, window)
        if len(X_train) < 20:
            continue

        # Train LSTM
        model = build_lstm(
            input_size=X_train.shape[2],
            hidden_size=hidden_size,
        ).to(device)

        optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
        criterion = nn.MSELoss()

        X_t = torch.FloatTensor(X_train).to(device)
        y_t = torch.FloatTensor(y_train).unsqueeze(1).to(device)

        best_loss = float("inf")
        best_state = None
        no_improve = 0

        for epoch in range(MAX_EPOCHS):
            model.train()
            perm = torch.randperm(len(X_t))
            epoch_loss = 0.0
            n_batches = 0
            for start in range(0, len(perm), BATCH_SIZE):
                idx = perm[start:start + BATCH_SIZE]
                xb = X_t[idx]
                yb = y_t[idx]
                optimizer.zero_grad()
                pred = model(xb)
                loss = criterion(pred, yb)
                loss.backward()
                optimizer.step()
                epoch_loss += loss.item()
                n_batches += 1

            avg_loss = epoch_loss / max(n_batches, 1)
            if avg_loss < best_loss - 1e-6:
                best_loss = avg_loss
                best_state = {k: v.clone() for k, v in model.state_dict().items()}
                no_improve = 0
            else:
                no_improve += 1
            if no_improve >= PATIENCE:
                break

        if best_state is not None:
            model.load_state_dict(best_state)
        model.eval()

        # Evaluate on test set
        fold_preds: list[float] = []
        fold_truths: list[float] = []

        for i in range(test_start, test_end - horizon):
            if i < window:
                continue
            # Use all data up to i for normalization
            feat_so_far = feat_vals[:i]
            f_mean = np.nanmean(feat_so_far, axis=0)
            f_std = np.nanstd(feat_so_far, axis=0) + 1e-8

            seq = (feat_vals[i - window:i] - f_mean) / f_std
            seq_tensor = torch.FloatTensor(seq).unsqueeze(0).to(device)

            with torch.no_grad():
                pred_val = model(seq_tensor).item()
            true_val = target_vals[i]

            if np.isfinite(pred_val) and np.isfinite(true_val):
                fold_preds.append(pred_val)
                fold_truths.append(true_val)
                preds.append(pred_val)
                truths.append(true_val)
                pred_dates.append(features.index[i])

            # Refit periodically
            if (i - test_start) % refit_every == 0 and i > test_start:
                refit_feat = feat_vals[:i]
                refit_target = target_vals[:i]
                rf_mean = np.nanmean(refit_feat, axis=0)
                rf_std = np.nanstd(refit_feat, axis=0) + 1e-8
                refit_norm = (refit_feat - rf_mean) / rf_std
                X_rf, y_rf = make_sequences(refit_norm, refit_target, window)
                if len(X_rf) >= 20:
                    try:
                        model = build_lstm(
                            input_size=X_rf.shape[2],
                            hidden_size=hidden_size,
                        ).to(device)
                        optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
                        X_rf_t = torch.FloatTensor(X_rf).to(device)
                        y_rf_t = torch.FloatTensor(y_rf).unsqueeze(1).to(device)
                        best_rf_loss = float("inf")
                        best_rf_state = None
                        rf_no_improve = 0
                        for ep in range(MAX_EPOCHS):
                            model.train()
                            perm = torch.randperm(len(X_rf_t))
                            for start in range(0, len(perm), BATCH_SIZE):
                                idx = perm[start:start + BATCH_SIZE]
                                optimizer.zero_grad()
                                pred = model(X_rf_t[idx])
                                loss = criterion(pred, y_rf_t[idx])
                                loss.backward()
                                optimizer.step()
                            model.eval()
                            with torch.no_grad():
                                val_loss = criterion(model(X_rf_t), y_rf_t).item()
                            if val_loss < best_rf_loss - 1e-6:
                                best_rf_loss = val_loss
                                best_rf_state = {k: v.clone() for k, v in model.state_dict().items()}
                                rf_no_improve = 0
                            else:
                                rf_no_improve += 1
                            if rf_no_improve >= PATIENCE:
                                break
                        if best_rf_state:
                            model.load_state_dict(best_rf_state)
                        model.eval()
                    except Exception:
                        pass  # keep previous model

        fp = np.asarray(fold_preds)
        ft = np.asarray(fold_truths)
        fold_mse = float(np.mean((fp - ft) ** 2)) if len(fp) else float("nan")
        fold_results.append({
            "fold": fold_idx,
            "n_test": len(fp),
            "mse_logrv": fold_mse,
            "best_train_loss": best_loss,
            "epochs_trained": epoch + 1,
        })

    preds_arr = np.asarray(preds)
    truths_arr = np.asarray(truths)
    aggregate_mse = (
        float(np.mean((preds_arr - truths_arr) ** 2)) if len(preds_arr) else float("nan")
    )
    forecasts = pd.Series(
        preds_arr, index=pd.DatetimeIndex(pred_dates), name="lstm_logrv_pred"
    )
    targets = pd.Series(
        truths_arr, index=pd.DatetimeIndex(pred_dates), name="logrv_target"
    )
    return {
        "horizon": horizon,
        "n_splits": n_splits,
        "n_total_preds": len(preds_arr),
        "aggregate_mse_logrv": aggregate_mse,
        "fold_results": fold_results,
        "forecasts": forecasts,
        "targets": targets,
    }


# -- Evaluation helpers -------------------------------------------------------

def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(365) if sigma > 1e-12 else float("nan")


def evaluate_one_combo(
    coin: str,
    horizon: int,
    seed: int,
    hidden_size: int = HIDDEN_SIZE,
    oos_strict_year: int | None = None,
) -> dict | None:
    """Run LSTM vs HAR Classic for one (coin, horizon, seed) combo.

    If oos_strict_year is set, data on/after Jan 1st of that year is held out
    from training/walk-forward (reserved for separate OOS verdict).
    """
    import torch

    torch.manual_seed(seed)
    np.random.seed(seed)

    hourly_rets = _load_one_coin(coin)
    if oos_strict_year is not None:
        cutoff = pd.Timestamp(f"{oos_strict_year}-01-01", tz=hourly_rets.index.tz)
        hourly_rets = hourly_rets[hourly_rets.index < cutoff]
    if len(hourly_rets) < 1000:
        return None

    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return None

    features, rv_aligned = prepare_features(hourly_rets)
    if len(features) < 200:
        return None

    # HAR Classic baseline
    try:
        har_out = walk_forward_har(rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY)
    except Exception:
        return None

    # LSTM
    try:
        lstm_out = walk_forward_lstm(
            features, rv_aligned, horizon=horizon,
            n_splits=N_SPLITS, refit_every=REFIT_EVERY,
            seed=seed, hidden_size=hidden_size,
        )
    except Exception as e:
        print(f"    LSTM failed: {e}", flush=True)
        return None

    har_fc = har_out["forecasts"]
    lstm_fc = lstm_out["forecasts"]
    common_fc_idx = har_fc.index.intersection(lstm_fc.index)
    if len(common_fc_idx) < 30:
        return None
    har_fc = har_fc.loc[common_fc_idx]
    lstm_fc = lstm_fc.loc[common_fc_idx]

    # Daily close returns
    daily_rets = hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    daily_rets.index = pd.DatetimeIndex(daily_rets.index).normalize()
    daily_rets = daily_rets.reindex(common_fc_idx).dropna()
    if len(daily_rets) < 30:
        return None
    har_fc = har_fc.reindex(daily_rets.index)
    lstm_fc = lstm_fc.reindex(daily_rets.index)

    # Kelly weights for each model
    har_pair = _kelly_weights_and_returns(daily_rets, har_fc, MU_WINDOW, KELLY_CAP)
    lstm_pair = _kelly_weights_and_returns(daily_rets, lstm_fc, MU_WINDOW, KELLY_CAP)
    if har_pair is None or lstm_pair is None:
        return None
    har_w, r = har_pair
    lstm_w, _ = lstm_pair
    if len(r) < 50:
        return None

    # Net returns at FEE_BPS
    har_net = _net_at_fee(har_w, r, FEE_BPS)
    lstm_net = _net_at_fee(lstm_w, r, FEE_BPS)
    bh_net = r.copy()

    # Sharpe
    sharpe_har = _sharpe_ann(har_net)
    sharpe_lstm = _sharpe_ann(lstm_net)
    sharpe_bh = _sharpe_ann(bh_net)
    delta_sharpe_lstm_vs_har = sharpe_lstm - sharpe_har

    # LW2008 paired Sharpe-diff SE
    _, _, _, se = ledoit_wolf_sharpe_diff_se(lstm_net, har_net)
    t_stat = delta_sharpe_lstm_vs_har / se if isinstance(se, float) and se > 1e-12 else float("nan")

    # MSE comparison on log-RV
    target = har_out["targets"].reindex(common_fc_idx).dropna()
    har_pred_aligned = har_fc.reindex(target.index)
    lstm_pred_aligned = lstm_fc.reindex(target.index)
    mse_har = float(np.mean((har_pred_aligned - target) ** 2))
    mse_lstm = float(np.mean((lstm_pred_aligned - target) ** 2))
    mse_reduction_pct = (mse_lstm - mse_har) / mse_har * 100 if mse_har > 0 else float("nan")

    return {
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "sharpe_har": sharpe_har,
        "sharpe_lstm": sharpe_lstm,
        "sharpe_bh": sharpe_bh,
        "delta_sharpe_lstm_vs_har": delta_sharpe_lstm_vs_har,
        "lw_se": se,
        "t_stat": t_stat,
        "mse_har": mse_har,
        "mse_lstm": mse_lstm,
        "mse_reduction_pct": mse_reduction_pct,
        "n_obs": len(r),
        "lstm_preds": len(lstm_fc),
        "har_preds": len(har_fc),
    }


def _csv_list(value: str) -> list[str]:
    return [s.strip() for s in value.split(",") if s.strip()]


def _csv_int_list(value: str) -> list[int]:
    return [int(s.strip()) for s in value.split(",") if s.strip()]


def main() -> None:
    parser = argparse.ArgumentParser(description="M15 Log-LSTM RV sweep")
    parser.add_argument("--dry-run", action="store_true", help="Run BTC h=1 seed=0 only")
    parser.add_argument("--hidden-size", type=int, default=HIDDEN_SIZE,
                        help=f"LSTM hidden size (default: {HIDDEN_SIZE})")
    parser.add_argument(
        "--seeds",
        type=_csv_int_list,
        default=None,
        help="Comma-separated seeds override (default: 0,1,7,42)",
    )
    parser.add_argument(
        "--coins",
        type=_csv_list,
        default=None,
        help="Comma-separated coins override (default: BTC/ETH/SOL/LTC/XRP/ADA/DOT)",
    )
    parser.add_argument(
        "--horizons",
        type=_csv_int_list,
        default=None,
        help="Comma-separated horizons override (default: 1,5,10)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Override results directory (default: results/m15_lstm_rv_h{hidden_size}/)",
    )
    parser.add_argument(
        "--oos-strict",
        type=int,
        default=None,
        metavar="YEAR",
        help=(
            "Hold out all data >= Jan 1st of YEAR from training/walk-forward "
            "(for separate OOS verdict). Example: --oos-strict 2027"
        ),
    )
    args = parser.parse_args()

    hidden_size = args.hidden_size
    coins = args.coins if args.coins is not None else COINS
    horizons = args.horizons if args.horizons is not None else HORIZONS
    seeds = args.seeds if args.seeds is not None else SEEDS
    oos_strict_year = args.oos_strict

    import torch
    print(f"PyTorch {torch.__version__}, CUDA: {torch.cuda.is_available()}")
    if torch.cuda.is_available():
        print(f"  GPU: {torch.cuda.get_device_name(0)}")

    model_demo = build_lstm(3, hidden_size, NUM_LAYERS)
    n_params = count_params(model_demo)
    print(f"LSTM params: {n_params} (hidden={hidden_size}, layers={NUM_LAYERS}, window={WINDOW})")

    results_dir = (
        args.output
        if args.output is not None
        else SCRIPT_DIR / "results" / f"m15_lstm_rv_h{hidden_size}"
    )
    results_dir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    checkpoint_path = results_dir / "checkpoint.jsonl"
    combos: list[dict] = []
    completed_keys: set[tuple] = set()
    if checkpoint_path.exists():
        with open(checkpoint_path, "r") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                combos.append(row)
                completed_keys.add((row["coin"], row["horizon"], row["seed"]))
        print(f"[CHECKPOINT] resumed {len(combos)} combos from {checkpoint_path.name}", flush=True)

    total = len(coins) * len(horizons) * len(seeds)
    done = 0

    if args.dry_run:
        print("[DRY RUN] BTC-USD h=1 seed=0 only")
        row = evaluate_one_combo("BTC-USD", 1, 0, hidden_size=hidden_size,
                                 oos_strict_year=oos_strict_year)
        if row:
            combos.append(row)
            print(json.dumps(row, indent=2))
        return

    if oos_strict_year is not None:
        print(f"[OOS-STRICT] Holding out data >= {oos_strict_year}-01-01")

    for coin in coins:
        for h in horizons:
            for seed in seeds:
                done += 1
                key = (coin, h, seed)
                if key in completed_keys:
                    print(f"\n[{done}/{total}] {coin} h={h} seed={seed} -- SKIP (checkpoint)", flush=True)
                    continue
                print(f"\n[{done}/{total}] {coin} h={h} seed={seed}", flush=True)
                row = evaluate_one_combo(coin, h, seed, hidden_size=hidden_size,
                                         oos_strict_year=oos_strict_year)
                if row is not None:
                    combos.append(row)
                    with open(checkpoint_path, "a") as f:
                        f.write(json.dumps(row, default=str) + "\n")
                else:
                    print(f"  SKIPPED (insufficient data)", flush=True)

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"M15 LSTM RV sweep complete: {len(combos)}/{total} combos in {elapsed:.0f}s")

    # Aggregate sign-test
    n_combos = len(combos)
    n_lstm_beats_har = sum(1 for r in combos if r["delta_sharpe_lstm_vs_har"] > 0)
    median_delta = float(np.median([r["delta_sharpe_lstm_vs_har"] for r in combos])) if combos else float("nan")
    median_mse = float(np.median([r["mse_reduction_pct"] for r in combos])) if combos else float("nan")
    p_sign = _binomial_pvalue_one_sided(n_lstm_beats_har, n_combos)

    # Per-coin aggregation
    per_coin: dict[str, dict] = {}
    for r in combos:
        c = r["coin"]
        per_coin.setdefault(c, {"deltas": [], "mses": []})
        per_coin[c]["deltas"].append(r["delta_sharpe_lstm_vs_har"])
        per_coin[c]["mses"].append(r["mse_reduction_pct"])

    # Per-horizon aggregation
    per_horizon: dict[int, dict] = {}
    for r in combos:
        h = r["horizon"]
        per_horizon.setdefault(h, {"deltas": [], "mses": []})
        per_horizon[h]["deltas"].append(r["delta_sharpe_lstm_vs_har"])
        per_horizon[h]["mses"].append(r["mse_reduction_pct"])

    print(f"\nSign-test: {n_lstm_beats_har}/{n_combos} ({n_lstm_beats_har/n_combos*100:.1f}%) LSTM>HAR")
    print(f"  p-value = {p_sign:.4f}")
    print(f"  median delta-Sharpe = {median_delta:+.4f}")
    print(f"  median MSE change = {median_mse:+.1f}%")
    print(f"\nPer-coin:")
    for c in coins:
        if c in per_coin:
            med = float(np.median(per_coin[c]["deltas"]))
            med_mse = float(np.median(per_coin[c]["mses"]))
            n_beats = sum(1 for d in per_coin[c]["deltas"] if d > 0)
            n_total = len(per_coin[c]["deltas"])
            print(f"  {c}: {med:+.4f} (MSE {med_mse:+.1f}%, beats {n_beats}/{n_total})")

    print(f"\nPer-horizon:")
    for h in HORIZONS:
        if h in per_horizon:
            med = float(np.median(per_horizon[h]["deltas"]))
            n_beats = sum(1 for d in per_horizon[h]["deltas"] if d > 0)
            n_total = len(per_horizon[h]["deltas"])
            print(f"  h={h}: {med:+.4f} ({n_beats}/{n_total})")

    # Verdict (G.2 strict)
    if p_sign < 0.05 and n_lstm_beats_har / max(n_combos, 1) >= 0.60:
        verdict = "BEATS"
    elif p_sign < 0.10 and n_lstm_beats_har / max(n_combos, 1) >= 0.55:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    print(f"\nVERDICT: {verdict} (p={p_sign:.4f}, win_rate={n_lstm_beats_har/n_combos*100:.1f}%)")

    # Save
    results = {
        "model": "Log-LSTM RV",
        "reference": "LSTM (Hochreiter & Schmidhuber 1997) applied to log-realized variance",
        "kelly_cap": KELLY_CAP,
        "fee_bps": FEE_BPS,
        "mu_window": MU_WINDOW,
        "n_splits": N_SPLITS,
        "refit_every": REFIT_EVERY,
        "window": WINDOW,
        "hidden_size": hidden_size,
        "num_layers": NUM_LAYERS,
        "n_params": n_params,
        "n_combos": n_combos,
        "n_lstm_beats_har": n_lstm_beats_har,
        "win_rate": n_lstm_beats_har / max(n_combos, 1),
        "p_sign": p_sign,
        "median_delta_sharpe": median_delta,
        "median_mse_change_pct": median_mse,
        "verdict": verdict,
        "runtime_s": elapsed,
        "combos": combos,
    }

    with open(results_dir / "results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)

    # CSV
    df = pd.DataFrame(combos)
    df.to_csv(results_dir / "m15_lstm_rv_results.csv", index=False)

    print(f"\nResults saved to {results_dir}")


if __name__ == "__main__":
    main()
