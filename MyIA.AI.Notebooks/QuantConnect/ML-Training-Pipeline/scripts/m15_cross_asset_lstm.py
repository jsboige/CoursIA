"""M15 Cross-Asset LSTM RV -- Neural volatility forecasting on traditional assets.

Question
--------
Does a small LSTM beat HAR Classic for equity/bond/vol volatility forecasting
using daily squared returns as RV proxy?

Assets: SPY, TLT, ^VIX (daily close-to-close).
Horizons: h in {1, 5, 10, 22} (long-horizon emphasis per dispatch Cycle 77).
Walk-forward 5-fold expanding, multi-seed >=4, Kelly sign-test vs HAR baseline.

Architecture (same as crypto M15):
    Input:  sliding window W=22 days of [log_RV, returns, sign(returns)] -> (W, 3)
    Model:  LSTM(hidden=64, 1 layer) + FC(64, 1)
    Target: log(RV_{t+h})
    Loss:   MSE on log-RV

RV proxy for daily data: squared daily log-returns (no intraday available).

Output
------
- results/m15_cross_asset/results.json
- results/m15_cross_asset/m15_cross_asset_results.csv
- docs/M15_CROSS_ASSET.md (verdict)

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
from m11g_fee_aware_kelly import (  # noqa: E402
    _binomial_pvalue_one_sided,
    _kelly_weights_and_returns,
    _net_at_fee,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402

warnings.filterwarnings("ignore")

ASSETS = ["SPY", "TLT", "^VIX"]
HORIZONS = [1, 5, 10, 22]
SEEDS = [0, 1, 7, 42]
KELLY_CAP = 1.0
MU_WINDOW = 60
FEE_BPS = 5  # equity standard (not 50bps crypto)
N_SPLITS = 5
REFIT_EVERY = 22
RESULTS_DIR = SCRIPT_DIR / "results" / "m15_cross_asset"

# LSTM hyperparams (same as crypto M15)
WINDOW = 22
HIDDEN_SIZE = 64
NUM_LAYERS = 1
DROPOUT = 0.0
LEARNING_RATE = 1e-3
MAX_EPOCHS = 100
PATIENCE = 10
BATCH_SIZE = 32


# -- Data loading --------------------------------------------------------------

def load_daily_asset(ticker: str) -> pd.Series:
    """Load daily log-returns for a traditional asset via yfinance.

    Returns a Series of daily log-returns indexed by Date.
    """
    import yfinance as yf

    data = yf.download(ticker, period="max", auto_adjust=True, progress=False)
    if data.empty:
        raise ValueError(f"No data for {ticker}")
    close = data["Close"]
    if isinstance(close, pd.DataFrame):
        close = close.iloc[:, 0]
    close = close.dropna()
    log_rets = np.log(close / close.shift(1)).dropna()
    log_rets.index = pd.DatetimeIndex(log_rets.index).normalize()
    log_rets.name = "log_ret"
    return log_rets


def daily_squared_rv(daily_log_returns: pd.Series) -> pd.Series:
    """Proxy for Realized Variance using squared daily log-returns.

    RV_t = r_t^2 (single observation per day).
    """
    rv = daily_log_returns.astype(float) ** 2
    rv.index = pd.DatetimeIndex(rv.index).normalize()
    rv.index.name = "date"
    rv.name = "RV"
    return rv


def prepare_features_daily(daily_log_returns: pd.Series) -> tuple[pd.DataFrame, pd.Series]:
    """Build [log_RV, returns, sign_returns] features from daily data.

    Returns (features_df, rv_series) both indexed by date.
    """
    rv = daily_squared_rv(daily_log_returns)
    log_rv = np.log(rv.clip(lower=1e-12))

    sign_rets = np.sign(daily_log_returns).rename("sign_returns")

    features = pd.concat(
        [log_rv.rename("log_rv"), daily_log_returns.rename("returns"), sign_rets],
        axis=1, sort=False,
    )
    features = features.dropna()

    rv = rv.reindex(features.index)
    return features, rv


# -- LSTM Model (reused from m15_lstm_rv) -------------------------------------

def build_lstm(input_size: int = 3, hidden_size: int = HIDDEN_SIZE,
               num_layers: int = NUM_LAYERS):
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

    return LSTMVolModel(input_size, hidden_size, num_layers)


def count_params(model) -> int:
    import torch
    return sum(p.numel() for p in model.parameters())


def make_sequences(features: np.ndarray, targets: np.ndarray,
                   window: int) -> tuple[np.ndarray, np.ndarray]:
    X, y = [], []
    for i in range(len(features) - window):
        X.append(features[i:i + window])
        y.append(targets[i + window])
    return np.array(X), np.array(y)


# -- Walk-forward LSTM ---------------------------------------------------------

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
        train_feat = feat_vals[:train_end]
        train_target = target_vals[:train_end]

        feat_mean = np.nanmean(train_feat, axis=0)
        feat_std = np.nanstd(train_feat, axis=0) + 1e-8
        train_feat_norm = (train_feat - feat_mean) / feat_std

        X_train, y_train = make_sequences(train_feat_norm, train_target, window)
        if len(X_train) < 20:
            continue

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

        fold_preds: list[float] = []
        fold_truths: list[float] = []

        for i in range(test_start, test_end - horizon):
            if i < window:
                continue
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
                        pass

        fp = np.asarray(fold_preds)
        ft_arr = np.asarray(fold_truths)
        fold_mse = float(np.mean((fp - ft_arr) ** 2)) if len(fp) else float("nan")
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
    targets_s = pd.Series(
        truths_arr, index=pd.DatetimeIndex(pred_dates), name="logrv_target"
    )
    return {
        "horizon": horizon,
        "n_splits": n_splits,
        "n_total_preds": len(preds_arr),
        "aggregate_mse_logrv": aggregate_mse,
        "fold_results": fold_results,
        "forecasts": forecasts,
        "targets": targets_s,
    }


# -- Evaluation ----------------------------------------------------------------

def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(252) if sigma > 1e-12 else float("nan")


def evaluate_one_combo(
    asset: str,
    horizon: int,
    seed: int,
    hidden_size: int = HIDDEN_SIZE,
) -> dict | None:
    """Run LSTM vs HAR Classic for one (asset, horizon, seed) combo."""
    import torch

    torch.manual_seed(seed)
    np.random.seed(seed)

    try:
        daily_rets = load_daily_asset(asset)
    except Exception as e:
        print(f"    Data load failed for {asset}: {e}", flush=True)
        return None

    if len(daily_rets) < 500:
        return None

    rv = daily_squared_rv(daily_rets)
    if len(rv) < 300:
        return None

    features, rv_aligned = prepare_features_daily(daily_rets)
    if len(features) < 200:
        return None

    # HAR Classic baseline
    try:
        har_out = walk_forward_har(
            rv, horizon=horizon, n_splits=N_SPLITS, refit_every=REFIT_EVERY,
        )
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

    # Align daily returns
    daily_rets_aligned = daily_rets.reindex(common_fc_idx).dropna()
    if len(daily_rets_aligned) < 30:
        return None
    har_fc = har_fc.reindex(daily_rets_aligned.index)
    lstm_fc = lstm_fc.reindex(daily_rets_aligned.index)

    # Kelly weights
    har_pair = _kelly_weights_and_returns(daily_rets_aligned, har_fc, MU_WINDOW, KELLY_CAP)
    lstm_pair = _kelly_weights_and_returns(daily_rets_aligned, lstm_fc, MU_WINDOW, KELLY_CAP)
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

    sharpe_har = _sharpe_ann(har_net)
    sharpe_lstm = _sharpe_ann(lstm_net)
    sharpe_bh = _sharpe_ann(bh_net)
    delta_sharpe = sharpe_lstm - sharpe_har

    # LW2008 paired Sharpe-diff SE
    _, _, _, se = ledoit_wolf_sharpe_diff_se(lstm_net, har_net)
    t_stat = delta_sharpe / se if isinstance(se, float) and se > 1e-12 else float("nan")

    # MSE comparison
    target = har_out["targets"].reindex(common_fc_idx).dropna()
    har_pred_aligned = har_fc.reindex(target.index)
    lstm_pred_aligned = lstm_fc.reindex(target.index)
    mse_har = float(np.mean((har_pred_aligned - target) ** 2))
    mse_lstm = float(np.mean((lstm_pred_aligned - target) ** 2))
    mse_reduction_pct = (mse_lstm - mse_har) / mse_har * 100 if mse_har > 0 else float("nan")

    return {
        "asset": asset,
        "horizon": horizon,
        "seed": seed,
        "sharpe_har": sharpe_har,
        "sharpe_lstm": sharpe_lstm,
        "sharpe_bh": sharpe_bh,
        "delta_sharpe_lstm_vs_har": delta_sharpe,
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
    parser = argparse.ArgumentParser(description="M15 Cross-Asset LSTM RV sweep")
    parser.add_argument("--dry-run", action="store_true", help="SPY h=1 seed=0 only")
    parser.add_argument("--hidden-size", type=int, default=HIDDEN_SIZE)
    parser.add_argument("--seeds", type=_csv_int_list, default=None)
    parser.add_argument("--assets", type=_csv_list, default=None,
                        help="Override assets (default: SPY,TLT,^VIX)")
    parser.add_argument("--horizons", type=_csv_int_list, default=None)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    assets = args.assets if args.assets is not None else ASSETS
    horizons = args.horizons if args.horizons is not None else HORIZONS
    seeds = args.seeds if args.seeds is not None else SEEDS
    hidden_size = args.hidden_size

    import torch
    print(f"M15 Cross-Asset LSTM RV sweep", flush=True)
    print(f"PyTorch {torch.__version__}, CUDA: {torch.cuda.is_available()}", flush=True)
    if torch.cuda.is_available():
        print(f"  GPU: {torch.cuda.get_device_name(0)}", flush=True)

    model_demo = build_lstm(3, hidden_size, NUM_LAYERS)
    n_params = count_params(model_demo)
    print(f"LSTM params: {n_params} (hidden={hidden_size})", flush=True)
    print(f"Assets: {assets}", flush=True)
    print(f"Horizons: {horizons}", flush=True)
    print(f"Seeds: {seeds}", flush=True)
    print(f"FEE_BPS: {FEE_BPS} (equity standard)", flush=True)

    results_dir = (
        args.output if args.output is not None
        else SCRIPT_DIR / "results" / "m15_cross_asset"
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
                completed_keys.add((row["asset"], row["horizon"], row["seed"]))
        print(f"[CHECKPOINT] resumed {len(combos)} combos", flush=True)

    total = len(assets) * len(horizons) * len(seeds)
    done = len(combos)

    if args.dry_run:
        print("[DRY RUN] SPY h=1 seed=0 only")
        row = evaluate_one_combo("SPY", 1, 0, hidden_size=hidden_size)
        if row:
            combos.append(row)
            print(json.dumps(row, indent=2))
        return

    for asset in assets:
        for h in horizons:
            for seed in seeds:
                done += 1
                key = (asset, h, seed)
                if key in completed_keys:
                    print(f"\n[{done}/{total}] {asset} h={h} seed={seed} -- SKIP (checkpoint)", flush=True)
                    continue
                print(f"\n[{done}/{total}] {asset} h={h} seed={seed}", flush=True)
                row = evaluate_one_combo(asset, h, seed, hidden_size=hidden_size)
                if row is not None:
                    combos.append(row)
                    # Checkpoint
                    with open(checkpoint_path, "a") as f:
                        f.write(json.dumps(row) + "\n")
                    ds = row["delta_sharpe_lstm_vs_har"]
                    print(f"  LSTM={row['sharpe_lstm']:.3f} HAR={row['sharpe_har']:.3f} "
                          f"delta={ds:+.4f} t={row['t_stat']:.2f}", flush=True)
                else:
                    print(f"  SKIPPED (insufficient data or error)", flush=True)

    elapsed = time.time() - t0

    # Save results
    df = pd.DataFrame(combos)
    csv_path = results_dir / "m15_cross_asset_results.csv"
    df.to_csv(csv_path, index=False)

    # Aggregate verdict
    n_total = len(df)
    if n_total == 0:
        print("\nNo results. Exiting.")
        return

    lstm_wins = int((df["delta_sharpe_lstm_vs_har"] > 0).sum())
    n_beats = int((df["t_stat"] > 1.96).sum())
    median_delta = float(df["delta_sharpe_lstm_vs_har"].median())
    mean_delta = float(df["delta_sharpe_lstm_vs_har"].mean())

    # Binomial test
    p_val = _binomial_pvalue_one_sided(lstm_wins, n_total)

    verdict = "BEATS" if n_beats > 0 and p_val < 0.05 else (
        "INCONCLUSIVE" if lstm_wins > n_total / 2 else "NO BEATS"
    )

    summary = {
        "verdict": verdict,
        "n_total": n_total,
        "lstm_sharpe_wins": lstm_wins,
        "n_beats_t196": n_beats,
        "median_delta_sharpe": median_delta,
        "mean_delta_sharpe": mean_delta,
        "binomial_pvalue": p_val,
        "fee_bps": FEE_BPS,
        "hidden_size": hidden_size,
        "elapsed_s": elapsed,
        "assets": assets,
        "horizons": horizons,
        "seeds": seeds,
        "timestamp": pd.Timestamp.now().isoformat(),
    }

    json_path = results_dir / "results.json"
    with open(json_path, "w") as f:
        json.dump(summary, f, indent=2)

    print(f"\n{'='*60}", flush=True)
    print(f"VERDICT: {verdict}", flush=True)
    print(f"  {lstm_wins}/{n_total} Sharpe wins, {n_beats} BEATS (t>1.96)", flush=True)
    print(f"  median delta_sharpe = {median_delta:+.4f}", flush=True)
    print(f"  binomial p = {p_val:.4f}", flush=True)
    print(f"  Elapsed: {elapsed:.0f}s ({elapsed/60:.1f}min)", flush=True)
    print(f"  CSV: {csv_path}", flush=True)
    print(f"  JSON: {json_path}", flush=True)


if __name__ == "__main__":
    main()
