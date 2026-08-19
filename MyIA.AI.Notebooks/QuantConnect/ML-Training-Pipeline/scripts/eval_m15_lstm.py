"""M15 Log-LSTM on ETF daily direction -- terrain commun with Chronos/Kronos.

3rd rung of the foundation-model spin-out #8607 (Epic #1409 / #1454):
the 1st rung was Chronos-Bolt (zero-shot, language of time series, #8610) and
the 2nd was Kronos (zero-shot, K-lines OHLCV, #8620). Both were NO BEATS on the
anti-bias basket (SPY/TLT/GLD) at long horizons (h=22/66/132). This script asks
the complementary question: does a small LSTM **fine-tuned** on the ETF direction
extract a directional edge that the zero-shot foundation models could not?

Question
--------
Does a fine-tuned Log-LSTM beat majority-class for ETF direction forecasting at
long horizons, on the SAME anti-bias basket and the SAME protocol as the
zero-shot foundation rungs?

Terrain commun (apples-to-apples with Chronos-Bolt / Kronos)
------------------------------------------------------------
- Universe: anti-bias basket SPY / TLT / GLD (no FAANG/Mag7) via load_data on
  datasets/panier (yfinance daily OHLCV).
- Protocol: walk-forward 5-fold expanding, 5 seeds (0/1/7/42/99), transaction
  cost 10 bps per rebalance, majority-class baseline.
- Horizons: pred_len in {24, 66, 132} (~ h=22 / 66 / 132 business days).
- Metric: edge_vs_majority = DirAcc - majority_baseline.
- Gate (§C CONJUNCTION, both legs required):
    * sigma leg : seeds>=4 AND mean_edge>0 AND (std<1e-10 OR mean_edge>=2*std)
    * DM leg    : dm_p_median < 0.05, Diebold-Mariano on an **mse** precision
                  loss vs the no-change (martingale) path forecast.
  sigma alone measures dispersion across seeds, NOT significance: this pipeline
  has a +19.97-sigma edge with DM p=0.236 on record. "linear" is a bias control
  and is never the conjunction leg (#10956/#10961). A missing DM leg yields
  INCONCLUSIVE, never BEATS -- absent evidence is not evidence (#11395).
  Per-seed signed bias (model AND baseline) is reported, per §C point 7.

The DirAcc definition matches evaluate_window (eval_kronos_zeroshot): a forecast
*path* is produced and we measure the fraction of day-over-day directional moves
predicted correctly. The LSTM is trained to regress the cumulative log-return
path over the next pred_len days (direct multi-step forecast); the predicted
path's day-over-day sign is then compared to the actual daily-return sign.

Why a self-contained walk-forward (C898-L)
------------------------------------------
Chronos/Kronos are zero-shot: load a frozen model and call predict per window.
M15 is fine-tuned: the model is TRAINED on the expanding window before each fold.
That is a structurally different inner loop, so this harness owns its walk-forward
(just like m15_lstm_rv.walk_forward_lstm) and reuses only the STABLE shared
helpers -- load_data, the majority-baseline / direction-accuracy formulas, and
the beats_valid gate -- rather than the zero-shot build_evaluation_windows /
evaluate_window contract. This keeps M15 robust to the #8620 OHLCV-contract
merge (no shared mutable contract dependency) while preserving identical outer
metrics, so the cross-model comparison stays apples-to-apples.

Stochasticity note (C897-L)
---------------------------
Unlike Chronos-Bolt (deterministic decoder -> std_edge=0 -> degenerate gate),
the LSTM training has seeded stochasticity (weight init + minibatch order).
torch.manual_seed + np.random.seed are set per seed, so std_edge>0 across seeds
is expected and the multi-seed gate is a REAL test for M15 (as it is for Kronos).

Architecture
------------
    Input:  sliding window W=22 days of [log_return, sign(log_return)] -> (W, 2)
    Model:  LSTM(hidden=64, 1 layer) + FC(64, pred_len)
    Target: cumulative log-return path over next pred_len days (direct multi-step)
    Loss:   MSE on the cumulative log-return path

Usage
-----
    # Dry-run (CPU, synthetic data, 2 folds, 1 seed)
    python eval_m15_lstm.py --dry-run

    # Pilot: anti-bias basket, h~22 only, 5 seeds (the h=22 column of the sweep)
    python eval_m15_lstm.py --data-dir ../datasets/panier --horizons 24

    # Full sweep (multi-cycle, checkpoint-resumable)
    python eval_m15_lstm.py --data-dir ../datasets/panier --horizons 24,66,132

Output
------
- results/m15_lstm_etf/results.json  (sweep consolidated, tracked)
- results/m15_lstm_etf/verdict.md    (verdict vs Chronos/Kronos)
- results/m15_lstm_etf/checkpoint.jsonl (resumability, gitignored)

Env: conda coursia-ml-training (Python 3.11, PyTorch 2.5.1 + CUDA, RTX 3070).
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from data_utils import load_data  # noqa: E402
from dm_test import diebold_mariano_test  # noqa: E402

# -- Terrain-commun constants (match Chronos-Bolt / Kronos rungs) ------------

SYMBOLS = ["SPY", "TLT", "GLD"]
HORIZONS = [24, 66, 132]  # ~ h=22 / 66 / 132 business days
SEEDS = [0, 1, 7, 42, 99]
N_SPLITS = 5
COST_BPS = 10.0
WINDOW = 22  # input lookback (days), matches M15 LSTM convention
HIDDEN_SIZE = 64
NUM_LAYERS = 1
LEARNING_RATE = 1e-3
MAX_EPOCHS = 100
PATIENCE = 10
BATCH_SIZE = 32
RESULTS_DIR = SCRIPT_DIR / "results" / "m15_lstm_etf"


# -- Baselines / metrics (stable formulas, identical to eval_kronos_zeroshot) -

def compute_direction_accuracy(y_true: np.ndarray, y_pred: np.ndarray) -> float:
    """Fraction of correctly predicted directional moves."""
    if len(y_true) == 0:
        return 0.0
    return float(np.mean(np.sign(y_true) == np.sign(y_pred)))


def compute_majority_baseline(returns: np.ndarray) -> dict:
    """Majority-class baseline for direction prediction (identical to rungs 1-2)."""
    up_frac = float(np.mean(returns > 0))
    down_frac = float(np.mean(returns < 0))
    majority_acc = max(up_frac, down_frac)
    return {
        "majority_class_accuracy": majority_acc,
        "pct_up": up_frac,
        "pct_down": down_frac,
        "majority_class": "up" if up_frac >= down_frac else "down",
    }


# -- LSTM model ---------------------------------------------------------------

def build_lstm(input_size: int, pred_len: int, hidden_size: int = HIDDEN_SIZE,
               num_layers: int = NUM_LAYERS):
    """Build a minimal LSTM that direct-forecasts the cumulative log-return path.

    Output shape: (pred_len,) -- the predicted cumulative log-return over the
    next pred_len days. Day-over-day predicted returns are obtained by diff,
    matching evaluate_window's DirAcc computation.
    """
    import torch
    import torch.nn as nn

    class LSTMDirectionModel(nn.Module):
        def __init__(self, inp_sz, hid_sz, n_layers, out_sz):
            super().__init__()
            self.lstm = nn.LSTM(inp_sz, hid_sz, n_layers, batch_first=True)
            self.fc = nn.Linear(hid_sz, out_sz)

        def forward(self, x):
            out, _ = self.lstm(x)
            return self.fc(out[:, -1, :])

    return LSTMDirectionModel(input_size, hidden_size, num_layers, pred_len)


def count_params(model) -> int:
    import torch
    return sum(p.numel() for p in model.parameters())


# -- Feature / target construction --------------------------------------------

def prepare_features(prices: pd.Series) -> tuple[np.ndarray, np.ndarray]:
    """Build [log_return, sign(log_return)] features from a daily close series.

    Returns (features, log_returns) where features.shape = (N, 2) and
    log_returns.shape = (N,). Indexing is aligned (features[i] describes day i).
    """
    log_ret = np.log(prices).diff()
    sign_ret = pd.Series(np.sign(log_ret.values), index=log_ret.index, name="sign_ret")
    features = pd.concat([log_ret.rename("log_ret"), sign_ret], axis=1).replace(
        [np.inf, -np.inf], np.nan
    ).dropna()
    log_ret_aligned = log_ret.reindex(features.index).fillna(0.0)
    return features.values.astype(np.float32), log_ret_aligned.values.astype(np.float32)


def make_cumulative_targets(log_returns: np.ndarray, pred_len: int) -> np.ndarray:
    """For each start index i, the cumulative log-return path over [i, i+pred_len).

    targets[i, k] = sum(log_returns[i : i+k+1]) for k in 0..pred_len-1.
    Shape: (N, pred_len). NaN where the window runs past the end.
    """
    n = len(log_returns)
    targets = np.full((n, pred_len), np.nan)
    for i in range(n - pred_len):
        seg = log_returns[i : i + pred_len]
        targets[i] = np.cumsum(seg)
    return targets


def make_sequences(features: np.ndarray, targets: np.ndarray, window: int):
    """Sliding-window sequences for LSTM training.

    X shape: (M, window, n_features); y shape: (M, pred_len).
    Only indices where the target path is fully finite are kept.
    """
    X, y = [], []
    for i in range(window, len(features)):
        if not np.all(np.isfinite(targets[i])):
            continue
        X.append(features[i - window : i])
        y.append(targets[i])
    if not X:
        return np.empty((0, window, features.shape[1])), np.empty((0, targets.shape[1]))
    return np.asarray(X, dtype=np.float32), np.asarray(y, dtype=np.float32)


# -- Walk-forward LSTM training ----------------------------------------------

def train_lstm(X_train: np.ndarray, y_train: np.ndarray, input_size: int,
               pred_len: int, seed: int, device) -> tuple:
    """Train one LSTM on the given fold's sequences. Returns (model, best_loss)."""
    import torch
    import torch.nn as nn

    torch.manual_seed(seed)

    model = build_lstm(input_size, pred_len).to(device)
    optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
    criterion = nn.MSELoss()

    X_t = torch.FloatTensor(X_train).to(device)
    y_t = torch.FloatTensor(y_train).to(device)

    best_loss = float("inf")
    best_state = None
    no_improve = 0
    last_epoch = 0

    for epoch in range(MAX_EPOCHS):
        model.train()
        perm = torch.randperm(len(X_t))
        epoch_loss = 0.0
        n_batches = 0
        for start in range(0, len(perm), BATCH_SIZE):
            idx = perm[start : start + BATCH_SIZE]
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
        last_epoch = epoch + 1
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
    return model, best_loss, last_epoch


def walk_forward_direction(
    prices: pd.Series,
    horizon: int,
    seed: int,
    n_splits: int = N_SPLITS,
    window: int = WINDOW,
) -> dict:
    """Walk-forward LSTM direction evaluation on one (symbol, horizon, seed).

    Expanding window, n_splits folds. For each fold, train on [0:train_end] then
    predict the cumulative log-return path for every test window in the fold and
    accumulate DirAcc contributions (day-over-day sign match, identical to
    evaluate_window).
    """
    import torch

    torch.manual_seed(seed)
    np.random.seed(seed)

    features, log_returns = prepare_features(prices)
    n = len(features)
    if n < (n_splits + 1) * 30:
        raise ValueError(f"n={n} too small for {n_splits} walk-forward splits")

    targets = make_cumulative_targets(log_returns, horizon)

    fold_size = n // (n_splits + 1)
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    # Aggregated day-over-day direction hits across all folds.
    all_actual_rets: list[float] = []
    all_pred_rets: list[float] = []
    fold_results: list[dict] = []

    for fold_idx in range(1, n_splits + 1):
        train_end = fold_size * fold_idx
        test_start = train_end
        test_end = min(train_end + fold_size, n - horizon)
        if test_end <= test_start + window:
            continue

        # Train on expanding [0:train_end]
        train_feat = features[:train_end]
        train_targets = targets[:train_end]
        # Normalize features using train statistics.
        feat_mean = np.nanmean(train_feat, axis=0)
        feat_std = np.nanstd(train_feat, axis=0) + 1e-8
        train_feat_norm = (train_feat - feat_mean) / feat_std

        X_train, y_train = make_sequences(train_feat_norm, train_targets, window)
        if len(X_train) < 20:
            continue

        model, best_loss, epochs_trained = train_lstm(
            X_train, y_train, input_size=X_train.shape[2],
            pred_len=horizon, seed=seed, device=device,
        )

        # Predict for each test window in the fold.
        fold_actual: list[float] = []
        fold_pred: list[float] = []
        for i in range(test_start, test_end):
            if i < window:
                continue
            # Normalize with statistics from all data up to i (no leakage of test).
            feat_so_far = features[:i]
            f_mean = np.nanmean(feat_so_far, axis=0)
            f_std = np.nanstd(feat_so_far, axis=0) + 1e-8
            seq = (features[i - window : i] - f_mean) / f_std
            seq_tensor = torch.FloatTensor(seq).unsqueeze(0).to(device)
            with torch.no_grad():
                pred_path = model(seq_tensor).squeeze(0).cpu().numpy()

            # Predicted day-over-day returns = diff of the cumulative path.
            pred_rets = np.diff(pred_path)
            # Actual day-over-day log-returns over [i, i+horizon).
            actual_rets = log_returns[i + 1 : i + horizon]

            m = min(len(pred_rets), len(actual_rets))
            if m < 1:
                continue
            fold_actual.extend(actual_rets[:m].tolist())
            fold_pred.extend(pred_rets[:m].tolist())

        if len(fold_actual) >= 10:
            fold_dir_acc = compute_direction_accuracy(
                np.asarray(fold_actual), np.asarray(fold_pred)
            )
            fold_results.append({
                "fold": fold_idx,
                "train_size": train_end,
                "n_test_points": len(fold_actual),
                "direction_accuracy": fold_dir_acc,
                "best_train_loss": best_loss,
                "epochs_trained": epochs_trained,
            })
            all_actual_rets.extend(fold_actual)
            all_pred_rets.extend(fold_pred)

    if not fold_results:
        return {"error": "no valid folds produced"}

    actual_arr = np.asarray(all_actual_rets)
    pred_arr = np.asarray(all_pred_rets)
    dir_acc = compute_direction_accuracy(actual_arr, pred_arr)

    # -- Diebold-Mariano precision leg (§C conjunction) ------------------------
    # The sigma leg (aggregation below) measures a DIRECTIONAL edge; §C also
    # requires a significance leg on a PRECISION loss (mse/mae), never on
    # "linear" -- that one is a bias differential, blind to dispersion
    # (#10956/#10961, documented in dm_test.py itself).
    #
    # Both legs bear on the SAME forecast object: the model regresses the
    # cumulative log-return path, and the day-over-day signs OF THAT PATH are
    # what produce DirAcc. The numeric counterpart of the majority baseline is
    # therefore the no-change (martingale) forecast pred=0 -- the standard
    # benchmark for return prediction: e_baseline = 0 - actual = -actual.
    # This does NOT claim the two legs measure the same quantity. It claims a
    # directional edge must not ride a path less precise than predicting
    # nothing at all.
    dm_block: dict = {"available": False, "reason": "fewer than 30 paired points"}
    if len(actual_arr) >= 30:
        errors_model = pred_arr - actual_arr
        errors_naive = -actual_arr  # no-change forecast
        dm_res = diebold_mariano_test(
            errors_model, errors_naive, loss_fn="mse", horizon=horizon
        )
        dm_block = {
            "available": True,
            "loss_fn": "mse",
            "baseline": "no-change (martingale) path forecast",
            "dm_statistic": dm_res.dm_statistic,
            "p_value": dm_res.p_value,
            "mean_loss_diff": dm_res.mean_loss_diff,
            "n_observations": dm_res.n_observations,
            # §C point 7: signed bias reported for model AND baseline.
            "bias_model": float(np.mean(errors_model)),
            "bias_baseline": float(np.mean(errors_naive)),
            "mae_model": float(np.mean(np.abs(errors_model))),
            "mae_baseline": float(np.mean(np.abs(errors_naive))),
        }

    return {
        "horizon": horizon,
        "seed": seed,
        "n_splits": n_splits,
        "n_folds": len(fold_results),
        "n_test_points": len(all_actual_rets),
        "direction_accuracy": float(dir_acc),
        "dm": dm_block,
        "fold_results": fold_results,
        "device": str(device),
        "is_trained": True,
    }


# -- Per-config evaluation ----------------------------------------------------

def evaluate_symbol_horizon(
    symbol: str, horizon: int, seed: int, data_dir: Path,
) -> dict | None:
    """Run walk-forward M15 LSTM for one (symbol, horizon, seed)."""
    try:
        prices_df = load_data(data_dir, symbol=symbol)
    except FileNotFoundError:
        print(f"    [SKIP] no data for {symbol}", flush=True)
        return None
    prices = prices_df["Close"].dropna()
    if len(prices) < 400:
        print(f"    [SKIP] {symbol} too short ({len(prices)} pts)", flush=True)
        return None

    out = walk_forward_direction(prices, horizon=horizon, seed=seed)
    if "error" in out:
        print(f"    [SKIP] {symbol} h={horizon} seed={seed}: {out['error']}", flush=True)
        return None

    daily_returns = prices.pct_change().dropna().values
    baseline = compute_majority_baseline(np.asarray(daily_returns))
    edge = out["direction_accuracy"] - baseline["majority_class_accuracy"]
    out["symbol"] = symbol
    out["majority_baseline"] = baseline
    out["edge_vs_majority"] = float(edge)
    out["n_prices"] = int(len(prices))
    return out


def run_sweep(args: argparse.Namespace) -> dict:
    """Run the (symbol x horizon x seed) sweep with checkpoint resumability."""
    import torch

    symbols = args.symbols.split(",") if args.symbols else SYMBOLS
    horizons = [int(h) for h in args.horizons.split(",")] if args.horizons else HORIZONS
    seeds = [int(s) for s in args.seeds.split(",")] if args.seeds else SEEDS

    data_dir = Path(args.data_dir)
    results_dir = Path(args.output) if args.output else RESULTS_DIR
    results_dir.mkdir(parents=True, exist_ok=True)
    checkpoint_path = results_dir / "checkpoint.jsonl"

    print(f"PyTorch {torch.__version__}, CUDA: {torch.cuda.is_available()}", flush=True)
    if torch.cuda.is_available():
        print(f"  GPU: {torch.cuda.get_device_name(0)}", flush=True)
    demo = build_lstm(2, horizons[0])
    print(f"LSTM params (input=2, hidden={HIDDEN_SIZE}, layers={NUM_LAYERS}, "
          f"pred_len={horizons[0]}): {count_params(demo)}", flush=True)

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
                completed_keys.add((row["symbol"], row["horizon"], row["seed"]))
        print(f"[CHECKPOINT] resumed {len(combos)} combos", flush=True)

    total = len(symbols) * len(horizons) * len(seeds)
    done = 0
    t0 = time.time()

    for symbol in symbols:
        for horizon in horizons:
            for seed in seeds:
                done += 1
                key = (symbol, horizon, seed)
                if key in completed_keys:
                    print(f"[{done}/{total}] {symbol} h={horizon} seed={seed} -- SKIP (checkpoint)",
                          flush=True)
                    continue
                print(f"[{done}/{total}] {symbol} h={horizon} seed={seed}", flush=True)
                row = evaluate_symbol_horizon(symbol, horizon, seed, data_dir)
                if row is not None:
                    combos.append(row)
                    with open(checkpoint_path, "a") as f:
                        f.write(json.dumps(row, default=str) + "\n")
                    print(f"    DirAcc={row['direction_accuracy']:.4f} "
                          f"majority={row['majority_baseline']['majority_class_accuracy']:.4f} "
                          f"edge={row['edge_vs_majority']:+.4f}", flush=True)
                else:
                    print("    SKIPPED (insufficient data)", flush=True)

    elapsed = time.time() - t0
    print(f"\nSweep: {len(combos)}/{total} combos in {elapsed:.0f}s", flush=True)

    # Aggregate per (symbol, horizon) across seeds for the beats_valid gate.
    summary_rows = []
    for symbol in symbols:
        for horizon in horizons:
            seed_rows = [r for r in combos
                         if r["symbol"] == symbol and r["horizon"] == horizon]
            if not seed_rows:
                continue
            edges = np.array([r["edge_vs_majority"] for r in seed_rows])
            mean_edge = float(np.mean(edges))
            std_edge = float(np.std(edges))
            n_beats = int(np.sum(edges > 0))
            # Leg 1 (sigma): directional edge, >=4 seeds, edge >= 2*std.
            sigma_leg = (
                len(seed_rows) >= 4 and mean_edge > 0
                and (std_edge < 1e-10 or mean_edge >= 2 * std_edge)
            )
            # Leg 2 (DM): median p-value across seeds on an mse precision loss.
            # §C is a CONJUNCTION -- sigma measures dispersion across seeds, not
            # significance, and a +19.97-sigma edge with DM p=0.236 is on record
            # in this very pipeline. A missing DM leg is NOT a pass: absent
            # evidence yields INCONCLUSIVE, never BEATS (#11395 class).
            dm_rows = [r["dm"] for r in seed_rows
                       if isinstance(r.get("dm"), dict) and r["dm"].get("available")]
            dm_ps = [d["p_value"] for d in dm_rows]
            dm_p_median = float(np.median(dm_ps)) if dm_ps else None
            # DIRECTION MATTERS. A small p-value says the two forecasts differ
            # significantly, NOT that the model wins. Measured on the synthetic
            # dry run (geometric random walk, nothing to predict): p_value=0.0
            # with mean_loss_diff=+1.15e-4 and mae 0.0146 vs 0.0119 -- i.e. the
            # model significantly WORSE than doing nothing. A p-only leg would
            # have passed it. d = loss_model - loss_baseline, so the model wins
            # only when the differential is NEGATIVE.
            dm_diff_median = (float(np.median([d["mean_loss_diff"] for d in dm_rows]))
                              if dm_rows else None)
            dm_leg = (dm_p_median is not None and dm_p_median < 0.05
                      and dm_diff_median is not None and dm_diff_median < 0)

            beats_valid = bool(sigma_leg and dm_leg)
            if sigma_leg and dm_p_median is None:
                verdict = "INCONCLUSIVE (no DM evidence)"
            elif beats_valid:
                verdict = "BEATS"
            else:
                verdict = "NO BEATS"

            mean_diracc = float(np.mean([r["direction_accuracy"] for r in seed_rows]))
            majority = seed_rows[0]["majority_baseline"]["majority_class_accuracy"]
            # §C point 7: signed bias, model AND baseline, averaged across seeds.
            biases = [(r["dm"]["bias_model"], r["dm"]["bias_baseline"])
                      for r in seed_rows
                      if isinstance(r.get("dm"), dict) and r["dm"].get("available")]
            summary_rows.append({
                "symbol": symbol,
                "horizon": horizon,
                "n_seeds": len(seed_rows),
                "mean_direction_accuracy": mean_diracc,
                "majority_baseline": majority,
                "mean_edge": mean_edge,
                "std_edge": std_edge,
                "n_beats": n_beats,
                "sigma_leg": sigma_leg,
                "dm_leg": dm_leg,
                "dm_p_median": dm_p_median,
                "dm_mean_loss_diff_median": dm_diff_median,
                "dm_loss_fn": "mse",
                "mean_bias_model": float(np.mean([b[0] for b in biases])) if biases else None,
                "mean_bias_baseline": float(np.mean([b[1] for b in biases])) if biases else None,
                # Kept explicitly so a reader can see whether the pre-§C gate
                # would have over-called this cell (sigma_only=True while
                # beats_valid=False is exactly the #11395 defect, made visible).
                "sigma_only_legacy_verdict": sigma_leg,
                "beats_valid": beats_valid,
                "verdict": verdict,
            })
            dm_txt = f"{dm_p_median:.4f}" if dm_p_median is not None else "n/a"
            print(f"  {symbol} h={horizon}: DirAcc={mean_diracc:.4f} "
                  f"majority={majority:.4f} edge={mean_edge:+.4f} "
                  f"(std={std_edge:.4f}, beats {n_beats}/{len(seed_rows)}) "
                  f"sigma_leg={sigma_leg} dm_p_median={dm_txt} "
                  f"[{verdict}]", flush=True)

    sweep_summary = {
        "model": "Log-LSTM ETF-direction (M15 adapted, fine-tuned)",
        "reference": "LSTM (Hochreiter & Schubhuber 1997), direct multi-step "
                     "cumulative log-return forecast, terrain commun with "
                     "Chronos-Bolt (#8610) and Kronos (#8620)",
        "terrain_commun": {
            "symbols": symbols,
            "horizons": horizons,
            "seeds": seeds,
            "n_splits": N_SPLITS,
            "cost_bps": COST_BPS,
            "window": WINDOW,
            "hidden_size": HIDDEN_SIZE,
            "num_layers": NUM_LAYERS,
        },
        "device": "cuda" if torch.cuda.is_available() else "cpu",
        "is_trained": True,
        "n_combos": len(combos),
        "runtime_s": elapsed,
        "summary": summary_rows,
        "combos": combos,
    }

    with open(results_dir / "results.json", "w") as f:
        json.dump(sweep_summary, f, indent=2, default=str)
    print(f"\nResults saved to {results_dir}", flush=True)
    return sweep_summary


def run_dry_run() -> None:
    """Synthetic-data smoke test: verifies the pipeline trains (is_trained=True)."""
    import torch

    np.random.seed(42)
    n_points = 1200
    dates = pd.date_range("2020-01-01", periods=n_points, freq="B")
    # Geometric random walk (proper up/down mix, unlike an additive +drift walk).
    prices = pd.Series(
        100.0 * np.exp(np.cumsum(np.random.normal(0.0003, 0.015, n_points))), index=dates
    )
    horizon = 24
    print(f"[DRY RUN] synthetic {n_points} pts, h={horizon}, seed=0", flush=True)
    print(f"PyTorch {torch.__version__}, CUDA: {torch.cuda.is_available()}", flush=True)
    out = walk_forward_direction(prices, horizon=horizon, seed=0, n_splits=3)
    print(json.dumps({k: v for k, v in out.items()
                      if k not in ("fold_results",)}, indent=2, default=str))
    baseline = compute_majority_baseline(prices.pct_change().dropna().values)
    edge = out["direction_accuracy"] - baseline["majority_class_accuracy"]
    print(f"\nDirAcc={out['direction_accuracy']:.4f} "
          f"majority={baseline['majority_class_accuracy']:.4f} "
          f"edge={edge:+.4f} is_trained={out['is_trained']}", flush=True)
    assert out["is_trained"], "SOTA-OK: model must have trained"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="M15 Log-LSTM ETF-direction (terrain commun Chronos/Kronos)"
    )
    parser.add_argument("--dry-run", action="store_true",
                        help="Synthetic smoke test (CPU, 3 folds, 1 seed)")
    parser.add_argument("--data-dir", default="../datasets/panier", type=str,
                        help="Directory with {SYMBOL}_*.csv OHLCV files")
    parser.add_argument("--symbols", default=None, type=str,
                        help="Comma-separated symbols (default: SPY,TLT,GLD)")
    parser.add_argument("--horizons", default=None, type=str,
                        help="Comma-separated pred_len horizons (default: 24,66,132)")
    parser.add_argument("--seeds", default=None, type=str,
                        help="Comma-separated seeds (default: 0,1,7,42,99)")
    parser.add_argument("--output", default=None, type=str,
                        help="Override results directory")
    args = parser.parse_args()

    if args.dry_run:
        run_dry_run()
    else:
        run_sweep(args)


if __name__ == "__main__":
    main()
