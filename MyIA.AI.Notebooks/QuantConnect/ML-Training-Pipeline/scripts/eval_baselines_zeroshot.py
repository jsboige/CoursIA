"""Trivial-baseline counterpoint for the #8607 foundation spin-out (#1409).

Purpose
-------
The 3 foundation rungs (Chronos-Bolt #8610, Kronos #8620, M15 LSTM #8625) are
all NO BEATS vs majority on the SPY/TLT/GLD ETF basket, and pairwise
indistinguishable (c.905 #8631). This module asks the **counterpoint** question:

    Do the simplest possible directional baselines (persistence, random-walk)
    do better or worse than the foundation models that "learn" the series?

If a trivial baseline that **ignores the series entirely** (random-walk = predict
no exploitable direction) or just **repeats the last move** (persistence =
naive momentum) lands on the same edge as Chronos/Kronos/M15, then the
sophistication of the foundation/fine-tuned models buys nothing on ETF
direction -- and #1409 (alpha = action policies, not price-direction forecast)
is reinforced by exhaustion of the methodological spectrum (trivial -> classic
-> foundation -> fine-tuned, all NO BEATS).

Baselines (deterministic, no seed)
----------------------------------
- **persistence**: predict that next day's direction == last observed day's
  direction (naive momentum / sign continuation). ``pred_rets[t] = log_returns[i-1]``
  for all t in the horizon window (apples-to-apples with the LSTM/Kronos test
  points: same folds, same ``actual_rets = log_returns[i+1:i+horizon]``).

Persistence is deterministic (no seed) -> ``std_edge = 0`` -> DEGENERATE at the
seed-level significance test (exactly like Chronos-Bolt, C893-L). The point of
this module is the **point estimate** of the edge vs majority, compared to the
foundation rungs via ``paired_rung_comparison.py`` (deterministic-vs-per-seed
alignment, c.905).

Note on random-walk: the financial random-walk baseline ("best forecast of
tomorrow is today") reduces, for *direction*, to predicting no change -- which
under a strict sign-match DirAcc matches only the ~0% of exactly-flat days
(DirAcc ~0.001), a degenerate artefact rather than a meaningful floor. The
random-walk *direction* forecast is therefore identical to persistence (predict
the last observed direction); we do not emit a separate predict-zero column.

Reuses ONLY stable helpers (C898-L): ``data_utils.load_data`` and the
majority/direction-accuracy formulas identical to eval_m15_lstm / eval_kronos.
No torch / no GPU.

Usage
-----
    python eval_baselines_zeroshot.py --data-dir <panier> \\
        --symbols SPY,TLT,GLD --horizons 24,66,132
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
import pandas as pd

from data_utils import load_data  # noqa: E402  (stable shared helper, C898-L)

SYMBOLS = ["SPY", "TLT", "GLD"]
HORIZONS = [24, 66, 132]  # ~ h=22 / 66 / 132 business days (identical to rungs)
N_SPLITS = 5  # identical to eval_m15_lstm walk-forward
WINDOW = 20  # context window size (identical to eval_m15_lstm prepare_features)


def prepare_features(prices: pd.Series) -> tuple[np.ndarray, np.ndarray]:
    """[log_ret, sign(log_ret)] features + the log-return series.

    Identical to eval_m15_lstm.prepare_features (stable feature contract).
    """
    daily_returns = prices.pct_change().dropna()
    log_returns = np.log(prices / prices.shift(1)).dropna()
    log_returns = log_returns.replace([np.inf, -np.inf], np.nan).dropna()
    sign = np.sign(log_returns).astype(float)
    features = np.column_stack([log_returns.values, sign.values])
    return features, log_returns.values


def compute_direction_accuracy(y_true: np.ndarray, y_pred: np.ndarray) -> float:
    """Fraction of correctly predicted directional moves (identical to rungs)."""
    if len(y_true) == 0:
        return 0.0
    return float(np.mean(np.sign(y_true) == np.sign(y_pred)))


def compute_majority_baseline(returns: np.ndarray) -> dict:
    """Majority-class baseline (identical to rungs 1-3)."""
    up_frac = float(np.mean(returns > 0))
    down_frac = float(np.mean(returns < 0))
    return {
        "majority_class_accuracy": max(up_frac, down_frac),
        "pct_up": up_frac,
        "pct_down": down_frac,
        "majority_class": "up" if up_frac >= down_frac else "down",
    }


def walk_forward_baseline(
    prices: pd.Series,
    horizon: int,
    baseline: str,
    n_splits: int = N_SPLITS,
    window: int = WINDOW,
) -> dict:
    """Walk-forward DirAcc of a trivial baseline on the SAME folds as the rungs.

    For each fold (expanding train [0:train_end], test [train_end:train_end+fold_size])
    and each test window i in the fold, the baseline predicts the direction of
    each of the next ``horizon`` days, and we accumulate sign-match contributions
    against ``actual_rets = log_returns[i+1:i+horizon]`` -- identical test points
    to eval_m15_lstm.walk_forward_direction, minus the LSTM.
    """
    features, log_returns = prepare_features(prices)
    n = len(features)
    if n < (n_splits + 1) * 30:
        raise ValueError(f"n={n} too small for {n_splits} walk-forward splits")

    fold_size = n // (n_splits + 1)
    all_actual: list[float] = []
    all_pred: list[float] = []
    fold_results: list[dict] = []

    for fold_idx in range(1, n_splits + 1):
        train_end = fold_size * fold_idx
        test_start = train_end
        test_end = min(train_end + fold_size, n - horizon)
        if test_end <= test_start + window:
            continue

        fold_actual: list[float] = []
        fold_pred: list[float] = []
        for i in range(test_start, test_end):
            if i < window:
                continue
            actual_rets = log_returns[i + 1: i + horizon]
            if baseline == "persistence":
                # Predict every future day's direction == last observed day's.
                last = log_returns[i - 1] if i >= 1 else 0.0
                pred_rets = np.full(len(actual_rets), last, dtype=float)
            elif baseline == "random_walk":
                # No exploitable signal: predict zero (no direction).
                pred_rets = np.zeros(len(actual_rets), dtype=float)
            else:
                raise ValueError(f"unknown baseline {baseline!r}")
            m = min(len(pred_rets), len(actual_rets))
            if m < 1:
                continue
            fold_actual.extend(actual_rets[:m].tolist())
            fold_pred.extend(pred_rets[:m].tolist())

        if len(fold_actual) >= 10:
            fold_dir_acc = compute_direction_accuracy(
                np.asarray(fold_actual), np.asarray(fold_pred))
            fold_results.append({
                "fold": fold_idx,
                "train_size": train_end,
                "n_test_points": len(fold_actual),
                "direction_accuracy": fold_dir_acc,
            })
            all_actual.extend(fold_actual)
            all_pred.extend(fold_pred)

    if not fold_results:
        return {"error": "no valid folds produced"}

    dir_acc = compute_direction_accuracy(np.asarray(all_actual), np.asarray(all_pred))
    return {
        "horizon": horizon,
        "baseline": baseline,
        "n_splits": n_splits,
        "n_folds": len(fold_results),
        "n_test_points": len(all_actual),
        "direction_accuracy": float(dir_acc),
        "fold_results": fold_results,
    }


def evaluate_symbol_horizon(symbol: str, horizon: int, data_dir: Path,
                            baseline: str) -> dict | None:
    prices_df = load_data(data_dir, symbol=symbol)
    if "Close" not in prices_df.columns:
        return None
    prices = prices_df["Close"].dropna()
    out = walk_forward_baseline(prices, horizon=horizon, baseline=baseline)
    if "error" in out:
        return None
    daily_returns = prices.pct_change().dropna().values
    base = compute_majority_baseline(np.asarray(daily_returns))
    edge = out["direction_accuracy"] - base["majority_class_accuracy"]
    out["symbol"] = symbol
    out["majority_baseline"] = base
    out["edge_vs_majority"] = float(edge)
    out["n_prices"] = int(len(prices))
    return out


def run_sweep(data_dir: Path, symbols: list[str], horizons: list[int]) -> dict:
    sweep = []
    combos = []  # M15-style combos (one per config) for paired_rung_comparison
    for baseline in ["persistence"]:
        for symbol in symbols:
            for horizon in horizons:
                row = evaluate_symbol_horizon(symbol, horizon, data_dir, baseline)
                if row is None:
                    continue
                diracc = row["direction_accuracy"]
                majority = row["majority_baseline"]["majority_class_accuracy"]
                edge = row["edge_vs_majority"]
                cfg = {
                    "symbol": symbol,
                    "pred_len": horizon,
                    "baseline": baseline,
                    "diracc": diracc,
                    "majority": majority,
                    "edge": edge,
                    "mean_edge": edge,
                    "std_edge": 0.0,  # deterministic baseline (C893-L)
                    "beats_valid": bool(edge > 0),
                    "fold_results": row["fold_results"],
                    "n_test_points": row["n_test_points"],
                }
                sweep.append(cfg)
                # M15-combo analogue (deterministic): single seed=0 carrying the edge.
                combos.append({
                    "symbol": symbol,
                    "horizon": horizon,
                    "seed": 0,
                    "baseline": baseline,
                    "direction_accuracy": diracc,
                    "majority_baseline": {"majority_class_accuracy": majority},
                    "edge_vs_majority": edge,
                })
    summary = [{
        "symbol": s, "horizon": h,
        "majority_baseline": next((c["majority"] for c in sweep
                                   if c["symbol"] == s and c["pred_len"] == h
                                   and c["baseline"] == "persistence"), None),
    } for s in symbols for h in horizons]
    return {
        "model": "trivial-baseline (persistence + random-walk) counterpoint",
        "reference": "#8607 foundation spin-out (Chronos/Kronos/M15)",
        "terrain_commun": "SPY/TLT/GLD ETF direction, walk-forward 5-fold, identical folds to rungs",
        "device": "cpu",
        "is_trained": False,
        "is_deterministic": True,
        "sweep": sweep,
        "combos": combos,
        "summary": summary,
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Trivial-baseline counterpoint for #8607 (persistence).")
    p.add_argument("--data-dir", default="../datasets/panier", type=str)
    p.add_argument("--symbols", default=",".join(SYMBOLS))
    p.add_argument("--horizons", default=",".join(str(h) for h in HORIZONS))
    p.add_argument("--out", default="results/baselines_zeroshot/results.json")
    args = p.parse_args(argv)

    data_dir = Path(args.data_dir)
    symbols = args.symbols.split(",") if args.symbols else SYMBOLS
    horizons = [int(h) for h in args.horizons.split(",")] if args.horizons else HORIZONS

    doc = run_sweep(data_dir, symbols, horizons)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(doc, indent=2), encoding="utf-8")
    print(f"baselines_zeroshot: {len(doc['sweep'])} configs -> {out_path}")
    # Compact console table
    print(f"\n{'baseline':<14}{'symbol':<6}{'h':>5}{'DirAcc':>9}{'major':>9}{'edge':>9}")
    for c in doc["sweep"]:
        print(f"{c['baseline']:<14}{c['symbol']:<6}{c['pred_len']:>5}"
              f"{c['diracc']:>9.4f}{c['majority']:>9.4f}{c['edge']:>+9.4f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
