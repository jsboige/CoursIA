"""M5 -- HMM Regime-Switching HAR: Volatility Regime Detection + Conditional Forecasting.

Fits a K-state Gaussian HMM on log-RV to identify volatility regimes, then
uses regime-switching HAR: separate HAR coefficients per regime, with the
current decoded regime selecting which model to use for prediction.

Approach v2 (regime-switching):
- K=2 Gaussian HMM on log-RV (low-vol vs high-vol regime)
- Viterbi-decode the most likely regime at each time step
- Fit separate HAR models for low-vol and high-vol regime days
- At prediction time, use current decoded regime to select the HAR model
- Walk-forward 5-fold expanding window, 4 seeds for HMM init
- DM test vs classic (single) HAR

Coins: BTC-USD (Bitstamp, ~2278 RV days) and ETH-USD (Binance, ~1495 RV days).
Horizons: h=1, 5, 10 days. Seeds: 0, 7, 42, 99.

References:
- Hamilton (1989) "A New Approach to the Economic Analysis of Nonstationary
  Time Series and the Business Cycle", Econometrica 57, 357-384.
- Corsi (2009) "A Simple Approximate Long-Memory Model of Realized Volatility",
  Journal of Financial Econometrics 7, 174-196.
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from dm_test import dm_verdict
from har_model import HARModel, _make_split_indices
from intraday_loader import load_binance_eth, load_bitstamp_btc
from realized_variance import daily_realized_variance, har_lag_features, realized_variance_to_log

try:
    from hmmlearn.hmm import GaussianHMM
except ImportError:
    sys.exit("hmmlearn not found. Install with: pip install hmmlearn")


SEEDS = [0, 7, 42, 99]
HORIZONS = [1, 5, 10]
N_SPLITS = 5
REFIT_EVERY = 22
N_HMM_STATES = 2
RESULTS_DIR = SCRIPTS_DIR / "results"


def fit_hmm_regimes(log_rv_train: np.ndarray, seed: int) -> "GaussianHMM":
    """Fit K-state GaussianHMM on log-RV. State 0 = low vol, state 1 = high vol."""
    model = GaussianHMM(
        n_components=N_HMM_STATES,
        covariance_type="full",
        n_iter=200,
        tol=1e-4,
        random_state=seed,
    )
    X = log_rv_train.reshape(-1, 1)
    model.fit(X)
    if model.means_[0, 0] > model.means_[1, 0]:
        model.means_ = model.means_[::-1]
        model.covars_ = model.covars_[::-1]
        trans = model.transmat_.copy()
        model.transmat_[0] = trans[1]
        model.transmat_[1] = trans[0]
        model.startprob_ = model.startprob_[::-1]
    return model


def decode_viterbi(model: "GaussianHMM", log_rv: np.ndarray) -> np.ndarray:
    """Viterbi-decode most likely state sequence. Returns 0=low, 1=high."""
    X = log_rv.reshape(-1, 1)
    return model.predict(X)


class RegimeSwitchingHAR:
    """HAR with regime dummy and regime x RV interaction terms.

    log RV_{t+h} = b0 + b_d*rv_d + b_w*rv_w + b_m*rv_m
                 + g0 * I(regime=high)
                 + g_d * rv_d * I(regime=high)
                 + g_w * rv_w * I(regime=high)
                 + g_m * rv_m * I(regime=high)
                 + e

    This allows different intercepts and slopes in each regime while
    keeping the temporal structure intact.
    """

    def __init__(self) -> None:
        self.coef_: np.ndarray | None = None

    def fit(self, rv_train: pd.Series, regime_labels: np.ndarray) -> "RegimeSwitchingHAR":
        feats = har_lag_features(rv_train).apply(realized_variance_to_log)
        target = realized_variance_to_log(rv_train).rename("y")
        # regime_labels is aligned to rv_train index
        high_regime = pd.Series(regime_labels == 1, index=rv_train.index, dtype=float)
        df = pd.concat([feats, high_regime.rename("R"), target], axis=1).dropna()
        if len(df) < 30:
            raise ValueError(f"RegimeSwitchingHAR needs >=30 obs, got {len(df)}")

        rv_d = df["rv_d"].values
        rv_w = df["rv_w"].values
        rv_m = df["rv_m"].values
        R = df["R"].values

        # Features: [1, rv_d, rv_w, rv_m, R, rv_d*R, rv_w*R, rv_m*R]
        X = np.column_stack([
            np.ones(len(df)),
            rv_d, rv_w, rv_m,
            R,
            rv_d * R, rv_w * R, rv_m * R,
        ])
        y = df["y"].values
        coef, *_ = np.linalg.lstsq(X, y, rcond=None)
        self.coef_ = coef
        return self

    def predict_h_step(
        self, rv_history: pd.Series, horizon: int, regime_high: bool,
    ) -> float:
        if self.coef_ is None:
            raise RuntimeError("predict before fit")
        R = 1.0 if regime_high else 0.0
        history = list(rv_history.astype(float).values)
        forecasts: list[float] = []
        for _ in range(horizon):
            tail = pd.Series(history[-22:])
            log_rv = np.log(tail.clip(lower=1e-12))
            rv_d = float(log_rv.iloc[-1])
            rv_w = float(log_rv.iloc[-5:].mean())
            rv_m = float(log_rv.iloc[-22:].mean())
            x = np.array([1.0, rv_d, rv_w, rv_m, R, rv_d * R, rv_w * R, rv_m * R])
            log_pred = float(x @ self.coef_)
            forecasts.append(log_pred)
            history.append(float(np.exp(log_pred)))
        return float(np.mean(forecasts))


def walk_forward_regime_switching(
    rv: pd.Series,
    horizon: int,
    seed: int,
    n_splits: int = N_SPLITS,
    refit_every: int = REFIT_EVERY,
) -> dict:
    """Walk-forward evaluation of regime-switching HAR vs classic HAR.

    At each prediction step:
    1. Decode the most likely regime from the HMM
    2. Use the regime-specific HAR model to predict
    3. Compare against a single classic HAR model
    """
    rv = rv.dropna().astype(float)
    n = len(rv)
    if n < 200:
        raise ValueError(f"need >=200 daily obs, got {n}")

    log_rv = np.log(rv.clip(lower=1e-12))
    log_rv_arr = log_rv.values
    splits = _make_split_indices(n, n_splits)

    regime_preds: list[float] = []
    classic_preds: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        if train_end < 60:
            continue

        # Fit HMM on training data
        hmm_model = fit_hmm_regimes(log_rv_arr[:train_end], seed=seed)

        # Decode regimes for training data
        train_labels = decode_viterbi(hmm_model, log_rv_arr[:train_end])

        # Fit regime-switching HAR (interaction terms)
        regime_model = RegimeSwitchingHAR().fit(rv.iloc[:train_end], train_labels)

        # Classic HAR
        classic_model = HARModel().fit(rv.iloc[:train_end])

        # Decode regimes for the test window in advance (Viterbi on train+test)
        # This is O(T) and done once per fold — much more efficient than per-step
        test_labels = decode_viterbi(
            hmm_model, log_rv_arr[:test_end],
        )[test_start:test_end - horizon]

        # Walk forward
        history = list(rv.iloc[:test_start].values)
        last_refit_idx = test_start

        for step_j, i in enumerate(range(test_start, test_end - horizon)):
            target_window = log_rv_arr[i:i + horizon].mean()
            tail = pd.Series(history[-(22 + horizon):])

            # Use the pre-decoded regime label for this test point
            current_regime = int(test_labels[step_j])

            # Regime-switching prediction: use interaction-term HAR
            regime_pred = regime_model.predict_h_step(tail, horizon, regime_high=(current_regime == 1))
            classic_pred = classic_model.predict_h_step(tail, horizon=horizon)

            regime_preds.append(regime_pred)
            classic_preds.append(classic_pred)
            truths.append(float(target_window))
            pred_dates.append(rv.index[i])

            history.append(float(rv.iloc[i]))

            # Periodic refit
            if (i - test_start) % refit_every == 0 and i > test_start:
                hmm_model = fit_hmm_regimes(log_rv_arr[:i], seed=seed)
                expanded_labels = decode_viterbi(hmm_model, log_rv_arr[:i])

                regime_model = RegimeSwitchingHAR().fit(rv.iloc[:i], expanded_labels)
                classic_model = HARModel().fit(rv.iloc[:i])

                # Re-decode remaining test labels from this point forward
                remaining_labels = decode_viterbi(
                    hmm_model, log_rv_arr[:test_end],
                )[(i + 1):test_end - horizon]
                # Patch test_labels from current position onward
                test_labels_list = list(test_labels)
                for k, lbl in enumerate(remaining_labels):
                    if step_j + 1 + k < len(test_labels_list):
                        test_labels_list[step_j + 1 + k] = int(lbl)
                test_labels = np.array(test_labels_list)
                last_refit_idx = i

    regime_preds = np.asarray(regime_preds)
    classic_preds = np.asarray(classic_preds)
    truths_arr = np.asarray(truths)

    regime_mse = float(np.mean((regime_preds - truths_arr) ** 2)) if len(truths_arr) else float("nan")
    classic_mse = float(np.mean((classic_preds - truths_arr) ** 2)) if len(truths_arr) else float("nan")

    regime_errors = regime_preds - truths_arr
    classic_errors = classic_preds - truths_arr
    dm = dm_verdict(regime_errors, classic_errors, horizon=horizon)

    return {
        "seed": seed,
        "horizon": horizon,
        "n_preds": len(truths_arr),
        "regime_mse": regime_mse,
        "classic_mse": classic_mse,
        "mse_reduction_pct": (
            (classic_mse - regime_mse) / classic_mse * 100
            if classic_mse > 0 else 0.0
        ),
        "dm_statistic": dm["dm_statistic"],
        "dm_p_value": dm["p_value"],
        "dm_verdict": dm["verdict"],
    }


def load_panel() -> dict[str, pd.Series]:
    """Load BTC and ETH daily RV series."""
    panels: dict[str, pd.Series] = {}
    try:
        btc = load_bitstamp_btc()
        ret_btc = np.log(btc.df["close"]).diff().dropna()
        rv_btc = daily_realized_variance(ret_btc)
        panels["BTC-USD"] = rv_btc
        print(f"BTC-USD: {len(rv_btc)} RV days ({rv_btc.index[0].date()} to {rv_btc.index[-1].date()})")
    except FileNotFoundError as e:
        print(f"BTC data not found: {e}")

    try:
        eth = load_binance_eth()
        ret_eth = np.log(eth.df["close"]).diff().dropna()
        rv_eth = daily_realized_variance(ret_eth)
        panels["ETH-USD"] = rv_eth
        print(f"ETH-USD: {len(rv_eth)} RV days ({rv_eth.index[0].date()} to {rv_eth.index[-1].date()})")
    except FileNotFoundError as e:
        print(f"ETH data not found: {e}")

    return panels


def main() -> None:
    print("=" * 70)
    print("M5 -- HMM Regime-Switching HAR vs Classic HAR")
    print(f"Seeds: {SEEDS}, Horizons: {HORIZONS}, HMM states: {N_HMM_STATES}")
    print(f"Approach: regime-switching (separate HAR per decoded regime)")
    print("=" * 70)

    panels = load_panel()
    if not panels:
        sys.exit("No data loaded, aborting.")

    t0 = time.time()
    all_results: list[dict] = []

    for coin, rv in panels.items():
        print(f"\n{'=' * 50}")
        print(f"  {coin}  ({len(rv)} RV days)")
        print(f"{'=' * 50}")

        # Quick HMM regime analysis on full data
        log_rv_full = np.log(rv.clip(lower=1e-12)).values
        hmm_full = fit_hmm_regimes(log_rv_full, seed=0)
        labels_full = decode_viterbi(hmm_full, log_rv_full)
        n_low = (labels_full == 0).sum()
        n_high = (labels_full == 1).sum()
        print(f"  HMM regime split (full data): low-vol={n_low} ({n_low/len(labels_full)*100:.0f}%), "
              f"high-vol={n_high} ({n_high/len(labels_full)*100:.0f}%)")
        print(f"  Low-vol mean log-RV: {log_rv_full[labels_full==0].mean():.4f}")
        print(f"  High-vol mean log-RV: {log_rv_full[labels_full==1].mean():.4f}")

        for horizon in HORIZONS:
            print(f"\n  h={horizon}:")
            seed_results = []
            for seed in SEEDS:
                t1 = time.time()
                res = walk_forward_regime_switching(rv, horizon, seed)
                elapsed = time.time() - t1
                tag = "**" if "BEATS" in res["dm_verdict"] and "BEATEN" not in res["dm_verdict"] else "  "
                print(
                    f"    seed={seed:2d}: regime_mse={res['regime_mse']:.4f} "
                    f"classic_mse={res['classic_mse']:.4f} "
                    f"reduction={res['mse_reduction_pct']:+.1f}% "
                    f"DM p={res['dm_p_value']:.4f} {tag}{res['dm_verdict']}{tag} "
                    f"({elapsed:.1f}s)"
                )
                res["coin"] = coin
                all_results.append(res)
                seed_results.append(res)

            n_beats = sum(1 for r in seed_results if "BEATS" in r["dm_verdict"] and "BEATEN" not in r["dm_verdict"])
            mean_reduction = np.mean([r["mse_reduction_pct"] for r in seed_results])
            mean_regime_mse = np.mean([r["regime_mse"] for r in seed_results])
            mean_classic_mse = np.mean([r["classic_mse"] for r in seed_results])
            agg_verdict = "BEATS" if n_beats == len(SEEDS) else "INCONCLUSIVE"
            print(
                f"    >> AGGREGATE: {n_beats}/{len(SEEDS)} seeds beat classic, "
                f"mean reduction={mean_reduction:+.1f}%, "
                f"verdict={agg_verdict}"
            )
            all_results.append({
                "coin": coin, "horizon": horizon, "seed": "aggregate",
                "n_beats_seeds": f"{n_beats}/{len(SEEDS)}",
                "mean_regime_mse": float(mean_regime_mse),
                "mean_classic_mse": float(mean_classic_mse),
                "mean_reduction_pct": float(mean_reduction),
                "aggregate_verdict": agg_verdict,
            })

    elapsed_total = time.time() - t0
    print(f"\n{'=' * 70}")
    print(f"Done in {elapsed_total:.0f}s ({elapsed_total / 60:.1f} min)")
    print(f"{'=' * 70}")

    RESULTS_DIR.mkdir(exist_ok=True)
    out_path = RESULTS_DIR / "m5_hmm_regime.json"
    with open(out_path, "w") as f:
        json.dump({
            "experiment": "M5_HMM_REGIME_SWITCHING_HAR",
            "approach": "regime-switching: separate HAR per Viterbi-decoded regime",
            "n_hmm_states": N_HMM_STATES,
            "seeds": SEEDS,
            "horizons": HORIZONS,
            "n_splits": N_SPLITS,
            "refit_every": REFIT_EVERY,
            "elapsed_seconds": elapsed_total,
            "results": all_results,
        }, f, indent=2, default=str)
    print(f"Results saved to {out_path}")

    print("\n## M5 HMM Regime-Switching HAR Summary")
    print("| Coin | h=1 | h=5 | h=10 |")
    print("|------|-----|-----|------|")
    for coin in panels:
        row = f"| {coin} |"
        for h in HORIZONS:
            agg = next(
                (r for r in all_results
                 if r["coin"] == coin and r["horizon"] == h
                 and r.get("seed") == "aggregate"),
                None,
            )
            if agg:
                v = agg["aggregate_verdict"]
                red = agg["mean_reduction_pct"]
                row += f" {v} ({red:+.1f}%) |"
            else:
                row += " -- |"
        print(row)


if __name__ == "__main__":
    main()
