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

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from dm_test import dm_verdict
from bias_metrics import _dm_centered_mse, _mse_decomposition  # noqa: E402
from har_model import HARModel, _make_split_indices
from intraday_loader import load_binance_eth, load_bitstamp_btc
from realized_variance import daily_realized_variance, har_lag_features, realized_variance_to_log

_HMMLEARN_MISSING = "hmmlearn not found. Install with: pip install hmmlearn"

try:
    from hmmlearn.hmm import GaussianHMM
except ImportError:  # pragma: no cover - only taken where hmmlearn is absent
    # Deliberately NOT `sys.exit` at import time: this module is imported by
    # `tests/test_hmm_regime_vol.py`, and a SystemExit raised during pytest
    # collection aborts the whole session with INTERNALERROR -- taking down
    # every other suite in the directory, not just this one. The failure is
    # deferred to the point of use, where it still reports identically for
    # CLI callers (same message, same exit code).
    GaussianHMM = None


def _require_hmmlearn() -> None:
    """Fail with the CLI-identical message when hmmlearn is unavailable."""
    if GaussianHMM is None:
        sys.exit(_HMMLEARN_MISSING)


SEEDS = [0, 7, 42, 99]
HORIZONS = [1, 5, 10]
N_SPLITS = 5
REFIT_EVERY = 22
N_HMM_STATES = 2
RESULTS_DIR = SCRIPTS_DIR / "results"


# `_mse_decomposition` and `_dm_centered_mse` are the canonical bias/precision
# helpers introduced by PR #12742 in `btc_vol.py`. They are duplicated here for
# the reason `btc_m15.py` states verbatim -- "keep this PR self-contained until
# a shared module is extracted (TODO post-merge)" -- with one M5-specific
# reason on top: `btc_vol` imports `dlinear_vol`, which imports `torch` at
# module level. M5 is HMM + OLS and runs on CPU with no deep-learning stack;
# importing it for two pure numpy functions would drag torch into a script that
# does not need it. M5 is now the THIRD duplication site, which is the argument
# for finally extracting them -- filed separately rather than folded in here.
def _is_beats(verdict: str) -> bool:
    """True only for `dm_verdict`'s winning verdict.

    `dm_verdict` emits exactly three strings: "BEATS baseline",
    "BEATEN BY baseline" and "INCONCLUSIVE". A bare `"BEATS" in verdict`
    also matches "BEATEN BY baseline" under a substring test on some
    tokenisations, hence the explicit exclusion kept from the original code.
    """
    return "BEATS" in verdict and "BEATEN" not in verdict


def _is_beaten(verdict: str) -> bool:
    """True only for `dm_verdict`'s losing verdict ("BEATEN BY baseline").

    The mirror of `_is_beats`. "BEATEN" appears in exactly one of the three
    strings `dm_verdict` emits, so no exclusion clause is needed here -- but
    the guard rails of `_is_beats` still apply the other way round: the two
    sentinel verdicts this module adds ("SHAPE_MISMATCH", "INSUFFICIENT_DATA")
    contain neither token and are therefore counted as neither win nor loss.
    """
    return "BEATEN" in verdict


def _aggregate_state(
    n_beats: int,
    n_beaten: int,
    n_seeds: int,
    dm_p_median: float,
    *,
    n_beats_parent: int | None = None,
) -> str:
    """Single state machine shared by the raw and the de-biased (precision) legs.

    Before #14388 the runner carried two aggregation conventions: a raw leg
    with two states ("BEATS" iff 4/4 seeds BEATS, else "INCONCLUSIVE") and a
    de-biased leg with four states (BEATS / NO BEATS / refuted-de-biased /
    INCONCLUSIVE). Two consumers reading the same artefact closed the gap
    manually with different rules; the two configs the doc publishes as
    "NO BEATS on the raw leg" were silently persisted as INCONCLUSIVE, and
    the executable could not reproduce its own published verdict.

    The unified machine is the four-state precedence, decided once here and
    sealed by tests (the raw leg simply never triggers the refuted branch,
    since there is no parent leg above it).

    1. unanimous BEATS + significant median  -> "BEATS"
    2. unanimous BEATEN + significant median -> "NO BEATS"
    3. the parent leg was unanimous BEATS   -> "refuted-de-biased"
    4. otherwise                             -> "INCONCLUSIVE"

    `NO BEATS` deliberately outranks `refuted-de-biased` when both apply (a raw
    win that the precision leg significantly reverses). "Refuted" states that a
    claim was not confirmed; the measurement in that case says more than that --
    it says the model loses. Reporting the weaker of the two would soften a
    measured loss, and the refutation stays legible anyway because every summary
    row prints the raw and the de-biased verdict side by side.

    The significance clause is redundant under unanimity (each per-seed BEATS /
    BEATEN already carries p < alpha, so the median of them does too) and is
    kept explicit only because the pre-existing BEATS branch stated it: an
    asymmetric pair of conditions would read as a deliberate difference.

    `n_seeds == 0` yields "INCONCLUSIVE" rather than a vacuous unanimity.
    `n_beats_parent is None` disables the refuted branch (raw-leg callsite).
    """
    if n_seeds <= 0:
        return "INCONCLUSIVE"
    if n_beats == n_seeds and dm_p_median < 0.05:
        return "BEATS"
    if n_beaten == n_seeds and dm_p_median < 0.05:
        return "NO BEATS"
    if n_beats_parent is not None and n_beats_parent == n_seeds:
        return "refuted-de-biased"
    return "INCONCLUSIVE"


def fit_hmm_regimes(log_rv_train: np.ndarray, seed: int) -> "GaussianHMM":
    """Fit K-state GaussianHMM on log-RV. State 0 = low vol, state 1 = high vol."""
    _require_hmmlearn()
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

    # --- Bias instrumentation (#1454 sub-grain; family pattern of #12742/#12745)
    #
    # `MSE = bias^2 + variance`. A DM on RAW errors therefore answers "which
    # model has the lower loss", NOT "which model is more precise": an edge can
    # be carried entirely by the baseline being miscalibrated. That is not
    # hypothetical here -- #12745 measured `har_bias_oos = -0.227` on BTC
    # against the very same classic-HAR baseline this harness compares to, and
    # the M15 edge did not survive the control (`refuted-de-biased`, #12788).
    #
    # Three legs are persisted, and none of them replaces the published one:
    #   * the signed OOS bias of EACH model (pr-review-discipline §C requires
    #     the bias report for "modele ET baseline"),
    #   * the edge recomputed against the DE-BIASED classic HAR, the §C
    #     interpretation `btc_vol.run_btc_debiased_recentered` uses,
    #   * `dm_centered_*`, the DM on errors centered by their own mean, whose
    #     `d_mean` is a pure variance differential -- the leg that says "more
    #     precise" rather than "better calibrated" (#10961).
    #
    # `dm_statistic` / `dm_p_value` / `dm_verdict` keep their original raw-error
    # meaning so the numbers already published in docs/M5_HMM_REGIME.md stay
    # reproducible and comparable; the control is ADDED beside them, never
    # substituted for them.
    regime_decomp = _mse_decomposition(regime_errors)
    classic_decomp_raw = _mse_decomposition(classic_errors)

    regime_bias_oos = float(np.mean(regime_errors)) if len(truths_arr) else float("nan")
    classic_bias_oos = float(np.mean(classic_errors)) if len(truths_arr) else float("nan")

    # De-biased classic HAR: subtract its own OOS bias from its forecasts.
    # The regime model is left raw -- comparing a raw model to a de-biased
    # baseline is the strict reading of §C (it can only hurt the model).
    classic_errors_debiased = classic_errors - classic_bias_oos
    classic_decomp_debiased = _mse_decomposition(classic_errors_debiased)
    classic_mse_debiased = classic_decomp_debiased["mse"]

    dm_centered = _dm_centered_mse(regime_errors, classic_errors, horizon=horizon)

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
        # --- bias report, per model (§C) ------------------------------------
        "regime_bias_oos": regime_bias_oos,
        "regime_bias_sq": regime_decomp["bias_sq"],
        "regime_variance": regime_decomp["variance"],
        "classic_bias_oos": classic_bias_oos,
        "classic_bias_sq_raw": classic_decomp_raw["bias_sq"],
        "classic_variance_raw": classic_decomp_raw["variance"],
        # --- edge against the DE-BIASED baseline ----------------------------
        "classic_mse_debiased": classic_mse_debiased,
        "classic_bias_sq_debiased": classic_decomp_debiased["bias_sq"],
        "classic_variance_debiased": classic_decomp_debiased["variance"],
        "classic_bias_share_of_mse": (
            classic_decomp_raw["bias_sq"] / classic_mse
            if classic_mse and classic_mse > 0 else float("nan")
        ),
        "mse_reduction_pct_vs_debiased_classic": (
            (classic_mse_debiased - regime_mse) / classic_mse_debiased * 100
            if classic_mse_debiased and classic_mse_debiased > 0 else float("nan")
        ),
        # --- DM on centered errors = variance differential ------------------
        "dm_centered_stat": dm_centered["dm_stat"],
        "dm_centered_pvalue": dm_centered["dm_pvalue"],
        "dm_centered_verdict": dm_centered["dm_verdict"],
        "dm_centered_mean_loss_diff": dm_centered.get("mean_loss_diff", float("nan")),
        # Per-observation series, kept OUT of the JSON (see `--dump-series`):
        # 24 runs x ~1.1k predictions would add ~2 MB to a committed artefact,
        # and the family's artefacts carry decompositions, not series.
        "_series": {
            "dates": [str(pd.Timestamp(d).date()) for d in pred_dates],
            "regime": [float(x) for x in regime_preds],
            "classic": [float(x) for x in classic_preds],
            "target": [float(x) for x in truths_arr],
        },
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


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """CLI so a single (coin, horizon) cell can be re-validated on its own.

    The full grid is 2 coins x 3 horizons x 4 seeds = 24 walk-forward runs.
    Re-auditing one published claim (e.g. the ETH h=1 BEATS) does not need the
    other 20 runs, and forcing them would put a bias re-check out of reach of a
    worker cycle. Defaults reproduce the original full sweep exactly.
    """
    p = argparse.ArgumentParser(description="M5 -- HMM regime-switching HAR vs classic HAR")
    p.add_argument("--coins", nargs="+", default=None,
                   help="subset of coins to run (default: every panel that loads)")
    p.add_argument("--horizons", nargs="+", type=int, default=HORIZONS)
    p.add_argument("--seeds", nargs="+", type=int, default=SEEDS)
    p.add_argument("--out", default=None,
                   help="results JSON path (default: results/m5_hmm_regime.json)")
    p.add_argument("--dump-series", default=None,
                   help="also write the per-observation forecast series to this CSV")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> None:
    args = _parse_args(argv)
    # Fail fast, before loading any data -- same message and exit code as the
    # former import-time guard.
    _require_hmmlearn()
    seeds = list(args.seeds)
    horizons = list(args.horizons)

    print("=" * 70)
    print("M5 -- HMM Regime-Switching HAR vs Classic HAR")
    print(f"Seeds: {seeds}, Horizons: {horizons}, HMM states: {N_HMM_STATES}")
    print(f"Approach: regime-switching (separate HAR per decoded regime)")
    print("=" * 70)

    panels = load_panel()
    if args.coins:
        panels = {c: rv for c, rv in panels.items() if c in set(args.coins)}
    if not panels:
        sys.exit("No data loaded, aborting.")

    t0 = time.time()
    all_results: list[dict] = []
    series_rows: list[dict] = []

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

        for horizon in horizons:
            print(f"\n  h={horizon}:")
            seed_results = []
            for seed in seeds:
                t1 = time.time()
                res = walk_forward_regime_switching(rv, horizon, seed)
                elapsed = time.time() - t1
                tag = "**" if _is_beats(res["dm_verdict"]) else "  "
                ctag = "**" if _is_beats(res["dm_centered_verdict"]) else "  "
                print(
                    f"    seed={seed:2d}: regime_mse={res['regime_mse']:.4f} "
                    f"classic_mse={res['classic_mse']:.4f} "
                    f"reduction={res['mse_reduction_pct']:+.1f}% "
                    f"DM p={res['dm_p_value']:.4f} {tag}{res['dm_verdict']}{tag} "
                    f"({elapsed:.1f}s)"
                )
                print(
                    f"              bias: regime={res['regime_bias_oos']:+.4f} "
                    f"classic={res['classic_bias_oos']:+.4f} "
                    f"(bias^2 = {res['classic_bias_share_of_mse'] * 100:.1f}% of classic MSE) "
                    f"| vs de-biased classic: {res['mse_reduction_pct_vs_debiased_classic']:+.1f}% "
                    f"| DM-centered p={res['dm_centered_pvalue']:.4f} "
                    f"{ctag}{res['dm_centered_verdict']}{ctag}"
                )
                res["coin"] = coin
                series = res.pop("_series")
                if args.dump_series:
                    for d, r_, c_, t_ in zip(
                        series["dates"], series["regime"], series["classic"], series["target"],
                    ):
                        series_rows.append({
                            "coin": coin, "horizon": horizon, "seed": seed,
                            "date": d, "pred_regime": r_, "pred_classic": c_, "target": t_,
                        })
                all_results.append(res)
                seed_results.append(res)

            n_seeds = len(seed_results)
            n_beats = sum(1 for r in seed_results if _is_beats(r["dm_verdict"]))
            n_beats_centered = sum(1 for r in seed_results if _is_beats(r["dm_centered_verdict"]))
            n_beaten_centered = sum(1 for r in seed_results if _is_beaten(r["dm_centered_verdict"]))
            n_beaten = sum(1 for r in seed_results if _is_beaten(r["dm_verdict"]))
            mean_reduction = np.mean([r["mse_reduction_pct"] for r in seed_results])
            mean_reduction_debiased = np.mean(
                [r["mse_reduction_pct_vs_debiased_classic"] for r in seed_results]
            )
            std_reduction = np.std([r["mse_reduction_pct"] for r in seed_results], ddof=0)
            mean_regime_mse = np.mean([r["regime_mse"] for r in seed_results])
            mean_classic_mse = np.mean([r["classic_mse"] for r in seed_results])
            mean_classic_mse_debiased = np.mean([r["classic_mse_debiased"] for r in seed_results])
            dm_p_median = float(np.median([r["dm_p_value"] for r in seed_results]))
            dm_centered_p_median = float(np.median([r["dm_centered_pvalue"] for r in seed_results]))
            # Both legs share the same four-state machine (#14388). The raw
            # leg passes n_beats_parent=None so the refuted-de-biased branch
            # never fires -- there is no parent leg above it.
            agg_verdict = _aggregate_state(
                n_beats=n_beats,
                n_beaten=n_beaten,
                n_seeds=n_seeds,
                dm_p_median=dm_p_median,
            )
            agg_verdict_centered = _aggregate_state(
                n_beats=n_beats_centered,
                n_beaten=n_beaten_centered,
                n_seeds=n_seeds,
                dm_p_median=dm_centered_p_median,
                n_beats_parent=n_beats,
            )
            print(
                f"    >> AGGREGATE: {n_beats}/{n_seeds} seeds beat classic, "
                f"mean reduction={mean_reduction:+.1f}%, "
                f"verdict={agg_verdict}"
            )
            print(
                f"    >> DE-BIASED: {n_beats_centered}/{n_seeds} seeds beat "
                f"({n_beaten_centered}/{n_seeds} beaten) on the precision leg, "
                f"mean reduction vs de-biased classic={mean_reduction_debiased:+.1f}%, "
                f"DM-centered p_median={dm_centered_p_median:.2e}, "
                f"verdict={agg_verdict_centered}"
            )
            all_results.append({
                "coin": coin, "horizon": horizon, "seed": "aggregate",
                "n_seeds": n_seeds,
                "n_beats_seeds": f"{n_beats}/{n_seeds}",
                "mean_regime_mse": float(mean_regime_mse),
                "mean_classic_mse": float(mean_classic_mse),
                "mean_reduction_pct": float(mean_reduction),
                "std_reduction_pct": float(std_reduction),
                "dm_p_median": dm_p_median,
                "aggregate_verdict": agg_verdict,
                # --- de-biased / precision leg (#1454 sub-grain) ------------
                "n_beats_seeds_centered": f"{n_beats_centered}/{n_seeds}",
                # The published tables carry a "seeds BEATEN (rec.)" column;
                # without this field it could not be read back from the artefact.
                "n_beaten_seeds_centered": f"{n_beaten_centered}/{n_seeds}",
                "mean_classic_mse_debiased": float(mean_classic_mse_debiased),
                "mean_reduction_pct_vs_debiased_classic": float(mean_reduction_debiased),
                "dm_centered_p_median": dm_centered_p_median,
                "mean_regime_bias_oos": float(np.mean([r["regime_bias_oos"] for r in seed_results])),
                "mean_classic_bias_oos": float(np.mean([r["classic_bias_oos"] for r in seed_results])),
                "mean_classic_bias_share_of_mse": float(
                    np.mean([r["classic_bias_share_of_mse"] for r in seed_results])
                ),
                "aggregate_verdict_debiased": agg_verdict_centered,
            })

    elapsed_total = time.time() - t0
    print(f"\n{'=' * 70}")
    print(f"Done in {elapsed_total:.0f}s ({elapsed_total / 60:.1f} min)")
    print(f"{'=' * 70}")

    RESULTS_DIR.mkdir(exist_ok=True)
    out_path = Path(args.out) if args.out else RESULTS_DIR / "m5_hmm_regime.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump({
            "experiment": "M5_HMM_REGIME_SWITCHING_HAR",
            "approach": "regime-switching: separate HAR per Viterbi-decoded regime",
            "n_hmm_states": N_HMM_STATES,
            "seeds": seeds,
            "horizons": horizons,
            "n_splits": N_SPLITS,
            "refit_every": REFIT_EVERY,
            "loss_fn": "mse",
            "dm_centered_errors": True,
            "classic_har_debiased": True,
            "elapsed_seconds": elapsed_total,
            "results": all_results,
        }, f, indent=2, default=str)
    print(f"Results saved to {out_path}")

    if args.dump_series:
        series_path = Path(args.dump_series)
        series_path.parent.mkdir(parents=True, exist_ok=True)
        pd.DataFrame(series_rows).to_csv(series_path, index=False)
        print(f"Forecast series ({len(series_rows)} rows) saved to {series_path}")

    print("\n## M5 HMM Regime-Switching HAR Summary")
    header = "| Coin | " + " | ".join(f"h={h}" for h in horizons) + " |"
    print(header)
    print("|" + "---|" * (len(horizons) + 1))
    for coin in panels:
        row = f"| {coin} |"
        for h in horizons:
            agg = next(
                (r for r in all_results
                 if r["coin"] == coin and r["horizon"] == h
                 and r.get("seed") == "aggregate"),
                None,
            )
            if agg:
                # Both verdicts, always: the raw one is what the doc published,
                # the de-biased one is what §C actually asks. Printing only the
                # survivor would hide which of the two moved.
                row += (
                    f" {agg['aggregate_verdict']} ({agg['mean_reduction_pct']:+.1f}%)"
                    f" / de-biased {agg['aggregate_verdict_debiased']}"
                    f" ({agg['mean_reduction_pct_vs_debiased_classic']:+.1f}%) |"
                )
            else:
                row += " -- |"
        print(row)


if __name__ == "__main__":
    main()
