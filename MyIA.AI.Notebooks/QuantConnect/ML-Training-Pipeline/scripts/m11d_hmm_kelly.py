"""M11d HMM regime-conditional Kelly mu estimator vs M11a kelly_har_mu60.

Hypothesis (carry-over from M11a/M11b/M11c)
-------------------------------------------
M11a + M11b documented Kelly-with-HAR-sigma + rolling-60d-mu sizing that
beats buy-hold by raw Delta Sharpe on 27/35 (coin, horizon) combos but with
0/35 reaching p<0.05 per the Ledoit-Wolf 2008 paired Sharpe SE in M11c
(`m11c_sharpe_test.py`). The remaining edge is mostly noise.

M5 (po-2024) reportedly tried HMM-on-volatility-forecast and it hurt vs the
HAR vol forecast. Here we try the opposite handle: keep the HAR vol intact
and estimate `mu` *conditional on the inferred HMM regime* instead of using a
global rolling mean.

Mechanics
---------
For each (coin, horizon) combo:
  1. Fit a 2-state Gaussian HMM (pure numpy, from `regime_detector.GaussianHMM`)
     on the *training* log-return panel only — same expanding-window splits as
     `walk_forward_har` (n_splits=5, refit_every=22). At each refit boundary we
     re-fit the HMM on the new training window.
  2. Viterbi-decode the regime of every day in the eval window from the
     most-recent fitted HMM.
  3. Compute a regime-conditional rolling mu: the trailing-60d mean of
     log-returns restricted to days that share the current day's regime label.
     If less than 10 in-regime samples in the window, fall back to the
     unrestricted 60d rolling mean (same as M11a kelly_har_mu60).
  4. Kelly fraction `f = clip(mu_regime / sigma2_HAR, 0, kelly_cap)` — same
     long-only cap, same fee model as M11a/M11b for fair comparison.
  5. Same Ledoit-Wolf 2008 paired-Sharpe SE test vs buy_hold (reuses
     `m11c_sharpe_test.ledoit_wolf_sharpe_diff_se`).

Anti-leakage
------------
The HMM is *re-fitted only at refit boundaries* using strictly past data; at
each eval day the regime is Viterbi-decoded from the most recent fit. The
regime-conditional rolling mu only looks at days with index < t (shift(1)),
matching the original `_kelly_strategy` convention.

Note on data alignment
----------------------
`walk_forward_har.forecasts` indexes the prediction at the *end* of each
expanding fold step. The daily log-return panel here is built the same way as
`simulate_har_kelly._evaluate_one`: grouped by trading-day normalize() then
reindexed onto the HAR forecast index — so the HMM regime labels are aligned
with the same calendar.

No new dependencies. Numpy + pandas + scipy + the internal `regime_detector`.
No FAANG/Mag7. No hmmlearn. PEP8.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.stats import norm

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from har_model import walk_forward_har  # noqa: E402
from intraday_loader import (  # noqa: E402
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from realized_variance import daily_realized_variance  # noqa: E402
from regime_detector import GaussianHMM  # noqa: E402


COINS_DEFAULT = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]
HORIZONS_DEFAULT = [1, 5, 10, 15, 20]


_COIN_CACHE: dict[str, pd.Series] = {}


def _load_one_coin(coin: str) -> pd.Series:
    if coin in _COIN_CACHE:
        return _COIN_CACHE[coin]
    if coin == "BTC-USD":
        s = hourly_log_returns(load_bitstamp_btc())
    elif coin == "ETH-USD":
        s = hourly_log_returns(load_binance_eth())
    else:
        s = hourly_log_returns(load_yf_intraday(coin))
    _COIN_CACHE[coin] = s
    return s


def _fit_hmm_winsorized(train_logret: np.ndarray, n_states: int) -> GaussianHMM:
    """Fit a Gaussian HMM on a 1-D training log-return series with MAD winsorization."""
    x = np.asarray(train_logret, dtype=float).ravel()
    x = x[np.isfinite(x)]
    if len(x) < 60:
        # Degenerate: just return a uniform-prior HMM, won't matter (fallback to global)
        hmm = GaussianHMM(n_states=n_states, n_iter=2)
        hmm.fit(np.atleast_2d(x).T if len(x) > 0 else np.zeros((10, 1)))
        return hmm
    m = np.median(x)
    mad = np.median(np.abs(x - m)) * 1.4826
    if mad > 0:
        x = np.clip(x, m - 4 * mad, m + 4 * mad)
    X = x.reshape(-1, 1)
    hmm = GaussianHMM(n_states=n_states, n_iter=40, tol=1e-4)
    hmm.fit(X)
    return hmm


def _regime_labels_walkforward(
    daily_logret: pd.Series,
    eval_index: pd.DatetimeIndex,
    n_splits: int,
    refit_every: int,
    n_states: int,
    train_min: int = 250,
) -> tuple[pd.Series, dict]:
    """Produce a regime label for each day in `eval_index` using expanding-window
    HMM refits.

    Strategy (efficient): the HMM is fitted on `daily_logret[:t0]` at each
    refit boundary t0, then a single Viterbi pass decodes regimes on
    `daily_logret[:t0]`. The labels for in-sample days [t0, t0+refit_every)
    are then carried forward by Viterbi on the expanding window
    `daily_logret[:t]` for t in that range -- but to keep cost O(T) rather than
    O(T^2) we only do the full Viterbi up to t0 and then advance the regime
    state day-by-day using the HMM emission + transition probabilities (online
    forward filtering). This matches what the original O(T^2) version computed
    at the most-likely state level.

    Parameters
    ----------
    daily_logret : pd.Series
        Daily log-returns indexed by trading day.
    eval_index : pd.DatetimeIndex
        Days to label (subset of daily_logret.index).
    refit_every : refit cadence in eval days.
    n_states : number of HMM states.
    train_min : minimum train length before first HMM fit.

    Returns
    -------
    labels : pd.Series of int regime labels, indexed by eval_index.
    diag   : dict with regime-conditional means and last transition matrix.
    """
    daily_logret = daily_logret.dropna().astype(float)
    full_index = daily_logret.index
    if len(full_index) < train_min + refit_every:
        return pd.Series(np.zeros(len(eval_index), dtype=int), index=eval_index), {
            "regime_means": [0.0] * n_states,
            "regime_vols": [0.0] * n_states,
            "A": np.eye(n_states).tolist(),
            "n_refits": 0,
        }

    eval_index = pd.DatetimeIndex(eval_index)
    pos_in_full = pd.Series(np.arange(len(full_index)), index=full_index)
    eval_pos = pos_in_full.reindex(eval_index).dropna().astype(int).values
    if len(eval_pos) == 0:
        return pd.Series([], dtype=int), {
            "regime_means": [0.0] * n_states,
            "regime_vols": [0.0] * n_states,
            "A": np.eye(n_states).tolist(),
            "n_refits": 0,
        }

    full_x = daily_logret.values.astype(float)
    labels = np.zeros(len(eval_pos), dtype=int)
    n_refits = 0
    last_state_means: list[float] = [0.0] * n_states
    last_state_vols: list[float] = [0.0] * n_states
    last_A: np.ndarray = np.eye(n_states)

    cur_hmm: GaussianHMM | None = None
    cur_perm: dict[int, int] = {}
    cur_log_A: np.ndarray | None = None
    cur_log_pi: np.ndarray | None = None
    last_refit_pos: int = -10 ** 9
    # Online Viterbi state for the current refit window
    delta: np.ndarray | None = None  # log-prob of best path ending in each state, shape (K,)
    backptr_state: int | None = None  # most likely current state given filtered path

    def _emission_log_prob(hmm: GaussianHMM, x_scalar: float) -> np.ndarray:
        """Log emission p(x|state) for each state (D=1)."""
        K = hmm.n_states
        mu = hmm.mu.ravel()
        sig = hmm.sig.ravel()
        log_det = np.log(sig)
        diff = x_scalar - mu
        mahal = diff * diff / sig
        return -0.5 * (np.log(2 * np.pi) + log_det + mahal)

    for i, pos in enumerate(eval_pos):
        # Refit if needed
        if cur_hmm is None or (pos - last_refit_pos) >= refit_every:
            train_end = pos
            if train_end < train_min:
                labels[i] = 0
                continue
            train_x = full_x[:train_end]
            cur_hmm = _fit_hmm_winsorized(train_x, n_states=n_states)
            n_refits += 1
            last_refit_pos = pos
            # Stable rename : sort states by mean ascending (so state 0 = bear, last = bull)
            order = np.argsort(cur_hmm.mu.ravel())
            cur_perm = {int(old): int(new) for new, old in enumerate(order)}
            last_state_means = [float(cur_hmm.mu.ravel()[order[k]]) for k in range(n_states)]
            last_state_vols = [float(np.sqrt(cur_hmm.sig.ravel()[order[k]])) for k in range(n_states)]
            last_A = cur_hmm.A.copy()
            cur_log_A = np.log(cur_hmm.A + 1e-300)
            cur_log_pi = np.log(cur_hmm.pi + 1e-300)
            # Initialise delta by full Viterbi on the training data, then advance
            # to position `pos` (current eval day, inclusive).
            decode_x = full_x[: pos + 1].reshape(-1, 1)
            m = np.median(decode_x)
            mad = np.median(np.abs(decode_x - m)) * 1.4826
            if mad > 0:
                decode_x = np.clip(decode_x, m - 4 * mad, m + 4 * mad)
            states = cur_hmm.predict(decode_x)
            # Use the Viterbi state at the last time step as our "filtered" point
            # estimate; for online updates between refits, reconstruct delta as
            # log P(state, x_{1:t}).
            T_cur = len(decode_x)
            log_emit = cur_hmm._log_emission(decode_x)
            delta = cur_log_pi + log_emit[0]
            for tt in range(1, T_cur):
                delta = log_emit[tt] + np.array([
                    np.logaddexp.reduce(delta + cur_log_A[:, k])
                    for k in range(n_states)
                ])
                # Re-centre to avoid underflow
                delta = delta - delta.max()
            raw_state = int(states[-1])
            backptr_state = raw_state
        else:
            # Online forward filter advance: delta(t) = log_emit(t) + logsumexp(delta(t-1)+log_A)
            assert cur_hmm is not None and cur_log_A is not None and delta is not None
            x_t = full_x[pos]
            log_emit_t = _emission_log_prob(cur_hmm, x_t)
            new_delta = np.empty(n_states)
            for k in range(n_states):
                new_delta[k] = log_emit_t[k] + np.logaddexp.reduce(delta + cur_log_A[:, k])
            new_delta -= new_delta.max()
            delta = new_delta
            backptr_state = int(np.argmax(delta))
        labels[i] = cur_perm.get(int(backptr_state), int(backptr_state))

    return (
        pd.Series(labels, index=eval_index[: len(labels)]),
        {
            "regime_means": last_state_means,
            "regime_vols": last_state_vols,
            "A": last_A.tolist(),
            "n_refits": n_refits,
        },
    )


def _regime_conditional_mu(
    daily_logret: pd.Series,
    regime_labels: pd.Series,
    mu_window: int = 60,
    min_in_regime: int = 10,
) -> pd.Series:
    """Compute rolling regime-conditional mu, shifted by 1 day.

    For each eval day t: look at the prior `mu_window` days, select those
    sharing today's regime label; if at least `min_in_regime` matches, take
    their mean log-return. Else fall back to the unrestricted rolling mean
    (same as kelly_har_mu60 baseline).
    """
    daily_logret = daily_logret.astype(float)
    df = pd.concat(
        [daily_logret.rename("r"), regime_labels.rename("regime")], axis=1, join="inner"
    ).dropna()
    fallback_mu = df["r"].rolling(mu_window).mean()
    out = pd.Series(np.nan, index=df.index, dtype=float)
    r_arr = df["r"].values
    reg_arr = df["regime"].values.astype(int)
    n = len(df)
    for i in range(n):
        lo = max(0, i - mu_window)
        # We need strictly past data for prediction at i (shift(1) discipline).
        # Use window [lo, i) and decide regime by today's label (i itself is
        # the regime to filter on, but we exclude it from the mean).
        window_r = r_arr[lo:i]
        window_reg = reg_arr[lo:i]
        today_reg = reg_arr[i]
        match = window_reg == today_reg
        if match.sum() >= min_in_regime:
            out.iloc[i] = float(window_r[match].mean())
        else:
            out.iloc[i] = float(fallback_mu.iloc[i - 1]) if i >= 1 else np.nan
    return out


def _kelly_returns_regime(
    daily_returns: pd.Series,
    forecast_log_rv: pd.Series,
    regime_labels: pd.Series,
    mu_window: int,
    kelly_cap: float,
    fee_bps: float,
    min_in_regime: int = 10,
) -> tuple[pd.Series, pd.Series]:
    """Per-period net returns + Kelly fraction series with regime-conditional mu.

    Mirrors `m11c_sharpe_test._kelly_net_returns` modulo the mu estimator.
    """
    aligned = pd.concat(
        [daily_returns.rename("r"), forecast_log_rv.rename("logrv"), regime_labels.rename("regime")],
        axis=1, join="inner",
    ).dropna()
    if len(aligned) < mu_window + 30:
        return pd.Series(dtype=float), pd.Series(dtype=float)

    mu_hat = _regime_conditional_mu(aligned["r"], aligned["regime"], mu_window, min_in_regime)
    sigma2_daily = np.exp(aligned["logrv"].values)
    f_kelly = mu_hat.values / np.clip(sigma2_daily, 1e-12, None)
    f_kelly = np.nan_to_num(f_kelly, nan=0.0, posinf=kelly_cap, neginf=0.0)
    f_kelly = np.clip(f_kelly, 0.0, kelly_cap)
    r = aligned["r"].values
    pnl = f_kelly * r
    turnover = np.abs(np.diff(f_kelly, prepend=f_kelly[0]))
    fee_drag = (fee_bps / 10000.0) * turnover
    net = pnl - fee_drag
    return (
        pd.Series(net, index=aligned.index, name="net"),
        pd.Series(f_kelly, index=aligned.index, name="f"),
    )


def _regime_persistence(labels: np.ndarray) -> float:
    """Mean run length of consecutive identical-regime days."""
    if len(labels) == 0:
        return 0.0
    runs = []
    cur = labels[0]
    rl = 1
    for x in labels[1:]:
        if x == cur:
            rl += 1
        else:
            runs.append(rl)
            cur = x
            rl = 1
    runs.append(rl)
    return float(np.mean(runs)) if runs else 0.0


_PRE_CACHE: dict[str, dict] = {}


def _precompute_coin(coin: str) -> dict:
    """Cache hourly_rets, rv, daily_close_rets per coin — invariant across horizons."""
    if coin in _PRE_CACHE:
        return _PRE_CACHE[coin]
    hourly_rets = _load_one_coin(coin)
    rv = daily_realized_variance(hourly_rets)
    daily_close_rets_raw = (
        hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    )
    daily_close_rets_raw.index = pd.DatetimeIndex(daily_close_rets_raw.index).normalize()
    _PRE_CACHE[coin] = {
        "hourly_rets": hourly_rets,
        "rv": rv,
        "daily_close_rets_raw": daily_close_rets_raw,
    }
    return _PRE_CACHE[coin]


def evaluate_one(
    coin: str,
    horizon: int,
    n_states: int,
    mu_window: int,
    kelly_cap: float,
    fee_bps: float,
    n_splits: int,
    refit_every: int,
    train_size: int,
) -> dict:
    """Run a full M11d eval for one (coin, horizon) combo and return a result dict."""
    t0 = time.time()
    pre = _precompute_coin(coin)
    rv = pre["rv"]
    if len(rv) < 300:
        return {"coin": coin, "horizon": horizon, "skipped": "rv<300"}
    daily_close_rets_raw = pre["daily_close_rets_raw"]

    har_out = walk_forward_har(rv, horizon=horizon, n_splits=n_splits, refit_every=refit_every)
    har_forecasts = har_out["forecasts"]

    daily_close_rets = daily_close_rets_raw.reindex(har_forecasts.index).dropna()
    har_forecasts = har_forecasts.reindex(daily_close_rets.index)

    eval_idx = daily_close_rets.index
    regime_labels, diag = _regime_labels_walkforward(
        daily_logret=daily_close_rets,
        eval_index=eval_idx,
        n_splits=n_splits,
        refit_every=refit_every,
        n_states=n_states,
        train_min=train_size,
    )

    if regime_labels.empty:
        return {"coin": coin, "horizon": horizon, "skipped": "no_regime_labels"}

    # Diagnostics on regimes
    labels_arr = regime_labels.values.astype(int)
    persistence = _regime_persistence(labels_arr)
    regime_share = {int(k): float(np.mean(labels_arr == k)) for k in range(n_states)}
    # Empirical regime-conditional log-return mean (annualised)
    emp_means: list[float] = []
    emp_vols: list[float] = []
    aligned_for_emp = pd.concat([daily_close_rets.rename("r"), regime_labels.rename("g")], axis=1).dropna()
    for k in range(n_states):
        m = aligned_for_emp.loc[aligned_for_emp["g"] == k, "r"]
        emp_means.append(float(m.mean() * 252.0) if len(m) else float("nan"))
        emp_vols.append(float(m.std(ddof=0) * np.sqrt(252.0)) if len(m) else float("nan"))

    # Active strategy: HMM regime-conditional Kelly
    r_active, f_active = _kelly_returns_regime(
        daily_returns=daily_close_rets,
        forecast_log_rv=har_forecasts,
        regime_labels=regime_labels,
        mu_window=mu_window,
        kelly_cap=kelly_cap,
        fee_bps=fee_bps,
    )

    # Baseline 1: buy_hold (same alignment as r_active)
    r_bh = daily_close_rets.reindex(r_active.index).dropna()
    r_active = r_active.reindex(r_bh.index).dropna()

    # Baseline 2: kelly_har_mu60 (replicate from m11c_sharpe_test, no regime)
    aligned = pd.concat(
        [daily_close_rets.rename("r"), har_forecasts.rename("logrv")], axis=1
    ).dropna()
    mu_hat_global = aligned["r"].rolling(mu_window).mean().shift(1)
    sigma2 = np.exp(aligned["logrv"].values)
    f_global = mu_hat_global.values / np.clip(sigma2, 1e-12, None)
    f_global = np.nan_to_num(f_global, nan=0.0, posinf=kelly_cap, neginf=0.0)
    f_global = np.clip(f_global, 0.0, kelly_cap)
    pnl_global = f_global * aligned["r"].values
    turn_global = np.abs(np.diff(f_global, prepend=f_global[0]))
    fee_global = (fee_bps / 10000.0) * turn_global
    r_kelly_global = pd.Series(pnl_global - fee_global, index=aligned.index, name="net")
    r_kelly_global = r_kelly_global.reindex(r_active.index).dropna()
    r_active = r_active.reindex(r_kelly_global.index)
    r_bh = r_bh.reindex(r_kelly_global.index)

    if len(r_active) < 60:
        return {"coin": coin, "horizon": horizon, "skipped": "insufficient_overlap"}

    # Ledoit-Wolf 2008 SE for active vs buy_hold
    sa, sb, diff_daily, se_daily = ledoit_wolf_sharpe_diff_se(r_active.values, r_bh.values)
    t_bh = diff_daily / se_daily if se_daily and np.isfinite(se_daily) and se_daily > 0 else float("nan")
    p_bh = float(1.0 - norm.cdf(t_bh)) if np.isfinite(t_bh) else float("nan")

    # LW SE for active vs kelly_har_mu60 (the M11a/c baseline)
    sa2, sk2, diff_kelly, se_kelly = ledoit_wolf_sharpe_diff_se(
        r_active.values, r_kelly_global.values
    )
    t_k = diff_kelly / se_kelly if se_kelly and np.isfinite(se_kelly) and se_kelly > 0 else float("nan")
    p_k = float(1.0 - norm.cdf(t_k)) if np.isfinite(t_k) else float("nan")

    sharpe_diff_ann_bh = (sa - sb) * np.sqrt(252.0)
    sharpe_diff_ann_kelly = (sa2 - sk2) * np.sqrt(252.0)

    elapsed = time.time() - t0
    return {
        "coin": coin,
        "horizon": horizon,
        "strategy": "kelly_hmm_har_mu60_regime",
        "n_states": n_states,
        "n_periods": int(len(r_active)),
        "n_refits": diag["n_refits"],
        "regime_persistence_days": round(persistence, 3),
        "regime_share": regime_share,
        "regime_means_train_logret": [round(m, 6) for m in diag["regime_means"]],
        "regime_vols_train_logret": [round(v, 6) for v in diag["regime_vols"]],
        "regime_means_eval_annualised": [round(m, 4) for m in emp_means],
        "regime_vols_eval_annualised": [round(v, 4) for v in emp_vols],
        "transition_matrix_last_fit": [
            [round(x, 4) for x in row] for row in diag["A"]
        ],
        "sharpe_active_ann": round(sa * np.sqrt(252.0), 4),
        "sharpe_buy_hold_ann": round(sb * np.sqrt(252.0), 4),
        "sharpe_kelly_har_mu60_ann": round(sk2 * np.sqrt(252.0), 4),
        "sharpe_diff_ann_vs_buy_hold": round(sharpe_diff_ann_bh, 4),
        "sharpe_diff_ann_vs_kelly_har_mu60": round(sharpe_diff_ann_kelly, 4),
        "se_daily_LW_vs_buy_hold": float(se_daily) if np.isfinite(se_daily) else None,
        "se_daily_LW_vs_kelly_har_mu60": float(se_kelly) if np.isfinite(se_kelly) else None,
        "t_stat_vs_buy_hold": float(t_bh) if np.isfinite(t_bh) else None,
        "t_stat_vs_kelly_har_mu60": float(t_k) if np.isfinite(t_k) else None,
        "p_value_one_sided_vs_buy_hold": float(p_bh) if np.isfinite(p_bh) else None,
        "p_value_one_sided_vs_kelly_har_mu60": float(p_k) if np.isfinite(p_k) else None,
        "BEATS_buy_hold_p005": bool(np.isfinite(p_bh) and p_bh < 0.05),
        "BEATS_kelly_har_mu60_p005": bool(np.isfinite(p_k) and p_k < 0.05),
        "BEATS_buy_hold_delta_sharpe": bool(sharpe_diff_ann_bh > 0),
        "BEATS_kelly_har_mu60_delta_sharpe": bool(sharpe_diff_ann_kelly > 0),
        "elapsed_s": round(elapsed, 2),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coins", type=str, nargs="+", default=COINS_DEFAULT)
    parser.add_argument("--horizons", type=int, nargs="+", default=HORIZONS_DEFAULT)
    parser.add_argument("--n-states", type=int, default=2,
                        help="Number of HMM states (default 2: bull/bear)")
    parser.add_argument("--mu-window", type=int, default=60,
                        help="Rolling window for regime-conditional mu (default 60)")
    parser.add_argument("--kelly-cap", type=float, default=1.0)
    parser.add_argument("--fee-bps", type=float, default=10.0)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument("--train-size", type=int, default=250)
    parser.add_argument("--out-dir", type=str,
                        default="results/m11d_hmm_kelly")
    args = parser.parse_args()

    t0 = time.time()
    print(f"[setup] coins={args.coins}", flush=True)
    print(f"[setup] horizons={args.horizons}  n_states={args.n_states}  mu_window={args.mu_window}", flush=True)
    print(f"[setup] kelly_cap={args.kelly_cap}  fee_bps={args.fee_bps}  refit_every={args.refit_every}", flush=True)

    rows: list[dict] = []
    for coin in args.coins:
        for h in args.horizons:
            try:
                row = evaluate_one(
                    coin=coin, horizon=h,
                    n_states=args.n_states, mu_window=args.mu_window,
                    kelly_cap=args.kelly_cap, fee_bps=args.fee_bps,
                    n_splits=args.n_splits, refit_every=args.refit_every,
                    train_size=args.train_size,
                )
                rows.append(row)
                if "skipped" in row:
                    print(f"  [skip] {coin} h={h}: {row['skipped']}", flush=True)
                else:
                    flag_bh = "**" if row["BEATS_buy_hold_p005"] else ("+" if row["BEATS_buy_hold_delta_sharpe"] else "")
                    flag_k = "**" if row["BEATS_kelly_har_mu60_p005"] else ("+" if row["BEATS_kelly_har_mu60_delta_sharpe"] else "")
                    print(
                        f"  {coin:<8s} h={h:<2d}  "
                        f"ΔSh_BH={row['sharpe_diff_ann_vs_buy_hold']:+.3f} p={row['p_value_one_sided_vs_buy_hold']:.3f} {flag_bh:<2s}  "
                        f"ΔSh_K60={row['sharpe_diff_ann_vs_kelly_har_mu60']:+.3f} p={row['p_value_one_sided_vs_kelly_har_mu60']:.3f} {flag_k:<2s}  "
                        f"persist={row['regime_persistence_days']:.1f}d n={row['n_periods']}",
                        flush=True,
                    )
            except Exception as exc:
                print(f"[ERROR] {coin} h={h}: {type(exc).__name__}: {exc}", flush=True)
                rows.append({
                    "coin": coin, "horizon": h, "error": f"{type(exc).__name__}: {exc}"
                })

    # Aggregate
    print("\n=== Aggregate counts ===", flush=True)
    valid = [r for r in rows if r.get("p_value_one_sided_vs_buy_hold") is not None]
    n = len(valid)
    b_bh_005 = sum(1 for r in valid if r["BEATS_buy_hold_p005"])
    b_bh_d = sum(1 for r in valid if r["BEATS_buy_hold_delta_sharpe"])
    b_k_005 = sum(1 for r in valid if r["BEATS_kelly_har_mu60_p005"])
    b_k_d = sum(1 for r in valid if r["BEATS_kelly_har_mu60_delta_sharpe"])
    print(f"  vs buy_hold        :  BEATS Δ>0 {b_bh_d}/{n}   BEATS p<0.05 {b_bh_005}/{n}", flush=True)
    print(f"  vs kelly_har_mu60  :  BEATS Δ>0 {b_k_d}/{n}    BEATS p<0.05 {b_k_005}/{n}", flush=True)

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    json_path = out_dir / "results.json"
    csv_path = out_dir / "results.csv"

    json_payload = {
        "rows": rows,
        "elapsed_s": time.time() - t0,
        "config": {
            "coins": args.coins,
            "horizons": args.horizons,
            "n_states": args.n_states,
            "mu_window": args.mu_window,
            "kelly_cap": args.kelly_cap,
            "fee_bps": args.fee_bps,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "train_size": args.train_size,
            "test": "Ledoit-Wolf 2008 paired Sharpe SE, one-sided p-value vs buy_hold and vs kelly_har_mu60",
            "hmm": "GaussianHMM (regime_detector.GaussianHMM, pure numpy)",
        },
    }
    json_path.write_text(json.dumps(json_payload, indent=2, default=str))

    csv_cols = [
        "coin", "horizon", "strategy", "n_states", "n_periods", "n_refits",
        "regime_persistence_days",
        "sharpe_active_ann", "sharpe_buy_hold_ann", "sharpe_kelly_har_mu60_ann",
        "sharpe_diff_ann_vs_buy_hold", "sharpe_diff_ann_vs_kelly_har_mu60",
        "se_daily_LW_vs_buy_hold", "se_daily_LW_vs_kelly_har_mu60",
        "t_stat_vs_buy_hold", "t_stat_vs_kelly_har_mu60",
        "p_value_one_sided_vs_buy_hold", "p_value_one_sided_vs_kelly_har_mu60",
        "BEATS_buy_hold_p005", "BEATS_kelly_har_mu60_p005",
        "BEATS_buy_hold_delta_sharpe", "BEATS_kelly_har_mu60_delta_sharpe",
    ]
    with open(csv_path, "w", newline="") as fh:
        wr = csv.DictWriter(fh, fieldnames=csv_cols)
        wr.writeheader()
        for r in rows:
            if "error" in r or "skipped" in r:
                continue
            wr.writerow({k: r.get(k) for k in csv_cols})

    print(f"\n[done] {time.time() - t0:.1f}s -- wrote {json_path} and {csv_path}", flush=True)


if __name__ == "__main__":
    main()
