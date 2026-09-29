"""M11a HAR-RV + Kelly + vol-targeting per-coin simulation.

Consumes HAR walk-forward forecasts (same pipeline as `train_har_baseline.py`)
and translates them into trading-relevant economic metrics:

1. **Vol-targeted Sharpe** (Fleming-Kirby-Ostdiek 2001): scale position size
   to achieve a target portfolio vol. Compares HAR forecast vs naive-30d
   forecast vs perfect-foresight RV.
2. **Kelly fraction** (Thorp 1969 / Kelly 1956): f* = mu / sigma^2 with capped
   leverage. Uses HAR sigma forecast + rolling realised mu estimator. Fee-aware.
3. **Equal-weight buy-and-hold** baseline.

Per-coin walk-forward simulation with the same expanding-window splits as the
HAR fits (n_splits=5, refit_every=22). Multi-seed not applicable (HAR is OLS,
deterministic). For Kelly mu estimation we run a small bootstrap robustness
check (4 mu-window settings) instead of seeds.

Timing convention (audited 2026-09-24, guarded by tests):
- A HAR forecast indexed at date i is computed from RV history STRICTLY
  before i (see ``paired_walk_forward_har``); it targets the mean log-RV over
  days [i, i+h-1]. The oracle arm averages the SAME window.
- The strategy weight for day i derives from that forecast (information as of
  the close of day i-1) and is applied to the close(i-1) -> close(i) daily
  return r_i, with fees charged on |w_i - w_{i-1}|. Kelly's mu_hat at day i
  uses returns up to i-1 only (``.shift(1)``). What the tests PROVE is
  information-flow causality (weights depend only on information available
  before the return they earn — see test_simulate_har_kelly_debias). Fill
  quality at the daily boundary (close vs open, slippage on 24h crypto
  liquidity) is NOT modeled beyond the fee term: a stated assumption, not a
  measured claim.

Debias replay (--debias, 2026-09-24, Epic #1454): paired three-arm
raw-vs-calibrated comparison — see ``paired_walk_forward_har``. Layer
discipline: forecast-layer DM-MSE measures forecast PRECISION; economic rows
(Sharpe / delta_sharpe_vs_bh) are reported separately and never constitute a
§C BEATS claim on their own.

Usage:
    python -u simulate_har_kelly.py \\
        --horizons 5 \\
        --extra-coins LTC-USD XRP-USD ADA-USD DOT-USD SOL-USD \\
        --target-vol 0.15 \\
        --kelly-cap 1.0 \\
        --fee-bps 10 \\
        --out-json results/m11a_har_kelly_simulation/results.json

Output structure (one row per (coin, horizon, strategy[, variant])):
    coin, horizon, strategy, variant, n_periods, sharpe, delta_sharpe_vs_bh,
    ann_return, ann_vol, max_drawdown, turnover, gross_pnl_per_year
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

from dm_test import dm_verdict
from garch_rolling_baseline import naive_constant_baseline
from har_model import (
    HARModel,
    _fit_har_with_train_calibration,
    _make_split_indices,
    walk_forward_har,
)
from intraday_loader import (
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from realized_variance import daily_realized_variance

ARMS = ("hist_raw", "fit_raw", "adjusted")


def _load_panel(
    skip_remote: bool, extra_coins: list[str] | None = None
) -> tuple[dict[str, pd.Series], list[dict], dict[str, str]]:
    """Load the data panel.

    Returns (panel, provenance, unavailable):
    - panel: coin -> hourly log-returns Series
    - provenance: one record per coin (source, window, n obs, as-of) so any
      replay states exactly WHICH data it ran on. Remote coins are LIVE
      fetches as of run time -- they are NOT the 2026-05 M11b panel, and any
      comparison with the historical 27/35 counts is non-like-for-like.
    - unavailable: coin -> reason for every expected-but-missing source
      (fail-closed sweep consumes this; missing combos are never silent).
    """
    import datetime as _dt

    fetched_at = _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds")
    out: dict[str, pd.Series] = {}
    provenance: list[dict] = []
    unavailable: dict[str, str] = {}

    def _record(coin: str, source: str, rets: pd.Series) -> None:
        out[coin] = rets
        provenance.append({
            "coin": coin,
            "source": source,
            "n_hourly": int(len(rets)),
            "first": str(rets.index[0]),
            "last": str(rets.index[-1]),
            "as_of": fetched_at,
            "immutable_local_file": source in ("bitstamp", "binance"),
            "note": (
                "fixed local file" if source in ("bitstamp", "binance")
                else "LIVE yfinance fetch (period=730d) -- NOT the 2026-05 M11b panel"
            ),
        })

    print("[load] BTC Bitstamp 1h ...", flush=True)
    try:
        btc = load_bitstamp_btc()
        _record("BTC-USD", "bitstamp", hourly_log_returns(btc))
        print(f"  BTC hourly returns: {len(out['BTC-USD'])} obs", flush=True)
    except Exception as exc:
        unavailable["BTC-USD"] = f"bitstamp load failed: {exc.__class__.__name__}: {exc}"
        print(f"[WARN] BTC unavailable: {unavailable['BTC-USD']}", flush=True)
    print("[load] ETH Binance 1h ...", flush=True)
    try:
        eth = load_binance_eth()
        _record("ETH-USD", "binance", hourly_log_returns(eth))
        print(f"  ETH hourly returns: {len(out['ETH-USD'])} obs", flush=True)
    except Exception as exc:
        unavailable["ETH-USD"] = f"binance load failed: {exc.__class__.__name__}: {exc}"
        print(f"[WARN] ETH unavailable: {unavailable['ETH-USD']}", flush=True)
    remote = ["SOL-USD"] + (extra_coins or [])
    for ticker in remote:
        if skip_remote:
            unavailable[ticker] = "skipped by --skip-remote"
            continue
        try:
            print(f"[load] {ticker} yfinance 1h (730d) ...", flush=True)
            ds = load_yf_intraday(ticker)
            _record(ticker, "yfinance", hourly_log_returns(ds))
            print(f"  {ticker} hourly returns: {len(out[ticker])} obs", flush=True)
        except Exception as exc:
            unavailable[ticker] = f"yfinance fetch failed: {exc.__class__.__name__}: {exc}"
            print(f"[WARN] {ticker} unavailable: {unavailable[ticker]}", flush=True)
    return out, provenance, unavailable


def paired_walk_forward_har(
    rv: pd.Series,
    horizon: int,
    n_splits: int = 5,
    refit_every: int = 22,
    calibration_size: int = 60,
) -> dict:
    """Single walk-forward pass producing THREE paired forecast arms.

    All arms share identical OOS dates, identical split/refit schedule
    (``_make_split_indices`` + refit every ``refit_every`` exactly as
    ``walk_forward_har``), so any difference between two arms is attributable
    to exactly one intervention:

    - ``hist_raw``   : full-train-window fit, no offset. Bit-identical to
                       ``walk_forward_har(calibrate_bias=False)`` — the
                       historical M11a/M11b configuration.
    - ``fit_raw``    : calibration fit (train minus the ``calibration_size``
                       tail), NO offset.
    - ``adjusted``   : same calibration fit minus its train-tail signed bias.
                       Bit-identical to ``walk_forward_har(calibrate_bias=True)``.

    Method note (2026-09-24): ``fit_raw`` vs ``adjusted`` share the SAME fit
    sample — their difference isolates the pure offset effect (causal debias
    effect). ``hist_raw`` vs ``adjusted`` changes BOTH the fit sample and the
    offset; it is reported as a separate, explicitly conflated arm, never as
    the causal effect.

    No leakage: the prediction indexed at date i (target window [i, i+h)) is
    computed from RV history strictly before i; the train-tail calibration of
    each refit uses training data only.
    """
    rv = rv.dropna().astype(float)
    n = len(rv)
    if n < 200:
        raise ValueError(f"need >=200 daily obs, got {n}")
    log_rv = np.log(rv.clip(lower=1e-12))
    splits = _make_split_indices(n, n_splits)
    hist_raw: list[float] = []
    fit_raw: list[float] = []
    adjusted: list[float] = []
    bias_by_pred: list[float] = []
    truths: list[float] = []
    pred_dates: list[pd.Timestamp] = []
    n_refits = 0
    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        if train_end < 60:
            continue
        segment_train = rv.iloc[:train_end]
        full_model = HARModel().fit(segment_train)
        cal_model, bias = _fit_har_with_train_calibration(
            segment_train, horizon=horizon, calibration_size=calibration_size,
        )
        history = list(rv.iloc[:test_start].values)
        for i in range(test_start, test_end - horizon):
            target_window = log_rv.iloc[i:i + horizon].mean()
            tail = pd.Series(history[-(22 + horizon):])
            hist_raw.append(full_model.predict_h_step(tail, horizon=horizon))
            cal_pred = cal_model.predict_h_step(tail, horizon=horizon)
            fit_raw.append(cal_pred)
            adjusted.append(cal_pred - bias)
            bias_by_pred.append(bias)
            truths.append(float(target_window))
            pred_dates.append(rv.index[i])
            history.append(float(rv.iloc[i]))
            if (i - test_start) % refit_every == 0 and i > test_start:
                segment_train = rv.iloc[:i]
                full_model = HARModel().fit(segment_train)
                cal_model, bias = _fit_har_with_train_calibration(
                    segment_train, horizon=horizon, calibration_size=calibration_size,
                )
                n_refits += 1
    idx = pd.DatetimeIndex(pred_dates)
    return {
        "horizon": horizon,
        "n_splits": n_splits,
        "calibration_size": calibration_size,
        "refit_every": refit_every,
        "n_refits": n_refits,
        "oos_dates": idx,
        "hist_raw": pd.Series(hist_raw, index=idx, name="hist_raw"),
        "fit_raw": pd.Series(fit_raw, index=idx, name="fit_raw"),
        "adjusted": pd.Series(adjusted, index=idx, name="adjusted"),
        "bias_by_pred": np.asarray(bias_by_pred),
        "targets": pd.Series(truths, index=idx, name="target"),
    }


def _forecast_layer_stats(
    label: str, preds: pd.Series, targets: pd.Series
) -> dict:
    """Signed bias / MAE / MSE of one forecast arm on the paired OOS window."""
    aligned = pd.concat([preds.rename("p"), targets.rename("t")], axis=1).dropna()
    e = aligned["p"].values - aligned["t"].values
    return {
        "arm": label,
        "layer": "forecast",
        "n_oos": int(len(e)),
        "mean_error": round(float(np.mean(e)), 6),
        "mae": round(float(np.mean(np.abs(e))), 6),
        "mse": round(float(np.mean(e ** 2)), 6),
    }


def validate_debias_sweep(
    expected_coins: list[str],
    horizons: list[int],
    rows: list[dict],
    unavailable: dict[str, str],
    mu_windows: list[int],
) -> tuple[list[dict], list[str]]:
    """Fail-closed sweep contract for the debias replay.

    Every expected (coin, horizon) combo must either (a) carry the full set of
    paired rows — buy_hold, vol_target_har and each kelly_har_mu{w} under all
    three arms {hist_raw, fit_raw, adjusted} — or (b) be explicitly attributed
    to an unavailable source. Anything else is a contract violation: returned
    as problems; the caller must exit non-zero on any.
    """
    produced: dict[tuple[str, int, str, str], int] = {}
    for r in rows:
        if "error" in r or r.get("skipped"):
            continue
        key = (r["coin"], r["horizon"], r["strategy"], r.get("variant", "hist_raw"))
        produced[key] = produced.get(key, 0) + 1
    problems: list[str] = []
    missing: list[dict] = []
    # Duplicates are data-integrity violations: fail loudly, never average them.
    for key, count in sorted(produced.items()):
        if count > 1:
            problems.append(f"duplicate row x{count}: {key}")
    # A row only counts as produced if it is non-degenerate: finite Sharpe and
    # n_periods > 0 (coordinator review 2026-09-24: presence alone is not
    # completeness).
    def _valid(coin: str, h: int, strategy: str, arm: str) -> bool:
        hits = [r for r in rows
                if r.get("coin") == coin and r.get("horizon") == h
                and r.get("strategy") == strategy and r.get("variant", "hist_raw") == arm
                and "error" not in r and not r.get("skipped")]
        if len(hits) != 1:
            return False
        sharpe = hits[0].get("sharpe")
        n_periods = hits[0].get("n_periods", 0)
        return (sharpe is not None and np.isfinite(sharpe) and n_periods > 0)

    for coin in expected_coins:
        for h in horizons:
            if coin in unavailable:
                missing.append({
                    "coin": coin, "horizon": h,
                    "reason": f"source unavailable: {unavailable[coin]}",
                })
                continue
            need = {("buy_hold", "hist_raw")}
            need |= {("vol_target_har", a) for a in ARMS}
            need |= {(f"kelly_har_mu{w}", a) for w in mu_windows for a in ARMS}
            gaps = [f"{s}/{a}" for (s, a) in sorted(need)
                    if not _valid(coin, h, s, a)]
            if gaps:
                problems.append(f"{coin} h={h}: missing/degenerate {len(gaps)} paired rows: {gaps[:6]}...")
    return missing, problems


def _equity_curve(returns: np.ndarray) -> tuple[float, float, float, float, float, float]:
    """Compute Sharpe, ann_return, ann_vol, max_drawdown, gross_pnl_per_year, hit_rate
    from a daily-return series."""
    n = len(returns)
    if n < 20:
        return (float("nan"),) * 6
    eq = np.cumprod(1.0 + returns)
    peaks = np.maximum.accumulate(eq)
    dd = (eq - peaks) / peaks
    max_dd = float(dd.min())
    mu = float(np.mean(returns))
    sd = float(np.std(returns, ddof=1))
    ann_ret = mu * 252.0
    ann_vol = sd * np.sqrt(252.0)
    sharpe = ann_ret / ann_vol if ann_vol > 1e-10 else 0.0
    gross_pnl_per_year = float(eq[-1] ** (252.0 / n) - 1.0) if eq[-1] > 0 else float("nan")
    hit_rate = float(np.mean(returns > 0))
    return sharpe, ann_ret, ann_vol, max_dd, gross_pnl_per_year, hit_rate


def _vol_target_strategy(
    daily_returns: pd.Series,
    forecast_log_rv: pd.Series,
    target_vol: float,
    fee_bps: float,
    max_leverage: float = 4.0,
) -> dict:
    """Vol-targeting: position weight = target_vol / forecast_vol_annual.

    Daily return: w * r_market - fee * |w_t - w_{t-1}|.
    """
    aligned = pd.concat([daily_returns.rename("r"), forecast_log_rv.rename("logrv")], axis=1).dropna()
    if len(aligned) < 30:
        return {"sharpe": float("nan"), "n_periods": 0}
    forecast_var_daily = np.exp(aligned["logrv"].values)
    forecast_vol_daily = np.sqrt(np.clip(forecast_var_daily, 1e-12, None))
    forecast_vol_annual = forecast_vol_daily * np.sqrt(252.0)
    weights = target_vol / np.clip(forecast_vol_annual, 0.01, None)
    weights = np.clip(weights, 0.0, max_leverage)
    r = aligned["r"].values
    pnl = weights * r
    turnover = np.abs(np.diff(weights, prepend=weights[0]))
    fee_drag = (fee_bps / 10000.0) * turnover
    net = pnl - fee_drag
    sharpe, ann_ret, ann_vol, max_dd, growth, hit = _equity_curve(net)
    return {
        "n_periods": int(len(net)),
        "sharpe": round(sharpe, 4),
        "ann_return": round(ann_ret, 6),
        "ann_vol": round(ann_vol, 6),
        "max_drawdown": round(max_dd, 6),
        "growth_pa": round(growth, 6),
        "hit_rate": round(hit, 4),
        "avg_weight": round(float(np.mean(weights)), 4),
        "avg_turnover": round(float(np.mean(turnover)), 6),
    }


def _kelly_strategy(
    daily_returns: pd.Series,
    forecast_log_rv: pd.Series,
    mu_window: int,
    kelly_cap: float,
    fee_bps: float,
    include_net: bool = False,
) -> dict:
    """Fractional Kelly: f_t = clip(mu_hat_t / sigma2_t, 0, kelly_cap).

    mu_hat: trailing rolling mean of daily returns over `mu_window` days
    (shifted 1: mu at day t uses returns up to t-1 only).
    sigma2: forecast (next-period log-RV from HAR -> exp -> daily variance).
    Long-only, fees deducted on weight changes.
    ``include_net=True`` additionally exposes the net return / weight arrays
    (test-only causality guards; never persisted in sweep rows).
    """
    aligned = pd.concat([daily_returns.rename("r"), forecast_log_rv.rename("logrv")], axis=1).dropna()
    if len(aligned) < mu_window + 30:
        return {"sharpe": float("nan"), "n_periods": 0}
    mu_hat = aligned["r"].rolling(mu_window).mean().shift(1)
    sigma2_daily = np.exp(aligned["logrv"].values)
    f_kelly = mu_hat.values / np.clip(sigma2_daily, 1e-12, None)
    f_kelly = np.nan_to_num(f_kelly, nan=0.0, posinf=kelly_cap, neginf=0.0)
    f_kelly = np.clip(f_kelly, 0.0, kelly_cap)
    r = aligned["r"].values
    pnl = f_kelly * r
    turnover = np.abs(np.diff(f_kelly, prepend=f_kelly[0]))
    fee_drag = (fee_bps / 10000.0) * turnover
    net = pnl - fee_drag
    sharpe, ann_ret, ann_vol, max_dd, growth, hit = _equity_curve(net)
    out = {
        "n_periods": int(len(net)),
        "sharpe": round(sharpe, 4),
        "ann_return": round(ann_ret, 6),
        "ann_vol": round(ann_vol, 6),
        "max_drawdown": round(max_dd, 6),
        "growth_pa": round(growth, 6),
        "hit_rate": round(hit, 4),
        "avg_weight": round(float(np.mean(f_kelly)), 4),
        "avg_turnover": round(float(np.mean(turnover)), 6),
    }
    if include_net:
        out["_net_returns"] = net.tolist()
        out["_weights"] = f_kelly.tolist()
        out["_index"] = [str(ts) for ts in aligned.index]
    return out


def _buy_hold_strategy(daily_returns: pd.Series) -> dict:
    r = daily_returns.dropna().values
    if len(r) < 20:
        return {"sharpe": float("nan"), "n_periods": 0}
    sharpe, ann_ret, ann_vol, max_dd, growth, hit = _equity_curve(r)
    return {
        "n_periods": int(len(r)),
        "sharpe": round(sharpe, 4),
        "ann_return": round(ann_ret, 6),
        "ann_vol": round(ann_vol, 6),
        "max_drawdown": round(max_dd, 6),
        "growth_pa": round(growth, 6),
        "hit_rate": round(hit, 4),
        "avg_weight": 1.0,
        "avg_turnover": 0.0,
    }


def _annotate_kelly_deltas(
    k: dict, daily_close_rets: pd.Series, mu_window: int, bh_sharpe_full: float
) -> None:
    """Attach support-disclosure deltas to a Kelly strategy row (2026-09-24).

    ``_kelly_strategy`` carries a ``mu_window``-day zero-weight warmup (mu_hat
    is shifted), while ``buy_hold`` spans the full OOS window. Two deltas are
    reported so the support question is never silent:
    - ``delta_sharpe_vs_bh``: full-window Kelly Sharpe minus full-window
      buy_hold Sharpe — same dates on both sides, the historical M11 protocol
      (Kelly's warmup days count as zero-weight days).
    - ``delta_sharpe_vs_bh_matched``: Kelly Sharpe recomputed on the net
      return series EXCLUDING the warmup rows, minus buy_hold Sharpe on the
      IDENTICAL dates — genuinely paired post-warmup supports (coordinator
      review 2026-09-24: a full-window Kelly Sharpe against a post-warmup
      buy_hold is not a matched comparison).
    """
    k["warmup_days"] = int(mu_window)
    k["delta_sharpe_vs_bh"] = (
        round(float(k["sharpe"]) - float(bh_sharpe_full), 4) if k.get("n_periods") else float("nan")
    )
    net = k.pop("_net_returns", None)
    k.pop("_weights", None)
    idx = k.pop("_index", None)
    if net is None or idx is None or len(net) <= mu_window:
        k["kelly_sharpe_postwarmup"] = float("nan")
        k["bh_sharpe_matched"] = float("nan")
        k["delta_sharpe_vs_bh_matched"] = float("nan")
        return
    post_net = np.asarray(net[mu_window:], dtype=float)
    post_idx = pd.DatetimeIndex(idx[mu_window:])
    kelly_post = _equity_curve(post_net)[0]
    bh_post_rets = daily_close_rets.reindex(post_idx).dropna()
    bh_m = _buy_hold_strategy(bh_post_rets)
    k["kelly_sharpe_postwarmup"] = round(float(kelly_post), 4)
    k["bh_sharpe_matched"] = bh_m.get("sharpe", float("nan"))
    k["delta_sharpe_vs_bh_matched"] = (
        round(float(kelly_post) - float(bh_m["sharpe"]), 4)
        if bh_m.get("n_periods") else float("nan")
    )


def _evaluate_one(
    coin: str,
    hourly_rets: pd.Series,
    horizon: int,
    target_vol: float,
    kelly_cap: float,
    fee_bps: float,
    mu_windows: list[int],
    n_splits: int,
    refit_every: int,
    train_size: int,
    debias: bool = False,
    calibration_size: int = 60,
) -> tuple[list[dict], list[dict], "pd.DataFrame | None"]:
    """Evaluate one (coin, horizon).

    debias=False: legacy single-arm behaviour (variant "hist_raw" on every row).
    debias=True: paired three-arm replay (see ``paired_walk_forward_har``):
    every strategy is run under {hist_raw, fit_raw, adjusted}; forecast-layer
    signed bias / MAE / MSE per arm plus DM tests are returned separately.

    Layer discipline (2026-09-24): DM-MSE on forecasts measures predictive
    PRECISION of the volatility forecasts — it says nothing by itself about
    the Kelly strategy net Sharpe vs buy_hold. Economic rows (Sharpe,
    delta_sharpe_vs_bh) and forecast rows (layer="forecast") are reported as
    separate layers; no §C "BEATS" verdict is emitted from the economic layer
    alone.
    """
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return ([{"coin": coin, "horizon": horizon, "skipped": "rv<300"}], [], None)
    print(f"\n[{coin} h={horizon}] RV days: {len(rv)} ({rv.index[0].date()} -> {rv.index[-1].date()})", flush=True)

    if debias:
        paired = paired_walk_forward_har(
            rv, horizon=horizon, n_splits=n_splits, refit_every=refit_every,
            calibration_size=calibration_size,
        )
        base_forecasts = paired["hist_raw"]
        forecasts_by_arm = {a: paired[a] for a in ARMS}
        print(f"  paired forecasts: {len(base_forecasts)} OOS points, "
              f"{paired['n_refits']} refits", flush=True)
    else:
        har_out = walk_forward_har(rv, horizon=horizon, n_splits=n_splits, refit_every=refit_every)
        base_forecasts = har_out["forecasts"]  # log-RV mean-of-h prediction
        forecasts_by_arm = None
        print(f"  HAR forecasts: {len(base_forecasts)} predictions", flush=True)

    # Daily returns aligned by trading-day index
    daily_close_rets = (
        hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    )
    daily_close_rets.index = pd.DatetimeIndex(daily_close_rets.index).normalize()
    daily_close_rets = daily_close_rets.reindex(base_forecasts.index).dropna()
    if debias:
        forecasts_by_arm = {a: s.reindex(daily_close_rets.index) for a, s in forecasts_by_arm.items()}
        targets = paired["targets"].reindex(daily_close_rets.index)
    else:
        base_forecasts = base_forecasts.reindex(daily_close_rets.index)

    # Naive-30d log-RV baseline (in same units)
    try:
        naive = naive_constant_baseline(rv, horizon=horizon, train_size=train_size, refit_every=refit_every)
        naive_log = np.log(naive.clip(lower=1e-12))
        naive_log = naive_log.reindex(daily_close_rets.index).dropna()
    except Exception as exc:
        print(f"  Naive baseline FAILED: {exc}", flush=True)
        naive_log = None

    # Perfect foresight (oracle arm). HISTORICAL NOTE: the original code used
    # .shift(-horizon), which targets days [i+1..i+h] whereas the HAR forecast
    # truth is [i..i+h-1] — an off-by-one. The fix (shift -(h-1)) is applied
    # ONLY in the debias replay so the legacy path stays bit-reproducible with
    # the historical M11a/M11b outputs (coordinator review, 2026-09-24).
    _oracle_shift = -(horizon - 1) if debias else -horizon
    realised_log_rv = (
        np.log(rv.clip(lower=1e-12)).rolling(horizon).mean().shift(_oracle_shift)
    ).reindex(daily_close_rets.index)

    rows: list[dict] = []
    forecast_stats: list[dict] = []

    def _push(res: dict, strategy: str, variant: str, **extra) -> None:
        res.update({"coin": coin, "horizon": horizon, "strategy": strategy,
                    "variant": variant})
        res.update(extra)
        rows.append(res)

    # 1. Buy-and-hold (forecast-independent)
    bh = _buy_hold_strategy(daily_close_rets)
    bh_sharpe = bh.get("sharpe", float("nan"))
    _push(bh, "buy_hold", "hist_raw")

    if debias:
        for arm in ARMS:
            f = forecasts_by_arm[arm]
            vt = _vol_target_strategy(daily_close_rets, f, target_vol, fee_bps)
            vt["delta_sharpe_vs_bh"] = round(float(vt["sharpe"]) - float(bh_sharpe), 4) if vt.get("n_periods") else float("nan")
            _push(vt, "vol_target_har", arm, target_vol=target_vol, fee_bps=fee_bps)
            for w in mu_windows:
                k = _kelly_strategy(daily_close_rets, f, w, kelly_cap, fee_bps, include_net=True)
                _annotate_kelly_deltas(k, daily_close_rets, w, bh_sharpe)
                _push(k, f"kelly_har_mu{w}", arm, kelly_cap=kelly_cap, fee_bps=fee_bps, mu_window=w)
        # Forecast layer: signed bias / MAE / MSE per arm + DM tests.
        # Error arrays are aligned on the SAME dates across all arms/naive.
        # Every row carries coin/horizon so a multi-coin aggregate JSON stays
        # attributable (coordinator review 2026-09-24).
        for arm in ARMS:
            arm_stat = _forecast_layer_stats(arm, forecasts_by_arm[arm], targets)
            arm_stat["coin"] = coin
            arm_stat["horizon"] = horizon
            forecast_stats.append(arm_stat)
        common = pd.concat([
            forecasts_by_arm["adjusted"].rename("a"),
            forecasts_by_arm["fit_raw"].rename("f"),
            forecasts_by_arm["hist_raw"].rename("h"),
            targets.rename("t"),
        ], axis=1).dropna()
        e_adj = (common["a"] - common["t"]).values
        e_fit = (common["f"] - common["t"]).values
        e_hist = (common["h"] - common["t"]).values
        dm_causal = dm_verdict(e_adj, e_fit, horizon=horizon, loss_fn="mse")
        dm_vs_hist = dm_verdict(e_adj, e_hist, horizon=horizon, loss_fn="mse")
        forecast_stats.append({
            "coin": coin, "horizon": horizon, "layer": "forecast",
            "test": "dm_mse_adjusted_vs_fit_raw",
            "interpretation": "causal offset effect: same fit sample, offset only",
            "n": int(len(e_adj)), **{k: (round(v, 6) if isinstance(v, float) else v)
                                      for k, v in dm_causal.items()},
        })
        forecast_stats.append({
            "coin": coin, "horizon": horizon, "layer": "forecast",
            "test": "dm_mse_adjusted_vs_hist_raw",
            "interpretation": "CONFLATED (fit sample AND offset both differ) — link to historical M11 config, not the causal effect",
            "n": int(len(e_adj)), **{k: (round(v, 6) if isinstance(v, float) else v)
                                      for k, v in dm_vs_hist.items()},
        })
        if naive_log is not None and len(naive_log) >= 30:
            e_naive = (naive_log.reindex(common.index) - common["t"]).dropna().values
            keep = ~(np.isnan((naive_log.reindex(common.index) - common["t"]).values))
            dm_vs_naive = dm_verdict(e_adj[keep], e_naive, horizon=horizon, loss_fn="mse")
            forecast_stats.append({
                "coin": coin, "horizon": horizon, "layer": "forecast",
                "test": "dm_mse_adjusted_vs_naive30",
                "interpretation": "precision vs naive-30d volatility baseline",
                "n": int(len(e_naive)), **{k: (round(v, 6) if isinstance(v, float) else v)
                                           for k, v in dm_vs_naive.items()},
            })
        series_frame = pd.DataFrame({
            "date": daily_close_rets.index,
            "daily_return": daily_close_rets.values,
            "target_logrv": targets.values,
            **{a: forecasts_by_arm[a].values for a in ARMS},
        })
    else:
        series_frame = None
        vt_har = _vol_target_strategy(daily_close_rets, base_forecasts, target_vol, fee_bps)
        vt_har["delta_sharpe_vs_bh"] = round(float(vt_har["sharpe"]) - float(bh_sharpe), 4) if vt_har.get("n_periods") else float("nan")
        _push(vt_har, "vol_target_har", "hist_raw", target_vol=target_vol, fee_bps=fee_bps)

        if naive_log is not None and len(naive_log) >= 30:
            vt_naive = _vol_target_strategy(daily_close_rets, naive_log, target_vol, fee_bps)
            _push(vt_naive, "vol_target_naive30", "hist_raw", target_vol=target_vol, fee_bps=fee_bps)

        vt_oracle = _vol_target_strategy(daily_close_rets, realised_log_rv, target_vol, fee_bps)
        _push(vt_oracle, "vol_target_oracle", "hist_raw", target_vol=target_vol, fee_bps=fee_bps)

        for w in mu_windows:
            k_har = _kelly_strategy(daily_close_rets, base_forecasts, w, kelly_cap, fee_bps, include_net=True)
            _annotate_kelly_deltas(k_har, daily_close_rets, w, bh_sharpe)
            _push(k_har, f"kelly_har_mu{w}", "hist_raw", kelly_cap=kelly_cap, fee_bps=fee_bps, mu_window=w)

        if naive_log is not None and len(naive_log) >= 30:
            w_central = mu_windows[len(mu_windows) // 2]
            k_naive = _kelly_strategy(daily_close_rets, naive_log, w_central, kelly_cap, fee_bps)
            _push(k_naive, f"kelly_naive30_mu{w_central}", "hist_raw",
                  kelly_cap=kelly_cap, fee_bps=fee_bps, mu_window=w_central)

    # Oracle in debias mode too (forecast-independent upper bound, one row)
    if debias:
        vt_oracle = _vol_target_strategy(daily_close_rets, realised_log_rv, target_vol, fee_bps)
        _push(vt_oracle, "vol_target_oracle", "hist_raw", target_vol=target_vol, fee_bps=fee_bps)
        if naive_log is not None and len(naive_log) >= 30:
            vt_naive = _vol_target_strategy(daily_close_rets, naive_log, target_vol, fee_bps)
            _push(vt_naive, "vol_target_naive30", "hist_raw", target_vol=target_vol, fee_bps=fee_bps)

    for row in rows:
        if row.get("sharpe") is not None and not (isinstance(row.get("sharpe"), float) and np.isnan(row["sharpe"])):
            print(f"  {row['strategy']:22s} [{row.get('variant','-'):9s}] Sharpe={row.get('sharpe',float('nan')):+.3f}  "
                  f"dSharpe_vs_BH={row.get('delta_sharpe_vs_bh',float('nan')):+.3f}  "
                  f"MaxDD={row.get('max_drawdown',float('nan')):+.4f}  "
                  f"n={row.get('n_periods',0)}", flush=True)
    return rows, forecast_stats, series_frame


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizons", type=int, nargs="+", default=[5])
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--train-size", type=int, default=250)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument("--target-vol", type=float, default=0.15,
                        help="Target annualized portfolio vol for vol-targeting")
    parser.add_argument("--kelly-cap", type=float, default=1.0,
                        help="Maximum Kelly fraction (long-only, no short)")
    parser.add_argument("--fee-bps", type=float, default=10.0,
                        help="Per-side rebalance fee in bps (10bps = 0.10% per turnover unit)")
    parser.add_argument("--mu-windows", type=int, nargs="+", default=[60, 120, 250],
                        help="Rolling mu estimation windows (days) for Kelly robustness")
    parser.add_argument("--skip-remote", action="store_true")
    parser.add_argument("--extra-coins", type=str, nargs="*", default=None)
    parser.add_argument("--out-json", type=str, default="results/m11a_har_kelly_simulation/results.json")
    parser.add_argument("--debias", action="store_true",
                        help="Paired three-arm replay (hist_raw / fit_raw / adjusted); "
                             "see paired_walk_forward_har for the method note")
    parser.add_argument("--calibration-size", type=int, default=60,
                        help="Train-tail calibration window (obs) for the debias arm")
    parser.add_argument("--series-dir", type=str, default=None,
                        help="Directory OUTSIDE the repo for full OOS series CSVs "
                             "(results-artifact-policy: repo keeps only aggregates)")
    parser.add_argument("--expect-coins", type=str, nargs="*", default=None,
                        help="Coins expected in the sweep (default: BTC/ETH + remote list). "
                             "Fail-closed: every expected combo is produced or explicitly missing")
    args = parser.parse_args()

    t0 = time.time()
    print(f"[setup] target_vol={args.target_vol}  kelly_cap={args.kelly_cap}  fee_bps={args.fee_bps}  "
          f"mu_windows={args.mu_windows}  horizons={args.horizons}  debias={args.debias}  "
          f"calibration_size={args.calibration_size if args.debias else 'n/a'}", flush=True)
    panel, provenance, unavailable = _load_panel(args.skip_remote, extra_coins=args.extra_coins)
    expected_coins = args.expect_coins or (
        ["BTC-USD", "ETH-USD"] + ["SOL-USD"] + (args.extra_coins or []))
    if not panel:
        print("[FATAL] no data source loaded — nothing to replay", flush=True)
        sys.exit(2)

    rows: list[dict] = []
    forecast_stats: list[dict] = []
    n_series = 0
    series_dir = Path(args.series_dir) if args.series_dir else None
    if series_dir and args.debias:
        series_dir.mkdir(parents=True, exist_ok=True)
    for coin, rets in panel.items():
        for h in args.horizons:
            try:
                c_rows, c_stats, c_series = _evaluate_one(
                    coin=coin,
                    hourly_rets=rets,
                    horizon=h,
                    target_vol=args.target_vol,
                    kelly_cap=args.kelly_cap,
                    fee_bps=args.fee_bps,
                    mu_windows=args.mu_windows,
                    n_splits=args.n_splits,
                    refit_every=args.refit_every,
                    train_size=args.train_size,
                    debias=args.debias,
                    calibration_size=args.calibration_size,
                )
                rows.extend(c_rows)
                forecast_stats.extend(c_stats)
                if c_series is not None and series_dir is not None:
                    fp = series_dir / f"{coin.replace('-', '_')}_h{h}.csv"
                    c_series.to_csv(fp, index=False)
                    n_series += 1
            except Exception as exc:
                print(f"[ERROR] {coin} h={h}: {exc.__class__.__name__}: {exc}", flush=True)
                rows.append({"coin": coin, "horizon": h, "error": f"{exc.__class__.__name__}: {exc}"})

    missing_combos: list[dict] = []
    problems: list[str] = []
    if args.debias:
        missing_combos, problems = validate_debias_sweep(
            expected_coins, args.horizons, rows, unavailable, args.mu_windows)

    out_df = pd.DataFrame(rows)
    print("\n=== M11 HAR + Kelly + vol-target — full table ===", flush=True)
    if "sharpe" in out_df.columns:
        cols = ["coin", "horizon", "strategy", "variant", "sharpe", "delta_sharpe_vs_bh",
                "ann_return", "ann_vol", "max_drawdown", "avg_weight", "avg_turnover", "n_periods"]
        cols = [c for c in cols if c in out_df.columns]
        print(out_df[cols].to_string(index=False), flush=True)

    payload = {
        "rows": rows,
        "forecast_stats": forecast_stats,
        "provenance": provenance,
        "unavailable_sources": unavailable,
        "missing_combos": missing_combos,
        "sweep_problems": problems,
        "config": {
            "target_vol": args.target_vol,
            "kelly_cap": args.kelly_cap,
            "fee_bps": args.fee_bps,
            "mu_windows": args.mu_windows,
            "horizons": args.horizons,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "train_size": args.train_size,
            "debias": args.debias,
            "calibration_size": args.calibration_size if args.debias else None,
            "expected_coins": expected_coins,
        },
        "caveats": [
            "Economic layer (Sharpe, delta_sharpe_vs_bh, sign-test) is NOT a §C BEATS "
            "claim; DM-MSE forecast tests measure forecast precision only (2026-09-24).",
            "Remote coins are LIVE yfinance fetches as of run time — NOT the 2026-05 "
            "M11b panel; any comparison with the historical 27/35 is non-like-for-like.",
            "adjusted vs fit_raw = causal offset effect; adjusted vs hist_raw conflates "
            "fit sample and offset.",
            "Kelly rows carry a mu_window-day zero-weight warmup: "
            "delta_sharpe_vs_bh uses the FULL-window buy_hold (historical M11 "
            "protocol, unpaired support); delta_sharpe_vs_bh_matched uses the "
            "post-warmup buy_hold support. Both are reported; neither is a §C "
            "claim.",
        ],
        "elapsed_s": time.time() - t0,
    }
    out_text = json.dumps(payload, indent=2, default=str)
    if len(out_text.encode("utf-8")) >= 512_000:
        print(f"[FATAL] aggregate JSON would be {len(out_text.encode('utf-8'))} bytes "
              f"(policy limit 512000) — refusing to write; reduce persisted fields", flush=True)
        sys.exit(3)
    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(out_text, encoding="utf-8")
    print(f"\n[done] {time.time() - t0:.1f}s — wrote {out_path} "
          f"({len(out_text.encode('utf-8'))} bytes, {n_series} series CSVs "
          f"{'-> ' + str(series_dir) if series_dir else '(none)'})", flush=True)
    if missing_combos:
        print(f"[report] {len(missing_combos)} combos explicitly missing "
              f"(unavailable sources): {sorted({m['coin'] for m in missing_combos})}", flush=True)
    if problems:
        print("[FATAL] sweep contract violated — missing/degenerate/duplicate rows:", flush=True)
        for p in problems:
            print(f"  - {p}", flush=True)
        sys.exit(1)
    if missing_combos:
        # PARTIAL: every gap is attributed to an unavailable source (nothing
        # silent), but the declared panel was NOT fully replayed. A full-panel
        # invocation must surface this with a non-zero exit; an intentional
        # partial replay declares --expect-coins limited to loadable sources
        # and exits 0 (coordinator review 2026-09-24).
        print(f"[sweep] PARTIAL — {len(missing_combos)}/{len(expected_coins) * len(args.horizons)} "
              f"expected combos missing (sources unavailable); exit 4", flush=True)
        sys.exit(4)
    print("[sweep] contract COMPLETE — all expected combos produced", flush=True)


if __name__ == "__main__":
    main()
