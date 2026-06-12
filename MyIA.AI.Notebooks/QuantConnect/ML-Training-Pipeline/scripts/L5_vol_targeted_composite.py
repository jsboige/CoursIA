"""L5: Vol-targeted trend portfolio composite (ladder #1409, rung 5).

Question
--------
Does adding (a) a 12-1 time-series momentum trend filter (best-of L1-L3
family) and (b) a 10% annualised vol-targeting overlay on top of the S7
composite (S3 HMM regime + HAR-RV-J vol conditioning + S4 v2 Ridge
allocation + execution gate) beat S4 v2 alone?

Architecture
------------
RegimeDetector (S3 HMM bull/bear)
    -> VolConditioner (HAR-RV-J inline, 22-day)
    -> RiskWeights (S4 v2 Ridge regime-conditional, vol-tuned alpha)
    -> TrendFilter (12-1 TSMOM per symbol, zero-out negative-momentum legs)
    -> VolTargeting (scale to 10% annualised ex-ante vol, leverage cap 1.0)
    -> ExecutionGate (skip high-cost trades vs trailing turnover)
    -> PortfolioOrders

Fixes vs s7_composite.py
------------------------
s7 computed turnover AFTER assigning new weights to current
(estimate_trade_cost(current, new) with current already == new), so
turnover_history was all zeros: the execution gate never fired
(skip_rate 0.0% on every seed in results/s7_composite/results.json) and
tx costs were effectively zero for both arms. L5 computes turnover
BEFORE the assignment, applies real turnover-based costs to BOTH the
composite and the S4 v2 baseline, and excludes ^VIX from the tradable
weight vector (s7 let the Ridge allocate weight to ^VIX which was then
silently dropped at return time).

Methodology (7 disciplines #1409)
---------------------------------
- Walk-forward 5-fold expanding window (no shuffle)
- Multi-seed block bootstrap (22-day) seeds [0, 1, 7, 42]
- Baselines: S4 v2 alone (primary), equal-weight (secondary)
- Tx costs: 10bps per unit turnover, 50bps stress (same weight path,
  costs recomputed from recorded per-day turnover)
- Anti-FAANG universe: sector + defensive ETFs only
- Deflated Sharpe (Bailey & Lopez de Prado) with N_TRIALS=10
  (conservative count of curriculum/ladder strategy heads tested
  against this baseline family: S1-S7 + L1-L3)
- Gate: delta Sharpe >= +0.10 vs S4 v2 alone, t >= 2.0 across seeds,
  >= 3/4 seeds positive. Verdict: BEATS / NO BEATS / INCONCLUSIVE.

Output
------
- results/l5_vol_targeted/results.json
- results/l5_vol_targeted/verdict.md

Env: system Python or coursia-ml-training (sklearn, statsmodels,
yfinance, numpy, pandas, scipy). CPU only.
"""

from __future__ import annotations

import argparse
import json
import time
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.stats import norm

from s7_composite import (
    BLOCK_SIZE,
    N_SPLITS,
    REFIT_EVERY,
    SYMBOLS,
    TX_COST_BPS,
    TX_COST_STRESS_BPS,
    block_bootstrap,
    classify_vol_regime,
    compute_inv_vol_ridge_weights,
    estimate_trade_cost,
    fit_hmm,
    har_rv_j_forecast,
    load_data,
    predict_regime,
    _max_drawdown,
    _sharpe_ann,
)

SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results" / "l5_vol_targeted"

SEEDS = [0, 1, 7, 42]
TARGET_VOL = 0.10          # 10% annualised (spec #1409 L5)
MAX_LEVERAGE = 1.0         # long-only, no borrowing: vol-targeting can only de-risk
MOM_LOOKBACK = 252         # 12-month momentum
MOM_SKIP = 21              # skip most recent month (12-1 TSMOM)
COV_LOOKBACK = 63          # ex-ante covariance window
GATE_SHARPE_DELTA = 0.10
COST_GATE_K = 1.5
N_TRIALS = 10              # deflated-Sharpe trial count (curriculum + ladder heads)


# ── Trend filter (12-1 TSMOM, best-performing trend family from L1-L3) ──────

def trend_filter(returns_boot: pd.DataFrame, idx: int, weights: dict[str, float]) -> dict[str, float]:
    """Zero out symbols whose 12-1 momentum is negative, renormalise.

    With < MOM_LOOKBACK days of history the filter is inactive.
    If every symbol is filtered out, the portfolio goes to cash (all-zero
    weights — daily return 0 before costs).
    """
    if idx < MOM_LOOKBACK:
        return weights
    window = returns_boot.iloc[idx - MOM_LOOKBACK: idx - MOM_SKIP]
    if len(window) < MOM_LOOKBACK - MOM_SKIP - 5:
        return weights
    mom = (1.0 + window).prod() - 1.0
    filtered = {s: (w if mom.get(s, 0.0) > 0.0 else 0.0) for s, w in weights.items()}
    total = sum(filtered.values())
    if total < 1e-12:
        return {s: 0.0 for s in weights}
    return {s: w / total for s, w in filtered.items()}


# ── Vol targeting overlay ────────────────────────────────────────────────────

def vol_target_scale(
    weights: dict[str, float],
    lookback_data: pd.DataFrame,
    target_vol: float = TARGET_VOL,
    max_leverage: float = MAX_LEVERAGE,
) -> float:
    """Scale factor so ex-ante annualised portfolio vol hits target_vol.

    Ex-ante vol from the trailing COV_LOOKBACK-day sample covariance.
    Scale is capped at max_leverage (1.0 = de-risk only); the unscaled
    remainder sits in cash at 0%.
    """
    syms = [s for s in SYMBOLS if s in lookback_data.columns]
    w = np.array([weights.get(s, 0.0) for s in syms])
    if w.sum() < 1e-12 or len(lookback_data) < 30:
        return 1.0
    cov = lookback_data[syms].cov().values * 252.0
    var_p = float(w @ cov @ w)
    if var_p <= 1e-12:
        return 1.0
    sigma_p = np.sqrt(var_p)
    return float(min(max_leverage, target_vol / sigma_p))


# ── Execution gate (fixed turnover accounting) ───────────────────────────────

def gated_weights(
    current: dict[str, float],
    proposed: dict[str, float],
    turnover_history: list[float],
    k: float = COST_GATE_K,
) -> tuple[dict[str, float], bool]:
    """Skip rebalance if its turnover exceeds k * trailing average turnover.

    Returns (weights_to_hold, skipped). Turnover is evaluated BEFORE any
    assignment (this is the s7 bug fix).
    """
    if len(turnover_history) < 5:
        return proposed, False
    cost = estimate_trade_cost(current, proposed)
    recent = turnover_history[-20:]
    trailing_avg = float(np.mean(recent))
    if trailing_avg > 0 and cost > k * trailing_avg:
        return current, True
    return proposed, False


# ── Strategy arm tracker ─────────────────────────────────────────────────────

class Arm:
    """Tracks one strategy arm: weights, turnover, gross daily returns."""

    def __init__(self, use_gate: bool):
        self.use_gate = use_gate
        self.current = {s: 1.0 / len(SYMBOLS) for s in SYMBOLS}
        # Gating history tracks PROPOSED turnover (not executed): appending
        # the executed 0 on a skipped day drags the trailing average down,
        # which locks the gate shut in a feedback loop (87% skip observed).
        self.proposed_history: list[float] = []
        self.gross_rets: list[float] = []
        self.turnovers: list[float] = []
        self.n_skipped = 0
        self.n_rebalances = 0

    def step(self, proposed: dict[str, float], day_ret: pd.Series) -> None:
        self.proposed_history.append(estimate_trade_cost(self.current, proposed))
        if self.use_gate:
            held, skipped = gated_weights(self.current, proposed, self.proposed_history[:-1])
            if skipped:
                self.n_skipped += 1
        else:
            held = proposed
        turnover = estimate_trade_cost(self.current, held)
        self.n_rebalances += 1
        self.current = held
        ret = sum(
            self.current.get(s, 0.0) * float(day_ret.get(s, 0.0))
            for s in SYMBOLS if s in day_ret.index
        )
        self.gross_rets.append(ret)
        self.turnovers.append(turnover)

    def hold(self, day_ret: pd.Series) -> None:
        """Day without enough lookback: hold current weights, no trade."""
        self.n_rebalances += 1
        ret = sum(
            self.current.get(s, 0.0) * float(day_ret.get(s, 0.0))
            for s in SYMBOLS if s in day_ret.index
        )
        self.gross_rets.append(ret)
        self.turnovers.append(0.0)

    def net(self, tx_bps: int) -> np.ndarray:
        g = np.array(self.gross_rets)
        t = np.array(self.turnovers)
        return g - t * tx_bps / 10000.0


# ── Walk-forward backtest ────────────────────────────────────────────────────

def walk_forward_l5(prices: pd.DataFrame, seed: int, n_splits: int = N_SPLITS) -> dict:
    """Single-pass walk-forward computing all arms; costs derived per bps level."""
    np.random.seed(seed)

    returns = prices[SYMBOLS].pct_change().dropna()
    n = len(returns)
    if n < 300:
        return {"error": "insufficient data"}

    boot_idx = np.sort(block_bootstrap(np.arange(n), BLOCK_SIZE, seed))
    returns_boot = returns.iloc[boot_idx].copy()
    returns_boot.index = returns.index[: len(boot_idx)]

    fold_size = n // (n_splits + 1)
    splits = []
    for k in range(1, n_splits + 1):
        train_end = fold_size * k
        test_end = min(train_end + fold_size, n)
        if test_end - train_end < 20:
            continue
        splits.append((train_end, train_end, test_end))

    arms = {
        "l5": Arm(use_gate=True),          # trend + vol-targeting + gate
        "l5_no_vt": Arm(use_gate=True),    # trend + gate, no vol-targeting
        "l5_vt_only": Arm(use_gate=True),  # vol-targeting + gate, no trend
        "s4v2": Arm(use_gate=False),       # baseline: Ridge, normal vol, no overlays
    }
    eqw_rets: list[float] = []
    vt_scales: list[float] = []

    hmm_res = None
    refit_counter = 0
    vol_forecasts: list[float] = []

    for train_end, test_start, test_end in splits:
        for i in range(test_end - test_start):
            idx = test_start + i
            if idx >= n:
                break

            if refit_counter % REFIT_EVERY == 0 or hmm_res is None:
                spy_ret = returns_boot["SPY"].values[:idx]
                if len(spy_ret) > 60:
                    try:
                        hmm_res = fit_hmm(spy_ret[-252:])
                    except Exception:
                        pass
            refit_counter += 1

            spy_slice = returns_boot["SPY"].values[:idx]
            regime_label, _ = (0, 0.5)
            if hmm_res is not None:
                regime_label, _ = predict_regime(hmm_res, spy_slice[-22:])

            rv_forecast = har_rv_j_forecast(spy_slice[-66:] if len(spy_slice) >= 66 else spy_slice)
            vol_forecasts.append(rv_forecast)
            vol_regime = classify_vol_regime(rv_forecast, vol_forecasts[-66:])

            day_ret = returns_boot.iloc[idx]
            lookback = returns_boot.iloc[max(0, idx - COV_LOOKBACK): idx]

            if len(lookback) >= 20:
                base = compute_inv_vol_ridge_weights(lookback, regime_label, vol_regime)
                base = {s: base.get(s, 0.0) for s in SYMBOLS}

                trended = trend_filter(returns_boot, idx, base)
                scale = vol_target_scale(trended, lookback)
                vt_scales.append(scale)

                arms["l5"].step({s: w * scale for s, w in trended.items()}, day_ret)
                arms["l5_no_vt"].step(trended, day_ret)
                scale_nt = vol_target_scale(base, lookback)
                arms["l5_vt_only"].step({s: w * scale_nt for s, w in base.items()}, day_ret)

                s4 = compute_inv_vol_ridge_weights(lookback, regime_label, "normal")
                arms["s4v2"].step({s: s4.get(s, 0.0) for s in SYMBOLS}, day_ret)
            else:
                for arm in arms.values():
                    arm.hold(day_ret)

            eqw_rets.append(float(np.mean([day_ret.get(s, 0.0) for s in SYMBOLS])))

    if len(arms["l5"].gross_rets) < 30:
        return {"error": "insufficient OOS returns"}

    out: dict = {"seed": seed, "n_obs": len(eqw_rets), "n_folds": len(splits)}
    eq_arr = np.array(eqw_rets)
    out["sharpe_eqw"] = _sharpe_ann(eq_arr)

    for bps_label, bps in (("", TX_COST_BPS), ("_stress", TX_COST_STRESS_BPS)):
        nets = {name: arm.net(bps) for name, arm in arms.items()}
        for name, arr in nets.items():
            out[f"sharpe_{name}{bps_label}"] = _sharpe_ann(arr)
        out[f"delta_vs_s4v2{bps_label}"] = out[f"sharpe_l5{bps_label}"] - out[f"sharpe_s4v2{bps_label}"]

    l5_net = arms["l5"].net(TX_COST_BPS)
    s4_net = arms["s4v2"].net(TX_COST_BPS)
    out["delta_vs_eqw"] = out["sharpe_l5"] - out["sharpe_eqw"]
    out["cum_ret_l5"] = float(np.prod(1 + l5_net) - 1)
    out["cum_ret_s4v2"] = float(np.prod(1 + s4_net) - 1)
    out["max_dd_l5"] = _max_drawdown(l5_net)
    out["max_dd_s4v2"] = _max_drawdown(s4_net)
    out["vol_l5_ann"] = float(np.std(l5_net, ddof=1) * np.sqrt(252))
    out["vol_s4v2_ann"] = float(np.std(s4_net, ddof=1) * np.sqrt(252))
    out["mean_vt_scale"] = float(np.mean(vt_scales)) if vt_scales else 1.0
    out["pct_days_descaled"] = float(np.mean(np.array(vt_scales) < 0.999)) if vt_scales else 0.0
    out["gate_skip_rate"] = arms["l5"].n_skipped / max(arms["l5"].n_rebalances, 1)
    out["mean_turnover_l5"] = float(np.mean(arms["l5"].turnovers))
    out["mean_turnover_s4v2"] = float(np.mean(arms["s4v2"].turnovers))
    out["psr_vs_s4v2"] = probabilistic_sharpe(l5_net, _sharpe_ann(s4_net))
    out["_l5_daily_sharpe"] = float(_sharpe_ann(l5_net) / np.sqrt(252))
    return out


# ── Deflated / probabilistic Sharpe (Bailey & Lopez de Prado 2014) ──────────

def probabilistic_sharpe(returns: np.ndarray, benchmark_sharpe_ann: float) -> float:
    """PSR: probability that the true Sharpe exceeds the benchmark Sharpe."""
    n = len(returns)
    if n < 30:
        return float("nan")
    sr = float(np.mean(returns) / (np.std(returns, ddof=1) + 1e-18))   # daily
    sr0 = benchmark_sharpe_ann / np.sqrt(252)
    from scipy.stats import kurtosis, skew
    g3 = float(skew(returns))
    g4 = float(kurtosis(returns, fisher=False))
    denom = np.sqrt(max(1e-12, 1 - g3 * sr + (g4 - 1) / 4.0 * sr ** 2))
    z = (sr - sr0) * np.sqrt(n - 1) / denom
    return float(norm.cdf(z))


def deflated_sharpe(seed_results: list[dict], n_trials: int = N_TRIALS) -> float:
    """DSR: PSR against the expected max Sharpe of n_trials random trials.

    Trial-variance is estimated from the cross-seed spread of the L5
    daily Sharpe estimates (conservative: seeds are perturbations of one
    strategy, so this understates trial variance and overstates DSR; the
    n_trials count compensates).
    """
    daily_srs = [r["_l5_daily_sharpe"] for r in seed_results]
    if len(daily_srs) < 2:
        return float("nan")
    var_sr = float(np.var(daily_srs, ddof=1))
    if var_sr <= 0:
        return float("nan")
    gamma = 0.5772156649
    sr0 = np.sqrt(var_sr) * (
        (1 - gamma) * norm.ppf(1 - 1.0 / n_trials)
        + gamma * norm.ppf(1 - 1.0 / (n_trials * np.e))
    )
    # PSR of the median-seed daily Sharpe vs this deflation threshold
    sr_med = float(np.median(daily_srs))
    n_obs = int(np.median([r["n_obs"] for r in seed_results]))
    z = (sr_med - sr0) * np.sqrt(n_obs - 1)
    return float(norm.cdf(z))


# ── Main multi-seed runner ───────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(description="L5 vol-targeted composite backtest")
    parser.add_argument("--seeds", default="0,1,7,42")
    parser.add_argument("--dry-run", action="store_true", help="single seed quick check")
    args = parser.parse_args()
    seeds = [int(s) for s in args.seeds.split(",")]
    if args.dry_run:
        seeds = seeds[:1]

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    print("Loading multi-asset data (sectors + defensive ETFs + VIX)...")
    prices = load_data()
    print(f"  {len(prices)} rows, {prices.index[0].date()} to {prices.index[-1].date()}")

    t0 = time.time()
    seed_results = []
    for seed in seeds:
        print(f"Seed {seed}...", end=" ", flush=True)
        t1 = time.time()
        res = walk_forward_l5(prices, seed)
        if "error" in res:
            print(f"ERROR: {res['error']}")
            continue
        seed_results.append(res)
        print(
            f"L5 {res['sharpe_l5']:.4f} vs S4v2 {res['sharpe_s4v2']:.4f} "
            f"(delta {res['delta_vs_s4v2']:+.4f}, vt_scale {res['mean_vt_scale']:.2f}, "
            f"skip {res['gate_skip_rate']:.1%}) [{time.time()-t1:.0f}s]"
        )

    if not seed_results:
        print("No results.")
        return

    deltas = np.array([r["delta_vs_s4v2"] for r in seed_results])
    deltas_stress = np.array([r["delta_vs_s4v2_stress"] for r in seed_results])
    mean_delta = float(np.mean(deltas))
    n_pos = int(np.sum(deltas > 0))
    t_stat = float(mean_delta / (np.std(deltas, ddof=1) / np.sqrt(len(deltas)))) if len(deltas) > 1 and np.std(deltas, ddof=1) > 1e-12 else float("nan")
    dsr = deflated_sharpe(seed_results) if len(seed_results) >= 2 else float("nan")

    beats = (
        mean_delta >= GATE_SHARPE_DELTA
        and n_pos >= 3
        and not np.isnan(t_stat)
        and t_stat >= 2.0
    )
    if beats:
        verdict = "BEATS"
    elif n_pos >= 2 and mean_delta > 0:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"

    summary = {
        "strategy": "L5 vol-targeted trend composite",
        "issue": "#1409 rung L5",
        "date": datetime.now().strftime("%Y-%m-%d %H:%M"),
        "verdict": verdict,
        "gate": f"delta >= +{GATE_SHARPE_DELTA} vs S4v2, t >= 2.0, >= 3/4 seeds positive",
        "mean_delta_vs_s4v2": mean_delta,
        "n_seeds_positive": f"{n_pos}/{len(deltas)}",
        "t_stat": t_stat,
        "deflated_sharpe_prob": dsr,
        "n_trials_dsr": N_TRIALS,
        "mean_delta_stress_50bps": float(np.mean(deltas_stress)),
        "mean_sharpe_l5": float(np.mean([r["sharpe_l5"] for r in seed_results])),
        "mean_sharpe_s4v2": float(np.mean([r["sharpe_s4v2"] for r in seed_results])),
        "mean_sharpe_l5_no_vt": float(np.mean([r["sharpe_l5_no_vt"] for r in seed_results])),
        "mean_sharpe_l5_vt_only": float(np.mean([r["sharpe_l5_vt_only"] for r in seed_results])),
        "mean_sharpe_eqw": float(np.mean([r["sharpe_eqw"] for r in seed_results])),
        "mean_vol_l5_ann": float(np.mean([r["vol_l5_ann"] for r in seed_results])),
        "target_vol": TARGET_VOL,
        "max_leverage": MAX_LEVERAGE,
        "elapsed_sec": round(time.time() - t0, 1),
        "seeds": [{k: v for k, v in r.items() if not k.startswith("_")} for r in seed_results],
    }

    with open(RESULTS_DIR / "results.json", "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)

    lines = [
        "# L5 Vol-Targeted Trend Composite — Verdict",
        "",
        f"**Date**: {summary['date']}  ",
        f"**Verdict**: **{verdict}**  ",
        f"**Gate**: {summary['gate']}",
        "",
        f"- Mean delta Sharpe vs S4 v2: **{mean_delta:+.4f}** (t = {t_stat:.3f})",
        f"- Seeds positive: {n_pos}/{len(deltas)}",
        f"- Deflated Sharpe probability (N={N_TRIALS} trials): {dsr:.4f}" if not np.isnan(dsr) else "- Deflated Sharpe: n/a",
        f"- Stress 50bps mean delta: {float(np.mean(deltas_stress)):+.4f}",
        f"- Mean Sharpe — L5: {summary['mean_sharpe_l5']:.4f} | S4v2: {summary['mean_sharpe_s4v2']:.4f} "
        f"| no-VT: {summary['mean_sharpe_l5_no_vt']:.4f} | VT-only: {summary['mean_sharpe_l5_vt_only']:.4f} "
        f"| EqW: {summary['mean_sharpe_eqw']:.4f}",
        f"- Realised L5 vol (ann): {summary['mean_vol_l5_ann']:.4f} (target {TARGET_VOL})",
        "",
        "Per-seed:",
        "",
        "| seed | L5 | S4v2 | delta | stress delta | vt scale | skip rate |",
        "|------|-----|------|-------|--------------|----------|-----------|",
    ]
    for r in seed_results:
        lines.append(
            f"| {r['seed']} | {r['sharpe_l5']:.4f} | {r['sharpe_s4v2']:.4f} "
            f"| {r['delta_vs_s4v2']:+.4f} | {r['delta_vs_s4v2_stress']:+.4f} "
            f"| {r['mean_vt_scale']:.3f} | {r['gate_skip_rate']:.1%} |"
        )
    (RESULTS_DIR / "verdict.md").write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"\nVERDICT: {verdict} (mean delta {mean_delta:+.4f}, {n_pos}/{len(deltas)} seeds, t={t_stat:.2f}, DSR={dsr:.3f})")
    print(f"Results written to {RESULTS_DIR}")


if __name__ == "__main__":
    main()
