"""S3 HMM Regime Detection — MarkovRegime 2-state on SPY+TLT+VIX.

Question
--------
Does regime-aware allocation (bull/bear switching) beat 50/50 SPY-TLT Buy-and-Hold?
Two variants:
  1. Daily frequency — MarkovRegression on daily returns
  2. Long-horizon — weekly aggregated returns for macro cycles

Methodology (causal, fix #21633)
--------------------------------
- statsmodels MarkovRegression 2-regime on SPY returns + TLT returns + VIX level
- CAUSAL walk-forward: for each day t the model is fitted on the expanding
  window [0, t) (strictly past) and refit every REFIT_EVERY days; the regime
  is read in the last training day's (filtered) probability and the regimes are
  named on the training window. A one-day decision lag is applied.
  (The previous version fitted the HMM on the block it labelled, read Kim
  smoothed probabilities, and named regimes on the block mean — in-sample.)
- Block bootstrap of the training slice (seed-dependent) for multi-seed
  variability — a real resampling, not a boundary jitter.
- Regime-aware allocation: bull -> 100% SPY, bear -> 100% TLT
- Verdict: Ledoit-Wolf (HAC) delta-Sharpe + Holm vs 50/50 rebalanced and
  SPY held (significance organ, #21329/#21633); an in-sample replay is kept as
  a leak witness (the future-read share of the old edge).

Output
------
- results/s3_hmm_regime/daily/results.json
- results/s3_hmm_regime/long_horizon/results.json
- results/s3_hmm_regime/verdict.md

Env: system Python 3.13. statsmodels, yfinance, numpy, pandas.
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

import strategy_metrics
import hmm_regime_significance as hmm_sig

SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results" / "s3_hmm_regime"

SYMBOLS = {"equity": "SPY", "bond": "TLT", "vol": "^VIX"}
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
REFIT_EVERY = 22
OOS_YEAR = 2027
TX_COST_BPS = 10
GATE_SHARPE_DELTA = 0.20
N_REGIMES = 2
BLOCK_SIZE = 22  # block bootstrap size (1 month trading days)
HMM_MIN_TRAIN = 126  # min training days before the first causal fit


# ── Data loading ─────────────────────────────────────────────────────────────

def load_data(start: str = "2017-01-01", end: str = "2026-12-31") -> pd.DataFrame:
    """Load SPY, TLT, VIX daily data via yfinance."""
    import yfinance as yf

    frames = {}
    for label, sym in SYMBOLS.items():
        df = yf.download(sym, start=start, end=end, progress=False)
        if df.empty:
            raise RuntimeError(f"No data for {sym}")
        if isinstance(df.columns, pd.MultiIndex):
            close = df[("Close", sym)]
        else:
            close = df["Close"]
        frames[label] = close

    out = pd.DataFrame(frames)
    out.index = pd.to_datetime(out.index)
    out.columns = ["spy_close", "tlt_close", "vix_close"]
    out = out.dropna()
    out["spy_ret"] = out["spy_close"].pct_change()
    out["tlt_ret"] = out["tlt_close"].pct_change()
    out["vix_level"] = out["vix_close"]
    return out.dropna()


def resample_weekly(df: pd.DataFrame) -> pd.DataFrame:
    """Resample to weekly frequency."""
    resampled = df.resample("W").agg({
        "spy_close": "last",
        "tlt_close": "last",
        "vix_close": "last",
    }).dropna()
    resampled["spy_ret"] = resampled["spy_close"].pct_change()
    resampled["tlt_ret"] = resampled["tlt_close"].pct_change()
    resampled["vix_level"] = resampled["vix_close"]
    return resampled.dropna()


# ── Block bootstrap ──────────────────────────────────────────────────────────

def block_bootstrap(
    data: np.ndarray,
    block_size: int,
    seed: int,
) -> np.ndarray:
    """Block bootstrap resampling for time-series preserving local structure."""
    rng = np.random.RandomState(seed)
    n = len(data)
    n_blocks = (n + block_size - 1) // block_size
    indices = []
    for _ in range(n_blocks):
        start = rng.randint(0, n - block_size + 1)
        indices.extend(range(start, min(start + block_size, n)))
    indices = indices[:n]
    return data[indices]


# ── HMM regime detection ─────────────────────────────────────────────────────

def fit_markov_regime(
    spy_ret: np.ndarray,
    tlt_ret: np.ndarray,
    vix_level: np.ndarray,
    seed: int = 0,
    use_bootstrap: bool = False,
    block_size: int = BLOCK_SIZE,
    n_regimes: int = N_REGIMES,
) -> dict:
    """Fit MarkovRegression 2-regime model and return regime labels + metadata.

    If use_bootstrap=True, resamples training data with block bootstrap
    (seed-dependent) for multi-seed variability.
    """
    from statsmodels.tsa.regime_switching.markov_regression import MarkovRegression

    if use_bootstrap:
        spy_ret = block_bootstrap(spy_ret, block_size, seed)
        tlt_ret = block_bootstrap(tlt_ret, block_size, seed)
        vix_level = block_bootstrap(vix_level, block_size, seed)

    # Normalize VIX for numerical stability
    vix_norm = (vix_level - vix_level.mean()) / (vix_level.std() + 1e-8)
    exog = np.column_stack([tlt_ret, vix_norm])

    try:
        mod = MarkovRegression(
            spy_ret,
            k_regimes=n_regimes,
            exog=exog,
            switching_variance=True,
        )
        res = mod.search_em_restarts(
            n_restarts=4,
            seed=seed,
            maxiter=200,
            tol=1e-6,
        )
        if res is None or not res.mle_retvals.get("converged", False):
            res = mod.fit(disp=False, maxiter=300)
    except Exception:
        try:
            mod = MarkovRegression(
                spy_ret,
                k_regimes=n_regimes,
                switching_variance=True,
            )
            res = mod.fit(disp=False, maxiter=300)
        except Exception as e:
            return {
                "labels": np.zeros(len(spy_ret), dtype=int),
                "smoothed_probs": np.ones((len(spy_ret), n_regimes)) / n_regimes,
                "transition_matrix": np.array([[0.95, 0.05], [0.05, 0.95]]),
                "converged": False,
                "error": str(e),
            }

    smoothed = res.smoothed_marginal_probabilities
    labels = np.argmax(smoothed, axis=1)

    # Name regimes: higher mean return = bull (0), lower = bear (1)
    regime_means = []
    for k in range(n_regimes):
        mask = labels == k
        regime_means.append(spy_ret[mask].mean() if mask.sum() > 0 else 0.0)

    # Relabel: bull=0 (higher return), bear=1 (lower return)
    if regime_means[0] < regime_means[1]:
        labels = 1 - labels
        smoothed = smoothed[:, [1, 0]]

    # Transition matrix
    try:
        tm = np.zeros((n_regimes, n_regimes))
        for i in range(n_regimes):
            p_stay = res.params.get(f"p[{i}->{i}]", 0.95)
            tm[i, i] = p_stay
            tm[i, 1 - i] = 1.0 - p_stay
        tm = tm / tm.sum(axis=1, keepdims=True)
    except Exception:
        tm = np.array([[0.95, 0.05], [0.05, 0.95]])

    return {
        "labels": labels,
        "smoothed_probs": smoothed,
        "transition_matrix": tm,
        "converged": True,
        "regime_means": regime_means,
        "log_likelihood": float(res.llf) if hasattr(res, "llf") else None,
    }


# ── Causal regime inference (fix #21633) ────────────────────────────────────

def _causal_regime_probabilities(
    df: pd.DataFrame,
    seed: int = 0,
) -> np.ndarray:
    """Causal bull-regime probability per day.

    For each day t the HMM is fitted on the expanding window ``[0, t)``
    (strictly past) and refit every ``REFIT_EVERY`` days. Between refits the
    probability of the last training day (a filtered value: it conditions only
    on data up to t-1) is held constant. Regimes are named on the training
    window (higher mean SPY return = bull), never on the day being scored.

    Seed variability comes from a block-bootstrap resampling of the TRAINING
    slice (protocol #21633 point 6: a real resampling, not a boundary jitter),
    so the cross-seed spread is honest.
    """
    n = len(df)
    spy_ret = df["spy_ret"].values
    tlt_ret = df["tlt_ret"].values
    vix = df["vix_level"].values

    p_bull = np.full(n, 0.5)
    last_fit = -1
    cached = 0.5
    for t in range(HMM_MIN_TRAIN, n):
        if (t - last_fit) >= REFIT_EVERY or last_fit < 0:
            sr, tr, vl = spy_ret[:t], tlt_ret[:t], vix[:t]
            if seed != 0:
                sr = block_bootstrap(sr, BLOCK_SIZE, seed)
                tr = block_bootstrap(tr, BLOCK_SIZE, seed)
                vl = block_bootstrap(vl, BLOCK_SIZE, seed)
            res = fit_markov_regime(sr, tr, vl, seed=seed)
            if res.get("converged", False):
                sm = res["smoothed_probs"]
                lab = np.argmax(sm, axis=1)
                means = [
                    sr[lab == k].mean() if (lab == k).sum() > 0 else 0.0
                    for k in range(N_REGIMES)
                ]
                bull_is = 0 if means[0] >= means[1] else 1
                cached = float(sm[-1, bull_is])
            else:
                cached = 0.5
            last_fit = t
        p_bull[t] = cached
    return p_bull


def walk_forward_regime(
    df: pd.DataFrame,
    seed: int = 0,
    frequency: str = "D",
) -> dict:
    """Causal walk-forward regime allocation (fix #21633).

    The regime probability for day t is read strictly from the past (expanding
    fit on ``[0, t)``, refit every ``REFIT_EVERY`` days, regimes named on the
    training window). A one-day decision lag is applied: the regime decided at
    the close of day t-1 selects the return of day t. This removes the three
    in-sample leaks of the previous version (fit on the labelled block, Kim
    smoothed probabilities, regime naming on the block mean).

    Returns the per-seed scalars plus the raw net return arrays (``_ret_*``)
    that the significance step consumes; the arrays are popped before the
    results are serialised.
    """
    n = len(df)
    spy_ret = df["spy_ret"].values
    tlt_ret = df["tlt_ret"].values

    p_bull = _causal_regime_probabilities(df, seed)
    pred = np.where(p_bull >= 0.5, 0, 1)  # 0 = bull -> SPY, 1 = bear -> TLT

    # One-day decision lag: decision closed at day t-1 -> return of day t.
    pred_lag = np.empty(n, dtype=int)
    pred_lag[0] = pred[0]
    pred_lag[1:] = pred[:-1]

    regime_ret = np.where(pred_lag == 0, spy_ret, tlt_ret)
    switches = np.diff(pred_lag) != 0
    tx_cost = np.zeros_like(regime_ret)
    tx_cost[1:][switches] = -TX_COST_BPS / 10000
    regime_ret_net = regime_ret + tx_cost

    bh_ret = 0.5 * spy_ret + 0.5 * tlt_ret
    spy_held_ret = spy_ret

    regime_sharpe = _sharpe(regime_ret_net)
    bh_sharpe = _sharpe(bh_ret)
    spy_held_sharpe = _sharpe(spy_held_ret)
    delta_sharpe = regime_sharpe - bh_sharpe

    regime_dd = _max_drawdown(regime_ret_net)
    bh_dd = _max_drawdown(bh_ret)

    n_switches = int(switches.sum())
    n_years = len(pred_lag) / 252
    switches_per_year = n_switches / n_years if n_years > 0 else 0

    regime_durations = _regime_durations(pred_lag)

    return {
        "regime_sharpe": float(regime_sharpe),
        "bh_sharpe": float(bh_sharpe),
        "spy_held_sharpe": float(spy_held_sharpe),
        "delta_sharpe": float(delta_sharpe),
        "regime_cum_ret": float(np.prod(1 + regime_ret_net) - 1),
        "bh_cum_ret": float(np.prod(1 + bh_ret) - 1),
        "regime_max_dd": float(regime_dd),
        "bh_max_dd": float(bh_dd),
        "n_switches": n_switches,
        "switches_per_year": float(switches_per_year),
        "regime_durations": regime_durations,
        "n_obs": n,
        "frequency": frequency,
        "seed": seed,
        # Raw arrays for the significance step (popped before serialisation):
        "_regime_ret": regime_ret_net,
        "_bh_ret": bh_ret,
        "_spy_held_ret": spy_held_ret,
    }


def _walk_forward_leaky(
    df: pd.DataFrame,
    seed: int = 0,
    frequency: str = "D",
) -> dict:
    """The PREVIOUS in-sample construction, kept only as a leak witness.

    Replays the original algorithm verbatim (fit the HMM on the block it
    labels, read Kim smoothed probabilities, name regimes on the block mean,
    no decision lag). Running it in the same harness as the causal version
    isolates the share of the advantage carried by reading the future
    (protocol #21633 point 7). NOT used for the reported verdict.
    """
    n_is = len(df)
    fold_size = n_is // N_SPLITS

    predicted_labels = np.full(n_is, -1, dtype=int)
    for fold_idx in range(N_SPLITS):
        train_end = fold_size * (fold_idx + 1)
        val_end = fold_size * (fold_idx + 2) if fold_idx < N_SPLITS - 1 else n_is
        train_end = min(train_end, n_is - 1)
        val_end = min(val_end, n_is)
        if train_end < 126:
            continue
        val_block = df.iloc[train_end:val_end]
        if len(val_block) == 0:
            continue
        val_result = fit_markov_regime(
            val_block["spy_ret"].values,
            val_block["tlt_ret"].values,
            val_block["vix_level"].values,
        )
        if not val_result.get("converged", False):
            continue
        predicted_labels[train_end:val_end] = val_result["labels"]

    predicted_labels[predicted_labels == -1] = 0
    jittered_labels = _jitter_regime_boundaries(predicted_labels, seed)

    spy_ret = df["spy_ret"].values
    tlt_ret = df["tlt_ret"].values
    min_len = min(len(spy_ret), len(jittered_labels))
    spy_ret = spy_ret[-min_len:]
    tlt_ret = tlt_ret[-min_len:]
    pred = jittered_labels[-min_len:]

    regime_ret = np.where(pred == 0, spy_ret, tlt_ret)
    switches = np.diff(pred) != 0
    tx_cost = np.zeros_like(regime_ret)
    tx_cost[1:][switches] = -TX_COST_BPS / 10000
    regime_ret_net = regime_ret + tx_cost
    bh_ret = 0.5 * spy_ret + 0.5 * tlt_ret

    return {
        "regime_sharpe": float(_sharpe(regime_ret_net)),
        "bh_sharpe": float(_sharpe(bh_ret)),
        "delta_sharpe": float(_sharpe(regime_ret_net) - _sharpe(bh_ret)),
        "n_switches": int(switches.sum()),
        "frequency": frequency,
        "seed": seed,
    }


def _jitter_regime_boundaries(labels: np.ndarray, seed: int, max_jitter: int = 5) -> np.ndarray:
    """Shift each regime transition by ±max_jitter days (seed-dependent).

    Tests whether the allocation Sharpe is robust to small perturbations
    in the exact timing of regime switches. This is the meaningful source
    of variability for HMM-based allocation (the regime partition itself
    is stable, but the boundary timing matters for trading).
    """
    if seed == 0:
        return labels.copy()  # Baseline: no jitter

    rng = np.random.RandomState(seed)
    jittered = labels.copy()

    # Find regime switch points
    switches = np.where(np.diff(labels) != 0)[0]
    if len(switches) == 0:
        return jittered

    for idx in switches:
        shift = rng.randint(-max_jitter, max_jitter + 1)
        new_idx = max(0, min(len(labels) - 1, idx + shift))
        # Propagate the new regime forward from the shifted boundary
        new_regime = labels[idx + 1]
        start = min(idx, new_idx)
        end = max(idx, new_idx)
        for i in range(start, end + 1):
            jittered[i] = new_regime

    return jittered


def _sharpe(returns: np.ndarray) -> float:
    """Annualized Sharpe (``strategy_metrics.sharpe``: ddof=1, risk-free 0, 252 days).

    Returns 0.0 for fewer than 2 returns or a standard deviation below 1e-10.
    """
    if len(returns) < 2 or np.std(returns, ddof=1) < 1e-10:
        return 0.0
    return float(strategy_metrics.sharpe(returns))


def _max_drawdown(returns: np.ndarray) -> float:
    """Max drawdown, starting capital as first peak (``strategy_metrics.max_drawdown``)."""
    return strategy_metrics.max_drawdown(returns)


def _regime_durations(labels: np.ndarray) -> dict:
    """Compute mean/median duration in each regime."""
    durations = {0: [], 1: []}
    if len(labels) == 0:
        return {"regime_0_mean_duration": 0, "regime_0_median_duration": 0,
                "regime_1_mean_duration": 0, "regime_1_median_duration": 0}
    current = labels[0]
    count = 1
    for i in range(1, len(labels)):
        if labels[i] == current:
            count += 1
        else:
            durations.get(current, durations.setdefault(current, [])).append(count)
            current = labels[i]
            count = 1
    durations.setdefault(current, []).append(count)

    result = {}
    for k in [0, 1]:
        ds = durations.get(k, [])
        result[f"regime_{k}_mean_duration"] = float(np.mean(ds)) if ds else 0.0
        result[f"regime_{k}_median_duration"] = float(np.median(ds)) if ds else 0.0
    return result


# ── Multi-seed runner ─────────────────────────────────────────────────────────

def run_experiment(
    frequency: str = "D",
    seeds: list[int] | None = None,
    witness: bool = False,
) -> dict:
    """Run the causal multi-seed experiment for a given frequency (#21633).

    The primary verdict is the Ledoit-Wolf + Holm significance of the
    deterministic (seed 0) baseline against the two references. The multi-seed
    block-bootstrap aggregation is a robustness summary. With ``witness=True``
    the previous in-sample construction is replayed in the same harness and the
    Sharpe gap (the future-read share) is published.
    """
    if seeds is None:
        seeds = SEEDS

    print(f"Loading data ({frequency})...")
    df = load_data()
    if frequency == "W":
        df = resample_weekly(df)
    print(f"  {len(df)} rows, {df.index[0].date()} to {df.index[-1].date()}")

    seed_results = []
    seed0_arrays = None
    seed0_result = None
    for seed in seeds:
        print(f"  Seed {seed} (causal walk-forward)...", end=" ", flush=True)
        t0 = time.time()
        result = walk_forward_regime(df, seed=seed, frequency=frequency)
        elapsed = time.time() - t0

        if "error" in result:
            print(f"ERROR: {result['error']}")
            continue

        # Keep seed-0's raw arrays in memory for the significance step.
        if seed == 0:
            seed0_arrays = (result["_regime_ret"], result["_bh_ret"],
                            result["_spy_held_ret"])
            seed0_result = result
        # Pop raw arrays (not serialisable into results.json).
        result.pop("_regime_ret", None)
        result.pop("_bh_ret", None)
        result.pop("_spy_held_ret", None)

        result["elapsed_s"] = round(elapsed, 1)
        seed_results.append(result)
        print(f"done ({elapsed:.1f}s) Sharpe={result['regime_sharpe']:.4f} "
              f"(B&H={result['bh_sharpe']:.4f}, delta={result['delta_sharpe']:+.4f})")

    if not seed_results:
        return {"error": "No seeds converged", "frequency": frequency}

    # Multi-seed block-bootstrap aggregation (robustness summary).
    deltas = [r["delta_sharpe"] for r in seed_results]
    regime_sharpes = [r["regime_sharpe"] for r in seed_results]
    bh_sharpes = [r["bh_sharpe"] for r in seed_results]
    switches = [r["switches_per_year"] for r in seed_results]
    regime_dds = [r["regime_max_dd"] for r in seed_results]

    mean_delta = float(np.mean(deltas))
    se_delta = float(np.std(deltas, ddof=1) / np.sqrt(len(deltas))) if len(deltas) > 1 else 0.0
    t_stat = mean_delta / se_delta if se_delta > 0 else 0.0
    n_positive = sum(1 for d in deltas if d > 0)
    n_seeds = len(seed_results)

    from scipy.stats import binom
    p_value_sign = float(binom.sf(n_positive - 1, n_seeds, 0.5)) if n_seeds > 1 else 1.0

    # Primary verdict: Ledoit-Wolf + Holm significance of the seed-0 baseline
    # against the two references (protocol #21633 point 5).
    significance = None
    if seed0_arrays is not None:
        regime_arr, bh_arr, spy_arr = seed0_arrays
        significance = hmm_sig.compare_to_references(
            regime_arr,
            {"50_50_rebalanced": bh_arr, "spy_held": spy_arr},
        )

    # Leak witness: replay the in-sample construction; the gap is the
    # future-read share (protocol #21633 point 7).
    leak_witness = None
    if witness and seed0_arrays is not None and seed0_result is not None:
        leaky = _walk_forward_leaky(df, seed=0, frequency=frequency)
        leak_witness = {
            "leaky_regime_sharpe": leaky["regime_sharpe"],
            "leaky_delta_sharpe": leaky["delta_sharpe"],
            "causal_regime_sharpe_seed0": seed0_result["regime_sharpe"],
            "causal_delta_sharpe_seed0": seed0_result["delta_sharpe"],
            "sharpe_gap_future_read": leaky["regime_sharpe"] - seed0_result["regime_sharpe"],
            "delta_gap_future_read": leaky["delta_sharpe"] - seed0_result["delta_sharpe"],
        }

    agg = {
        "frequency": frequency,
        "n_seeds": n_seeds,
        "seeds": seeds,
        "mean_delta_sharpe": round(mean_delta, 6),
        "se_delta_sharpe": round(se_delta, 6),
        "t_stat": round(t_stat, 3),
        "mean_regime_sharpe": round(float(np.mean(regime_sharpes)), 4),
        "mean_bh_sharpe": round(float(np.mean(bh_sharpes)), 4),
        "mean_switches_per_year": round(float(np.mean(switches)), 1),
        "mean_regime_max_dd": round(float(np.mean(regime_dds)), 4),
        "n_positive": n_positive,
        "p_value_sign": round(p_value_sign, 6),
        "significance": significance,
        "verdict": significance["verdict"] if significance else "NO BEATS",
        "leak_witness": leak_witness,
        "seed_results": seed_results,
    }

    return agg


# ── Verdict report ────────────────────────────────────────────────────────────

def write_verdict(daily_results: dict, lh_results: dict, output_dir: Path) -> Path:
    """Write comparative verdict.md."""
    output_dir.mkdir(parents=True, exist_ok=True)
    verdict_path = output_dir / "verdict.md"

    lines = ["# S3 HMM Regime Detection — Verdict (causal, #21633)\n"]
    lines.append(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n")
    lines.append(f"Method: MarkovRegression 2-regime (statsmodels), **causal** walk-forward")
    lines.append(f"Features: SPY returns + TLT returns + VIX level")
    lines.append(f"Regime: fitted on the expanding window [0,t), refit every "
                 f"{REFIT_EVERY} days, named on the training window, 1-day decision lag")
    lines.append(f"Allocation: bull -> 100% SPY, bear -> 100% TLT")
    lines.append(f"Tx costs: {TX_COST_BPS}bps per switch")
    lines.append(f"Significance: Ledoit-Wolf (HAC) + Holm vs 50/50 rebalanced and SPY held")
    lines.append(f"Multi-seed: block bootstrap of the training slice, seeds 0/1/7/42\n")

    for label, res in [("Daily", daily_results), ("Weekly (Long-Horizon)", lh_results)]:
        lines.append(f"## Variant: {label}\n")
        if "error" in res:
            lines.append(f"**ERROR**: {res['error']}\n")
            continue
        lines.append(f"- **Verdict**: {res['verdict']}")
        sig = res.get("significance")
        if sig:
            for name, c in sig["comparisons"].items():
                lines.append(
                    f"- vs {name}: delta-Sharpe {c['sharpe_diff']:+.4f} "
                    f"(Ledoit-Wolf p={c['ledoit_wolf_p']:.4f}, Holm p={c['holm_p']:.4f}, "
                    f"bootstrap CI95 [{c['bootstrap_ci95'][0]:.3f}, {c['bootstrap_ci95'][1]:.3f}])")
        lines.append(f"- Mean delta-Sharpe (multi-seed): {res['mean_delta_sharpe']:+.6f} "
                     f"(SE={res['se_delta_sharpe']:.6f}, t={res['t_stat']:.3f})")
        lines.append(f"- Regime-aware Sharpe: {res['mean_regime_sharpe']:.4f} "
                     f"vs B&H {res['mean_bh_sharpe']:.4f}")
        lines.append(f"- Max Drawdown: {res['mean_regime_max_dd']:.4f}")
        lines.append(f"- Switching: {res['mean_switches_per_year']:.1f}/year")
        lines.append(f"- Seeds positive: {res['n_positive']}/{res['n_seeds']} "
                     f"(p={res['p_value_sign']:.4f})\n")
        lw = res.get("leak_witness")
        if lw:
            lines.append(f"### Témoin de fuite (in-sample replay)\n")
            lines.append(f"- Sharpe in-sample (lissé, sans décalage): {lw['leaky_regime_sharpe']:.4f}")
            lines.append(f"- Sharpe causal (seed 0): {lw['causal_regime_sharpe_seed0']:.4f}")
            lines.append(f"- **Écart porté par la lecture du futur**: "
                         f"{lw['sharpe_gap_future_read']:+.4f} "
                         f"(delta-Sharpe {lw['delta_gap_future_read']:+.4f})\n")

    # Comparative table
    lines.append("## Comparative\n")
    lines.append("| Metric | Daily | Weekly |")
    lines.append("|--------|-------|--------|")
    if "error" not in daily_results and "error" not in lh_results:
        lines.append(f"| Verdict | {daily_results['verdict']} | {lh_results['verdict']} |")
        lines.append(f"| Delta-Sharpe | {daily_results['mean_delta_sharpe']:+.4f} | "
                     f"{lh_results['mean_delta_sharpe']:+.4f} |")
        lines.append(f"| Regime Sharpe | {daily_results['mean_regime_sharpe']:.4f} | "
                     f"{lh_results['mean_regime_sharpe']:.4f} |")
        lines.append(f"| B&H Sharpe | {daily_results['mean_bh_sharpe']:.4f} | "
                     f"{lh_results['mean_bh_sharpe']:.4f} |")
        lines.append(f"| Switches/year | {daily_results['mean_switches_per_year']:.1f} | "
                     f"{lh_results['mean_switches_per_year']:.1f} |")
        lines.append(f"| Seeds pos | {daily_results['n_positive']}/{daily_results['n_seeds']} | "
                     f"{lh_results['n_positive']}/{lh_results['n_seeds']} |")
    lines.append("")

    any_beats = (
        daily_results.get("verdict") == "BEATS"
        or lh_results.get("verdict") == "BEATS"
    )
    lines.append("## Verdict S3 (causal)\n")
    lines.append(f"**S3 = {'BEATS' if any_beats else 'NO BEATS'}**")
    lines.append("Condition: the Ledoit-Wolf (HAC) delta-Sharpe is positive and "
                 "Holm-significant (< 0.05) against BOTH references.\n")

    verdict_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"\nVerdict written to {verdict_path}")
    return verdict_path


# ── CLI ───────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="S3 HMM Regime Detection")
    parser.add_argument(
        "--seeds", type=str, default="0,1,7,42",
        help="Comma-separated seeds (default: 0,1,7,42)",
    )
    parser.add_argument(
        "--frequency", type=str, default="all",
        choices=["D", "W", "M", "all"],
        help="Frequency: D=daily, W=weekly, all=run both",
    )
    parser.add_argument(
        "--output", type=str, default=None,
        help="Output directory (default: results/s3_hmm_regime/)",
    )
    parser.add_argument(
        "--witness", action="store_true",
        help="Also replay the previous in-sample construction and report the "
             "future-read Sharpe gap (protocol #21633 point 7).",
    )
    args = parser.parse_args()

    seeds = [int(s) for s in args.seeds.split(",")]
    output_dir = Path(args.output) if args.output else RESULTS_DIR
    output_dir.mkdir(parents=True, exist_ok=True)

    t_start = time.time()

    if args.frequency == "all":
        print("=" * 60)
        print("S3 HMM Regime Detection — Daily")
        print("=" * 60)
        daily = run_experiment("D", seeds, witness=args.witness)
        daily_dir = output_dir / "daily"
        daily_dir.mkdir(parents=True, exist_ok=True)
        (daily_dir / "results.json").write_text(
            json.dumps(daily, indent=2, default=str), encoding="utf-8"
        )

        print("\n" + "=" * 60)
        print("S3 HMM Regime Detection — Long-Horizon (Weekly)")
        print("=" * 60)
        lh = run_experiment("W", seeds, witness=args.witness)
        lh_dir = output_dir / "long_horizon"
        lh_dir.mkdir(parents=True, exist_ok=True)
        (lh_dir / "results.json").write_text(
            json.dumps(lh, indent=2, default=str), encoding="utf-8"
        )

        write_verdict(daily, lh, output_dir)
    else:
        result = run_experiment(args.frequency, seeds, witness=args.witness)
        freq_dir = output_dir / args.frequency
        freq_dir.mkdir(parents=True, exist_ok=True)
        (freq_dir / "results.json").write_text(
            json.dumps(result, indent=2, default=str), encoding="utf-8"
        )
        print(json.dumps({"verdict": result.get("verdict"), "frequency": args.frequency},
                         indent=2))

    elapsed = time.time() - t_start
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
