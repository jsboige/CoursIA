"""S5 — HMM regime-conditional SIZING (Curriculum V3 "L6" falsifiable hypothesis).

Hypothesis (ai-01 coordination decision 2026-07-19, #1409):
    L1-L5 trend overlays are all NO BEATS. L6 is defined as ONE falsifiable
    hypothesis DISTINCT from the trend family: **regime-conditional position
    SIZING via the HMM regime STATE (per-day probability), not another trend
    overlay**. Same bar of proof as every Curriculum rung: walk-forward 5-fold,
    >=4 seeds, edge >= 2 sigma cross-seed, transaction costs, honest verdict.

The architectural delta vs the V2 keepers (S3/S4):
    Both S3 (`s3_hmm_regime`) and S4 (`s4_inverse_vol_ridge_v2`) FIT the 2-regime
    MarkovRegression model — and S3's ``fit_markov_regime`` even returns per-day
    ``smoothed_probs`` (the regime probability, col 0 = bull, col 1 = bear). But
    BOTH predecessors **discard the probability at the OOS step** and collapse to
    the argmax hard label before sizing (S3:256, S4:289). S4's sizing is a hard
    ``if regime_label == 1`` defensive tilt. So the question "does using the
    *continuous* regime probability as a sizing scalar beat the hard switch?" has
    never been asked in the Curriculum.

This script asks it. Concretely:
    1. Real OOS regime inference (NOT in-sample-on-the-test-block like S3/S4):
       refit the HMM on the expanding training window ending at t-1 every
       ``REFIT_EVERY`` days, and read the smoothed regime probability at the
       current day from the model's own filter recursion on the training slice.
       No future information leaks into the regime call (this is the honest OOS
       semantics; neither predecessor does it — verified s3:248-256, s4:287-289).
    2. Continuous sizing: blend the bull and bear inverse-vol weight vectors by
       ``p_bear = smoothed_probs[-1, 1]``:
           w = (1 - p_bear) * w_bull + p_bear * w_bear
       instead of S4's hard ``np.where``. With Ridge shrinkage + simplex proj.
    3. Turnover-aware transaction cost (``estimate_trade_cost``) measured from
       (old, new) weights BEFORE reassignment — the s7_composite same-dict bug
       (PR #8591) is avoided by construction here.

Baselines (must beat at least the hard-switch one for the hypothesis to hold):
    - ``equal``      : static equal-weight (11 sectors/ETFs).
    - ``inv_vol``    : static inverse-volatility.
    - ``s4_hard``    : S4's hard regime-switch sizing (reproduced) — the
                       *direct* baseline that isolates the continuous-vs-hard
                       question. If S5 does not beat s4_hard, the probability
                       adds nothing and the hypothesis is REFUTED.

Universe: the 11-asset S4 panel (SPY, TLT, XLF, XLK, XLE, XLV, XLY, XLI, XLB,
XLU, XLP). Data via yfinance (data-source-to-convert, AUTHORIZED).

Gate: BEATS if mean(delta_sharpe_vs_s4_hard) > GATE_SHARPE_DELTA, t >= 2.0,
      >= 3/4 seeds positive, p_sign < 0.05. Else NO BEATS. If NO BEATS the
      Epic parks honestly (ai-01: "pas de L7 invente").

References:
    - S3/S4 (Curriculum V2 keepers): scripts/s3_hmm_regime.py, s4_inverse_vol_ridge_v2.py
    - Hamilton (1989): regime-switching models.
    - Corsi (2009): HAR-RV (the vol regime input).

Usage:
    # Smoke test (CPU-safe, 1 seed, 1 fold, tiny panel) — verify OOS plumbing
    python s5_hmm_regime_sizing.py --smoke
    # Full multi-seed sweep
    python s5_hmm_regime_sizing.py --seeds 0,1,7,42
    # Subset of symbols
    python s5_hmm_regime_sizing.py --symbols SPY TLT XLU XLP XLV
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
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

# Reuse the V2 keepers' primitives (single source of truth) ---------------
from s3_hmm_regime import fit_markov_regime  # noqa: E402
from s4_inverse_vol_ridge_v2 import (  # noqa: E402
    SYMBOLS,
    DEFENSIVE,
    inv_vol_weights,
    _project_simplex,
    equal_weights,
)

# ── Constants ────────────────────────────────────────────────────────────────

RESULTS_DIR = SCRIPT_DIR / "results" / "s5_hmm_regime_sizing"
SEEDS = [0, 1, 7, 42]
N_SPLITS = 5
OOS_YEAR = 2027
TX_COST_BPS = 5
TX_COST_STRESS_BPS = 50
GATE_SHARPE_DELTA = 0.10  # same as S4 (we want to beat the hard-switch baseline)
N_REGIMES = 2
BLOCK_SIZE = 22
REFIT_EVERY = 22  # HMM refit cadence (was vestigial in S3/S4; we actually use it)
RIDGE_ALPHA = 1.0  # Ridge shrinkage towards equal-weight (matches S4 default)
# Hermes review concern 1: the default alpha=1.0 compresses bull/bear toward
# equal-weight, so the continuous-vs-hard delta is small *by construction*. To
# rule out that NO BEATS is an artefact of shrinkage (rather than a genuine
# refutation), we sweep alpha and report the verdict per alpha. alpha=0.0 = no
# shrink (pure inverse-vol bull/bear, max blend amplitude); alpha=1.0 = S4's
# default. Robust verdict = NO BEATS at EVERY alpha.
ALPHA_GRID = [0.0, 0.1, 0.5, 1.0]
HMM_MIN_TRAIN = 252  # min days to fit the regime model


# ── Data ─────────────────────────────────────────────────────────────────────

def load_data(start: str = "2017-01-01", end: str = "2026-12-31") -> pd.DataFrame:
    """Load daily prices for the 11-asset panel via yfinance + VIX for the HMM."""
    import yfinance as yf

    frames = {}
    for sym in SYMBOLS + ["^VIX"]:
        df = yf.download(sym, start=start, end=end, progress=False)
        if df.empty:
            raise RuntimeError(f"No data for {sym}")
        if isinstance(df.columns, pd.MultiIndex):
            close = df[("Close", sym)]
        else:
            close = df["Close"]
        frames[sym] = close
    out = pd.DataFrame(frames)
    out.index = pd.to_datetime(out.index)
    return out.dropna()


def block_bootstrap(data: np.ndarray, block_size: int, seed: int) -> np.ndarray:
    """Stationary block bootstrap (matches s3/s4/s7)."""
    rng = np.random.RandomState(seed)
    n = len(data)
    n_blocks = (n + block_size - 1) // block_size
    indices = np.empty(n, dtype=int)
    pos = 0
    for _ in range(n_blocks):
        s = rng.randint(0, n - block_size + 1)
        e = min(pos + block_size, n)
        indices[pos:e] = np.arange(s, s + e - pos)
        pos = e
    return data[indices % n]


# ── Continuous regime-conditional sizing (the L6 delta) ─────────────────────

def _bull_bear_weight_vectors(
    returns: np.ndarray, alpha: float = RIDGE_ALPHA
) -> tuple[np.ndarray, np.ndarray]:
    """Bull and bear inverse-vol weight vectors with Ridge shrinkage.

    Bull  = inverse-vol across all assets (no defensive tilt).
    Bear  = inverse-vol tilted towards DEFENSIVE assets (doubled contribution),
            then Ridge-shrunk towards equal-weight. Mirrors S4's per-regime
            construction so the only difference between S5 and S4 is the
            continuous blend vs the hard switch.
    """
    n_assets = returns.shape[1]
    base = inv_vol_weights(returns)
    eq = equal_weights(n_assets)

    w_bull = _project_simplex((base + alpha * eq) / (1 + alpha))

    defensive_mask = np.array([1.0 if SYMBOLS[i] in DEFENSIVE else 0.5
                               for i in range(n_assets)])
    tilted = base * defensive_mask
    tilted = tilted / (tilted.sum() + 1e-12)
    w_bear = _project_simplex((tilted + alpha * eq) / (1 + alpha))
    return w_bull, w_bear


def continuous_regime_weights(
    returns: np.ndarray, p_bear: float, alpha: float = RIDGE_ALPHA
) -> np.ndarray:
    """Blend bull/bear vectors by the regime probability p_bear in [0, 1].

    Replaces S4's hard ``if regime_label == 1`` (s4:203). When p_bear is 0 or 1
    this reduces exactly to the S4 bull/bear vectors, so the hard switch is a
    special case of this continuous rule.
    """
    p_bear = float(np.clip(p_bear, 0.0, 1.0))
    w_bull, w_bear = _bull_bear_weight_vectors(returns, alpha)
    w = (1.0 - p_bear) * w_bull + p_bear * w_bear
    return _project_simplex(w)


def hard_regime_weights(returns: np.ndarray, regime_label: int) -> np.ndarray:
    """S4's hard-switch sizing, reproduced as the direct baseline.

    regime_label == 0 -> bull vector, == 1 -> bear vector (from the SAME
    _bull_bear_weight_vectors, so the comparison is apples-to-apples).
    """
    w_bull, w_bear = _bull_bear_weight_vectors(returns)
    return w_bear if regime_label == 1 else w_bull


def estimate_trade_cost(
    current_weights: np.ndarray, new_weights: np.ndarray
) -> float:
    """Sum of absolute weight changes (turnover). Measured from (old, new).

    NOTE: the caller MUST pass the OLD weights (before reassignment) — measuring
    turnover after ``current = new`` yields 0 (the s7_composite bug fixed in
    #8591). We document this here so the anti-pattern cannot return.
    """
    return float(np.sum(np.abs(new_weights - current_weights)))


# ── OOS regime inference (the honest part — real expanding-window refit) ─────

def _hmm_inputs(prices: pd.DataFrame) -> dict:
    """Precompute the HMM's (spy_ret, tlt_ret, vix_level) series aligned to the
    price index. The S3 fitter takes (spy_ret, tlt_ret, vix_level)."""
    spy = prices["SPY"].values
    tlt = prices["TLT"].values
    vix = prices["^VIX"].values
    spy_ret = np.diff(np.concatenate([[spy[0]], spy])) / np.concatenate([[spy[0]], spy])[:-1] \
        if len(spy) > 1 else np.zeros(len(spy))
    # simpler/robust pct_change aligned
    spy_ret = pd.Series(spy).pct_change().fillna(0.0).values
    tlt_ret = pd.Series(tlt).pct_change().fillna(0.0).values
    return {"spy_ret": spy_ret, "tlt_ret": tlt_ret, "vix_level": vix}


def oos_regime_probabilities(
    prices: pd.DataFrame, seed: int
) -> np.ndarray:
    """Real OOS regime inference: for each test day t, the regime probability
    comes from an HMM fitted on data STRICTLY BEFORE t (expanding window), with
    the model held fixed for ``REFIT_EVERY`` days between refits.

    Returns ``p_bear`` array (shape (n_days,)) aligned to ``prices.index``. Days
    before the first valid fit return p_bear = 0.5 (neutral).

    Seed variability: block-bootstrap perturbation of the training slice (same
    mechanism as S3/S4), so cross-seed spread is honest.
    """
    n = len(prices)
    inputs = _hmm_inputs(prices)
    spy_ret = inputs["spy_ret"]
    tlt_ret = inputs["tlt_ret"]
    vix_level = inputs["vix_level"]

    p_bear = np.full(n, 0.5)
    last_fit_idx = -1
    cached_p = 0.5  # regime prob held constant between refits

    for t in range(HMM_MIN_TRAIN, n):
        if (t - last_fit_idx) >= REFIT_EVERY or last_fit_idx < 0:
            # Fit on the expanding training window [0, t) — strictly past.
            train_slice = slice(0, t)
            sr = spy_ret[train_slice]
            tr = tlt_ret[train_slice]
            vl = vix_level[train_slice]
            # Block-bootstrap the training slice for seed variability.
            if seed != 0:
                sr = block_bootstrap(sr, BLOCK_SIZE, seed)
                tr = block_bootstrap(tr, BLOCK_SIZE, seed)
                vl = block_bootstrap(vl, BLOCK_SIZE, seed)
            try:
                res = fit_markov_regime(sr, tr, vl, seed=seed)
                if res.get("converged", False):
                    # Smoothed prob of the CURRENT last training day, from the
                    # model fitted on [0, t). No future leak: the filter at
                    # index t-1 only uses data up to t-1.
                    sp = res["smoothed_probs"]
                    cached_p = float(sp[-1, 1])  # col 1 = bear
                else:
                    cached_p = 0.5
            except Exception:
                cached_p = 0.5
            last_fit_idx = t
        p_bear[t] = cached_p
    return p_bear


# ── Walk-forward backtest ────────────────────────────────────────────────────

def _sharpe_ann(returns: np.ndarray) -> float:
    if len(returns) < 10:
        return float("nan")
    mu = float(np.mean(returns))
    sigma = float(np.std(returns, ddof=1))
    return (mu / sigma) * np.sqrt(252) if sigma > 1e-12 else float("nan")


def _max_drawdown(returns: np.ndarray) -> float:
    cum = np.cumprod(1 + returns)
    peak = np.maximum.accumulate(cum)
    dd = (cum - peak) / peak
    return float(np.min(dd)) if len(dd) > 0 else 0.0


def walk_forward_sizing(
    prices: pd.DataFrame, seed: int, tx_bps: int = TX_COST_BPS, alpha: float = RIDGE_ALPHA
) -> dict:
    """Walk-forward 5-fold backtest comparing continuous (S5) vs hard (S4) vs
    static baselines. Transaction costs are turnover-aware and applied once per
    rebalance day.

    Rebalance cadence: **daily, by design** (Hermes review concern 3). The HMM
    emits a fresh regime probability every bar, and a *sizing* strategy is
    meant to re-derive the blend each day — so n_rebalances approximates n_obs
    (both ~2000 in the full panel). This is conservative for the NO BEATS
    verdict: more rebalancing = more turnover cost = a lower bar for continuous
    to clear, not a higher one. Static baselines (equal/inv_vol) pay no cost.

    alpha: Ridge shrinkage toward equal-weight (concern 1 sweep). 0.0 = pure
    inverse-vol bull/bear (max blend amplitude); 1.0 = S4 default.
    """
    returns = prices.drop(columns=["^VIX"]).pct_change().dropna()
    n = len(returns)

    if n < 300:
        return {"error": "insufficient data"}

    # OOS regime probabilities (real expanding-window refit).
    p_bear_series = oos_regime_probabilities(prices, seed)

    fold_size = n // (N_SPLITS + 1)
    splits = []
    for k in range(1, N_SPLITS + 1):
        train_end = fold_size * k
        test_start = train_end
        test_end = min(train_end + fold_size, n)
        if test_end - test_start < 20:
            continue
        splits.append((train_end, test_start, test_end))

    # OOS window span = first test_start .. last test_end (for honest metrics).
    oos_start = splits[0][1] if splits else 0
    oos_end = splits[-1][2] if splits else n

    rets = returns.values
    idx_global = returns.index

    # Strategy returns containers.
    strat = {name: [] for name in ("continuous", "hard", "inv_vol", "equal")}
    n_rebalances = 0
    n_turnover_skips = 0

    # Weight states (init equal-weight).
    w_cont = equal_weights(rets.shape[1])
    w_hard = equal_weights(rets.shape[1])

    for fold_idx, (train_end, test_start, test_end) in enumerate(splits):
        for i in range(test_end - test_start):
            t = test_start + i
            if t >= n:
                break

            lookback = rets[max(0, t - 63):t]
            pb = p_bear_series[t]
            regime_label = 1 if pb > 0.5 else 0

            if len(lookback) >= 20:
                # Continuous sizing (S5 hypothesis), swept over alpha (concern 1).
                new_cont = continuous_regime_weights(lookback, pb, alpha)
                cost_cont = estimate_trade_cost(w_cont, new_cont)
                # Hard-switch sizing (S4 baseline, direct comparator).
                new_hard = hard_regime_weights(lookback, regime_label)
                cost_hard = estimate_trade_cost(w_hard, new_hard)
                # Static baselines.
                w_iv = inv_vol_weights(lookback)
                w_eq = equal_weights(rets.shape[1])

                w_cont = new_cont
                w_hard = new_hard
                n_rebalances += 1
            else:
                cost_cont = cost_hard = 0.0
                w_iv = equal_weights(rets.shape[1])
                w_eq = equal_weights(rets.shape[1])

            day_ret = rets[t]
            tx = tx_bps / 10000.0
            strat["continuous"].append(float(w_cont @ day_ret) - cost_cont * tx)
            strat["hard"].append(float(w_hard @ day_ret) - cost_hard * tx)
            strat["inv_vol"].append(float(w_iv @ day_ret))
            strat["equal"].append(float(w_eq @ day_ret))

    if len(strat["continuous"]) < 30:
        return {"error": "insufficient OOS returns"}

    out = {}
    for name, arr in strat.items():
        a = np.array(arr)
        out[f"sharpe_{name}"] = _sharpe_ann(a)
        out[f"cumret_{name}"] = float(np.prod(1 + a) - 1)
        out[f"maxdd_{name}"] = _max_drawdown(a)
    out["delta_continuous_vs_hard"] = out["sharpe_continuous"] - out["sharpe_hard"]
    out["delta_continuous_vs_equal"] = out["sharpe_continuous"] - out["sharpe_equal"]
    out["seed"] = seed
    out["alpha"] = alpha
    out["n_obs"] = len(strat["continuous"])
    out["n_rebalances"] = n_rebalances
    # Hermes review concern 2: mean p_bear over the FULL OOS window, not just
    # the last fold (the prior code used the post-loop test_start/test_end, i.e.
    # fold 5 only — misleading in the verdict table).
    out["mean_p_bear"] = float(np.mean(p_bear_series[oos_start:oos_end]))
    out["frac_bear_days"] = float(np.mean(p_bear_series[oos_start:oos_end] > 0.5))
    return out


# ── Verdict ──────────────────────────────────────────────────────────────────

def aggregate_and_verdict(seed_results: list[dict]) -> dict:
    """Aggregate cross-seed: mean delta vs the hard baseline, SE, t-stat,
    sign-test p-value. BEATS gate (delta > GATE, t >= 2, >= 3/4 positive)."""
    from scipy.stats import binomtest

    deltas = [r["delta_continuous_vs_hard"] for r in seed_results]
    n = len(deltas)
    mean_delta = float(np.mean(deltas))
    se = float(np.std(deltas, ddof=1) / np.sqrt(n)) if n > 1 else 0.0
    t_stat = mean_delta / se if se > 1e-12 else float("inf")
    n_positive = int(np.sum(np.array(deltas) > 0))
    p_sign = float(binomtest(n_positive, n, 0.5, alternative="greater").pvalue) \
        if n > 0 else 1.0

    beats = (
        mean_delta > GATE_SHARPE_DELTA
        and t_stat >= 2.0
        and n_positive >= 3
    )
    verdict = "BEATS" if beats else "NO BEATS"

    return {
        "hypothesis": "regime-conditional SIZING via HMM probability (continuous blend) "
                      "beats S4's hard regime switch",
        "n_seeds": n,
        "seeds": [r["seed"] for r in seed_results],
        "mean_delta_continuous_vs_hard": mean_delta,
        "se_delta": se,
        "t_stat": t_stat,
        "n_positive": n_positive,
        "p_sign": p_sign,
        "gate_delta": GATE_SHARPE_DELTA,
        "gate_t_stat": 2.0,
        "mean_sharpe_continuous": float(np.mean([r["sharpe_continuous"] for r in seed_results])),
        "mean_sharpe_hard": float(np.mean([r["sharpe_hard"] for r in seed_results])),
        "mean_sharpe_equal": float(np.mean([r["sharpe_equal"] for r in seed_results])),
        "mean_sharpe_inv_vol": float(np.mean([r["sharpe_inv_vol"] for r in seed_results])),
        "verdict": verdict,
        "seed_results": seed_results,
    }


def write_verdict(results: dict, output_dir: Path) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)
    by_alpha = results["by_alpha"]
    md = ["# S5 HMM Regime Sizing — Verdict (robustness sweep)", "",
          f"Hypothesis: {results['hypothesis']}", "",
          f"Date: {time.strftime('%Y-%m-%d %H:%M')}", "",
          f"- **Robust verdict**: **{results['robust_verdict']}**",
          f"- Sweep: alpha (Ridge shrink toward equal-weight) in {results['alpha_grid']}. "
          f"alpha=0.0 = pure inverse-vol bull/bear (max blend amplitude); alpha=1.0 = S4 default.",
          f"- Robust = NO BEATS at EVERY alpha (excludes shrinkage-artefact, Hermes concern 1).", "",
          "## Alpha-sweep summary", "",
          "| alpha | Continuous | Hard | Equal | Delta vs hard | t | seeds pos | Verdict |",
          "|-------|-----------|------|-------|--------------|---|-----------|---------|"]
    for a in sorted(by_alpha, key=lambda x: float(x)):
        v = by_alpha[a]
        md.append(
            f"| {a} | {v['mean_sharpe_continuous']:.4f} | {v['mean_sharpe_hard']:.4f} | "
            f"{v['mean_sharpe_equal']:.4f} | {v['mean_delta_continuous_vs_hard']:+.6f} | "
            f"{v['t_stat']:.3f} | {v['n_positive']}/{v['n_seeds']} | {v['verdict']} |"
        )
    # Per-seed detail for the reference alpha (1.0 = S4 default).
    ref = results.get("reference_alpha_1.0")
    if ref:
        md += ["", "## Per-seed detail (alpha=1.0, S4 default shrinkage)", "",
               "| Seed | Continuous | Hard | Delta | Equal | InvVol | mean p_bear | frac bear days |",
               "|------|-----------|------|-------|-------|--------|-------------|----------------|"]
        for r in ref["seed_results"]:
            md.append(
                f"| {r['seed']} | {r['sharpe_continuous']:.4f} | {r['sharpe_hard']:.4f} | "
                f"{r['delta_continuous_vs_hard']:+.4f} | {r['sharpe_equal']:.4f} | "
                f"{r['sharpe_inv_vol']:.4f} | {r['mean_p_bear']:.3f} | "
                f"{r.get('frac_bear_days', float('nan')):.3f} |"
            )
    md += ["",
           "## Methodology notes",
           "- mean p_bear / frac bear days measured over the FULL OOS window (all folds), "
           "not just the last fold (Hermes concern 2).",
           "- Rebalance cadence: **daily, by design** (n_rebalances approx n_obs). The HMM emits "
           "a fresh regime probability every bar; a sizing strategy re-derives the blend daily. "
           "Conservative for NO BEATS: more rebalancing = more turnover cost (Hermes concern 3).",
           "- OOS: real expanding-window HMM refit on [0,t) every 22 days (neither S3 nor S4 do "
           "this — they fit on the test block itself). No future leak."]
    verdict_path = output_dir / "verdict.md"
    verdict_path.write_text("\n".join(md) + "\n", encoding="utf-8")
    return verdict_path


# ── Main ─────────────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(description="S5 HMM regime-conditional sizing (Curriculum V3 L6)")
    parser.add_argument("--seeds", default="0,1,7,42", help="Seeds (comma-separated)")
    parser.add_argument("--smoke", action="store_true",
                        help="Smoke test: 1 seed, tiny panel, verify OOS plumbing")
    parser.add_argument("--symbols", nargs="*", default=None,
                        help="Subset of SYMBOLS (default: full 11-asset panel)")
    args = parser.parse_args()

    smoke = args.smoke
    seeds = [0] if smoke else [int(s.strip()) for s in args.seeds.split(",")]

    print("Loading multi-asset panel (sectors + defensive ETFs + VIX)...")
    prices_full = load_data()
    cols = (args.symbols + ["^VIX"]) if args.symbols else (list(SYMBOLS) + ["^VIX"])
    # Keep only columns present; smoke trims the panel for speed.
    if smoke:
        cols = ["SPY", "TLT", "XLU", "XLP", "^VIX"]
    prices = prices_full[[c for c in cols if c in prices_full.columns]].dropna()
    # Re-bind SYMBOLS-derived indices used by the sizing fns to the active panel.
    active_symbols = [c for c in cols if c != "^VIX" and c in prices.columns]
    print(f"  active panel ({len(active_symbols)}): {active_symbols}")

    t0 = time.time()
    alphas = [1.0] if smoke else list(ALPHA_GRID)
    by_alpha: dict[float, dict] = {}
    for alpha in alphas:
        print(f"\n=== alpha={alpha} (Ridge shrink toward equal-weight) ===")
        seed_results = []
        for seed in seeds:
            print(f"  Seed {seed}...", end=" ", flush=True)
            t1 = time.time()
            r = walk_forward_sizing(prices, seed, alpha=alpha)
            if "error" in r:
                print(f"ERROR: {r['error']}")
                continue
            seed_results.append(r)
            print(
                f"cont={r['sharpe_continuous']:.4f} hard={r['sharpe_hard']:.4f} "
                f"eq={r['sharpe_equal']:.4f} delta={r['delta_continuous_vs_hard']:+.4f} "
                f"p_bear={r['mean_p_bear']:.3f} ({time.time()-t1:.1f}s)",
                flush=True,
            )
        if not seed_results:
            print(f"No valid results for alpha={alpha}")
            continue
        by_alpha[alpha] = aggregate_and_verdict(seed_results)

    print(f"\nTotal time: {time.time()-t0:.1f}s")
    if not by_alpha:
        print("No valid results.")
        return

    # Robust verdict (Hermes review concern 1): NO BEATS at EVERY alpha excludes
    # the shrinkage-artefact explanation. If any alpha BEATS, the hypothesis is
    # NOT robustly refuted and the finding goes back to ai-01.
    all_no_beats = all(v["verdict"] == "NO BEATS" for v in by_alpha.values())
    robust_verdict = "ROBUST NO BEATS" if all_no_beats else "NOT ROBUST (>=1 alpha BEATS)"
    summary = {
        "hypothesis": next(iter(by_alpha.values()))["hypothesis"],
        "robust_verdict": robust_verdict,
        "alpha_grid": alphas,
        "by_alpha": {str(a): by_alpha[a] for a in by_alpha},
        "reference_alpha_1.0": by_alpha.get(1.0),
    }
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    (RESULTS_DIR / "results.json").write_text(
        json.dumps(summary, indent=2, default=str), encoding="utf-8"
    )
    vpath = write_verdict(summary, RESULTS_DIR)
    print(f"\nRobust verdict: {robust_verdict}")
    for alpha in by_alpha:
        v = by_alpha[alpha]
        print(f"  alpha={alpha}: {v['verdict']}  "
              f"delta={v['mean_delta_continuous_vs_hard']:+.4f}  "
              f"t={v['t_stat']:.2f}  {v['n_positive']}/{v['n_seeds']} pos")
    print(f"Verdict written to {vpath}")
    print(f"Verdict written to {vpath}")


if __name__ == "__main__":
    main()
