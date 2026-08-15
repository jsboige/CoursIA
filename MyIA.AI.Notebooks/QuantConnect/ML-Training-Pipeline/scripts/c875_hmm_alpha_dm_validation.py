"""C875 - HMM-alpha rigorous validation: Ledoit-Wolf paired Sharpe-diff DM test.

Fills the validation gap in `hmm_alpha_research.ipynb`: the existing notebook
runs walk-forward 5-fold x 4 seeds but uses a *heuristic* verdict
(edge >= 2 sigma). It does NOT run a proper Diebold-Mariano significance test
against the buy-and-hold benchmark, unlike M3/M4/M11e/M12/M15.

This script:
1. Replicates the HMM-alpha walk-forward from the notebook (BTC 2/3/4 states,
   ETH 2/3, SOL 2/3/4, Joint 3 = 9 configs).
2. Uses 5 seeds [0, 1, 7, 42, 99] (standard, adds 99 to existing 4).
3. Captures per-fold paired daily returns (strat net of cost vs buy-and-hold).
4. Computes Ledoit-Wolf (2008) paired Sharpe-difference with HAC Newey-West SE
   (re-using `m11c_sharpe_test.ledoit_wolf_sharpe_diff_se`).
5. Stress test at 50 bps round-trip (in addition to baseline 10 bps crypto).
6. Outputs an honest BEATS/NO BEATS/INCONCLUSIVE verdict per config.

Methodology:
- For each (asset, n_states) config:
    For each seed in [0,1,7,42,99]:
        For each of 5 walk-forward folds:
            Fit HMM on train (expanding window), predict on test.
            Signal: long state = argmax of state means (return column).
            Strat return = signal * next-day return - cost(trade).
    Aggregate: for each fold, AVERAGE strat returns across seeds
    (seed-ensemble = expected strategy under EM stochasticity).
    Concatenate fold-level seed-averaged returns -> pooled OOS series.
    Run Ledoit-Wolf paired Sharpe-diff (HAC) on pooled series.
- Verdict: BEATS iff Sharpe_strat > Sharpe_BH AND one-sided p < 0.05.

References:
- Ledoit, O. & Wolf, M. (2008). Robust performance hypothesis testing with the
  Sharpe ratio. Journal of Empirical Finance 15(5).
- Diebold, F.X. & Mariano, R.S. (1995). Comparing Predictive Accuracy. JBES.
- Broad, J. (2025). Hands-On AI Trading with Python, Ch6 Ex4 (HMM alpha source).

Outputs:
- `scripts/results/c875_hmm_alpha_dm.json` (full per-config metrics)
- stdout summary table

Env: `coursia-ml-training` (numpy, pandas, scipy, scikit-learn, hmmlearn 0.3.3).
HMM is CPU-bound (no GPU); nvidia-smi polled before/after to document thermals
per CLAUDE.md HARD rule on absent `gpu_training` watchdog.
"""

from __future__ import annotations

import json
import sys
import time
import warnings
from pathlib import Path

import numpy as np
import pandas as pd
import yfinance as yf
from hmmlearn import hmm
from sklearn.preprocessing import StandardScaler

warnings.filterwarnings("ignore")

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

# Re-use the Ledoit-Wolf HAC paired Sharpe-diff from the existing M11c test.
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402

RESULTS_DIR = SCRIPT_DIR / "results"
RESULTS_DIR.mkdir(exist_ok=True)

SEEDS = [0, 1, 7, 42, 99]
N_FOLDS = 5
COST_BPS_BASELINE = 10.0   # crypto standard (cf CLAUDE.md gate §C)
COST_BPS_STRESS = 50.0     # stress per REGISTRY methodology
ANNUALIZE = np.sqrt(365)   # crypto trades 365d/yr


# ---------------------------------------------------------------------------
# Data loading
# ---------------------------------------------------------------------------

def _yf_download_retry(ticker: str, start: str, end: str,
                       max_attempts: int = 3) -> pd.Series:
    """yfinance download with retries (handles transient rate-limits)."""
    for attempt in range(max_attempts):
        df = yf.download(ticker, start=start, end=end, progress=False,
                         auto_adjust=True)
        if df is not None and len(df) > 0:
            close = df["Close"]
            if isinstance(close, pd.DataFrame):
                close = close.iloc[:, 0]
            return close.dropna()
        time.sleep(2 * (attempt + 1))
    raise RuntimeError(f"yfinance failed for {ticker} after {max_attempts} attempts")


def load_returns() -> dict[str, pd.Series]:
    """Load BTC/ETH/SOL daily log returns via yfinance.

    Uses 2018+ for BTC/ETH and 2020+ for SOL (yfinance reliability window;
    the original notebook's 2014 range returns 'possibly delisted' on retry).
    2018-2024 covers 2 full BTC halving cycles (2018 bear, 2020-21 bull,
    2022 bear, 2023-24 recovery) = robust regime diversity for HMM.
    """
    print("[data] Downloading BTC-USD, ETH-USD, SOL-USD via yfinance...")
    btc = _yf_download_retry("BTC-USD", "2018-01-01", "2024-12-31")
    eth = _yf_download_retry("ETH-USD", "2018-01-01", "2024-12-31")
    sol = _yf_download_retry("SOL-USD", "2020-01-01", "2024-12-31")

    # Normalize column names (yfinance may return DataFrame or Series)
    if isinstance(btc, pd.DataFrame):
        btc = btc.iloc[:, 0]
    if isinstance(eth, pd.DataFrame):
        eth = eth.iloc[:, 0]
    if isinstance(sol, pd.DataFrame):
        sol = sol.iloc[:, 0]

    btc.name = "BTC"
    eth.name = "ETH"
    sol.name = "SOL"


    ret = {}
    for sym, s in [("BTC", btc), ("ETH", eth), ("SOL", sol)]:
        s = s.dropna()
        r = np.log(s / s.shift(1)).dropna()
        r.name = sym
        ret[sym] = r
        print(f"  {sym}: {len(r)} daily returns, "
              f"{r.index[0].date()} -> {r.index[-1].date()}")
    return ret


def build_joint_features(returns: dict[str, pd.Series]) -> pd.DataFrame:
    """Build the cross-asset feature set used by the joint multi-asset HMM.

    Mirrors `hmm_alpha_research.ipynb` cell `ea883e55` (joint features).
    """
    df = pd.DataFrame({k: v for k, v in returns.items()})
    df = df.dropna()

    feats = pd.DataFrame(index=df.index)
    feats["btc_ret"] = df["BTC"]
    feats["btc_vol20"] = df["BTC"].rolling(20).std()
    feats["btc_mom5"] = df["BTC"].rolling(5).sum()
    feats["eth_ret"] = df["ETH"]
    feats["btc_eth_corr"] = df["BTC"].rolling(20).corr(df["ETH"])
    feats["sol_ret"] = df["SOL"]
    feats["btc_sol_corr"] = df["BTC"].rolling(20).corr(df["SOL"])
    feats["rel_mom_btc_eth"] = (df["BTC"].rolling(10).sum()
                                - df["ETH"].rolling(10).sum())
    feats["rel_mom_btc_sol"] = (df["BTC"].rolling(10).sum()
                                - df["SOL"].rolling(10).sum())
    return feats.dropna()


# ---------------------------------------------------------------------------
# Walk-forward HMM-alpha
# ---------------------------------------------------------------------------

def walk_forward_hmm_alpha(
    returns_series: pd.Series,
    n_states: int,
    seeds: list[int],
    n_folds: int,
    cost_bps: float,
    feature_df: pd.DataFrame | None = None,
    btc_returns_for_joint: pd.Series | None = None,
) -> pd.DataFrame:
    """Walk-forward validation of the HMM-alpha strategy.

    If `feature_df` is None: single-asset HMM on `returns_series` reshaped.
    Else: joint multi-asset HMM on `feature_df`; signal applied to
    `btc_returns_for_joint`.

    Returns DataFrame with columns:
        fold, seed, sharpe_strat, sharpe_bh, n_trades, n_test,
        strat_returns (object: np.ndarray), bh_returns (object: np.ndarray)
    """
    single = feature_df is None
    if single:
        idx = returns_series.index
        n = len(returns_series)
        values = returns_series.values
    else:
        idx = feature_df.index
        # Align btc returns to feature index
        if btc_returns_for_joint is None:
            raise ValueError("btc_returns_for_joint required for joint HMM")
        btc_aligned = btc_returns_for_joint.reindex(idx).dropna()
        feature_df = feature_df.loc[btc_aligned.index]
        idx = btc_aligned.index
        n = len(idx)

    fold_size = n // (n_folds + 1)
    min_fold_days = 30  # minimum for meaningful Sharpe; skip degenerate tail
    rows = []

    for seed in seeds:
        for fold in range(n_folds):
            train_end = fold_size * (fold + 2)
            test_start = train_end
            test_end = min(train_end + fold_size, n)
            if test_end - test_start < min_fold_days:
                # Skip degenerate tail fold (e.g., 3-5 day remainder)
                continue

            try:
                if single:
                    X_train = returns_series.iloc[:train_end].values.reshape(-1, 1)
                    X_test = returns_series.iloc[test_start:test_end].values.reshape(-1, 1)
                    test_ret = returns_series.iloc[test_start:test_end].values
                    model = hmm.GaussianHMM(
                        n_components=n_states, covariance_type="full",
                        n_iter=200, random_state=seed, tol=1e-4,
                    )
                    model.fit(X_train)
                    states = model.predict(X_test)
                    means = model.means_.flatten()
                else:
                    train_feat = feature_df.iloc[:train_end]
                    test_feat = feature_df.iloc[test_start:test_end]
                    scaler = StandardScaler()
                    X_train = scaler.fit_transform(train_feat.values)
                    X_test = scaler.transform(test_feat.values)
                    test_ret = btc_aligned.iloc[test_start:test_end].values
                    model = hmm.GaussianHMM(
                        n_components=n_states, covariance_type="full",
                        n_iter=200, random_state=seed, tol=1e-4,
                    )
                    model.fit(X_train)
                    states = model.predict(X_test)
                    # First column of means corresponds to btc_ret
                    means = model.means_[:, 0]

                long_state = int(np.argmax(means))
                signals = np.where(states == long_state, 1, 0)
                strat_gross = signals * test_ret
                trades = np.abs(np.diff(signals, prepend=signals[0]))
                costs = trades * cost_bps / 10000.0
                strat_net = strat_gross - costs

                bh = test_ret.copy()
                if np.std(strat_net) > 0 and np.std(bh) > 0:
                    sharpe_strat = (np.mean(strat_net) / np.std(strat_net)
                                    * ANNUALIZE)
                    sharpe_bh = np.mean(bh) / np.std(bh) * ANNUALIZE
                else:
                    sharpe_strat = 0.0
                    sharpe_bh = 0.0

                rows.append({
                    "fold": fold, "seed": seed,
                    "sharpe_strat": float(sharpe_strat),
                    "sharpe_bh": float(sharpe_bh),
                    "n_trades": int(trades.sum()),
                    "n_test": int(test_end - test_start),
                    "strat_returns": strat_net,
                    "bh_returns": bh,
                })
            except Exception as e:  # noqa: BLE001
                rows.append({
                    "fold": fold, "seed": seed,
                    "sharpe_strat": float("nan"),
                    "sharpe_bh": float("nan"),
                    "n_trades": 0, "n_test": int(test_end - test_start),
                    "strat_returns": np.array([]),
                    "bh_returns": np.array([]),
                    "error": str(e),
                })
    return pd.DataFrame(rows)


# ---------------------------------------------------------------------------
# Ledoit-Wolf DM aggregation per config
# ---------------------------------------------------------------------------

def aggregate_dm(wf_df: pd.DataFrame) -> dict:
    """Aggregate walk-forward results into a Ledoit-Wolf DM verdict.

    Method: per fold, average strat returns across seeds (seed-ensemble =
    expected strategy under EM stochasticity). Concatenate folds into one
    pooled OOS series. Run Ledoit-Wolf paired Sharpe-diff (HAC) once.
    """
    valid = wf_df.dropna(subset=["sharpe_strat"]).copy()
    valid = valid[valid["strat_returns"].apply(len) > 0]
    if len(valid) == 0:
        return {"verdict": "NO DATA", "n_folds_seed_valid": 0}

    # Per fold: average strat_returns across seeds
    pooled_strat = []
    pooled_bh = []
    for fold in sorted(valid["fold"].unique()):
        sub = valid[valid["fold"] == fold]
        # All seeds must have same length for a given fold (same test window)
        lens = sub["strat_returns"].apply(len).unique()
        if len(lens) > 1:
            mn = int(min(lens))
            strat_arrs = np.stack([s[:mn] for s in sub["strat_returns"].values])
            bh_arrs = np.stack([b[:mn] for b in sub["bh_returns"].values])
        else:
            strat_arrs = np.stack(sub["strat_returns"].values)
            bh_arrs = np.stack(sub["bh_returns"].values)
        pooled_strat.append(strat_arrs.mean(axis=0))
        pooled_bh.append(bh_arrs.mean(axis=0))

    strat_pooled = np.concatenate(pooled_strat)
    bh_pooled = np.concatenate(pooled_bh)
    n_obs = len(strat_pooled)

    if n_obs < 30:
        return {"verdict": "INSUFFICIENT DATA", "n_obs": n_obs}

    sharpe_strat, sharpe_bh, sdiff, se = ledoit_wolf_sharpe_diff_se(
        strat_pooled, bh_pooled
    )
    if np.isnan(se) or se < 1e-12:
        t_stat = float("nan")
        p_one_sided = float("nan")
    else:
        t_stat = sdiff / se
        from scipy import stats as sps
        # One-sided: H0: Sharpe_strat <= Sharpe_BH; reject if t large positive
        p_one_sided = float(sps.norm.sf(t_stat))

    # Verdict per CLAUDE.md gate §C: BEATS requires DM significance + edge
    if (not np.isnan(p_one_sided)) and sdiff > 0 and p_one_sided < 0.05:
        verdict = "BEATS"
    elif (not np.isnan(p_one_sided)) and sdiff < 0 and p_one_sided < 0.05:
        # Baseline significantly better
        verdict = "NO BEATS"
    elif not np.isnan(p_one_sided):
        verdict = "INCONCLUSIVE"
    else:
        verdict = "INCONCLUSIVE (SE=0)"

    # Cross-seed edge on Sharpe (heuristic from existing notebook, kept for
    # comparability)
    mean_s = float(valid["sharpe_strat"].mean())
    std_s = float(valid["sharpe_strat"].std(ddof=1)) if len(valid) > 1 else float("nan")
    edge_sigma = mean_s / std_s if std_s and std_s > 0 else float("inf")

    return {
        "verdict": verdict,
        "n_obs": int(n_obs),
        "n_fold_seed_pairs": int(len(valid)),
        "sharpe_strat_daily": float(sharpe_strat),
        "sharpe_bh_daily": float(sharpe_bh),
        "sharpe_strat_annual": float(sharpe_strat * ANNUALIZE),
        "sharpe_bh_annual": float(sharpe_bh * ANNUALIZE),
        "sharpe_diff_daily": float(sdiff),
        "sharpe_diff_annual": float(sdiff * ANNUALIZE),
        "se_diff_daily": float(se),
        "t_stat": float(t_stat),
        "p_value_one_sided": float(p_one_sided),
        "mean_sharpe_fold_seed": mean_s,
        "std_sharpe_fold_seed": std_s,
        "edge_sigma_heuristic": float(edge_sigma),
        "mean_trades_per_fold_seed": float(valid["n_trades"].mean()),
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    print("=" * 70)
    print("C875 - HMM-alpha rigorous DM validation")
    print("=" * 70)
    print(f"Seeds: {SEEDS}  (5 seeds, standard 0/1/7/42/99)")
    print(f"Folds: {N_FOLDS}  (walk-forward, expanding)")
    print(f"Cost scenarios: baseline {COST_BPS_BASELINE} bps, "
          f"stress {COST_BPS_STRESS} bps")
    print(f"Annualization: sqrt(365) = {ANNUALIZE:.4f}")
    print()

    # GPU thermal snapshot (start) - documents that HMM is CPU-bound and
    # GPU stays cool even with absent `gpu_training` watchdog.
    try:
        import subprocess
        gpu_start = subprocess.run(
            ["nvidia-smi", "--query-gpu=temperature.gpu,memory.used",
             "--format=csv,noheader"],
            capture_output=True, text=True, check=False,
        ).stdout.strip()
        print(f"[thermal] GPU state at start: {gpu_start}")
    except Exception as e:  # noqa: BLE001
        print(f"[thermal] nvidia-smi unavailable: {e}")
    print()

    t_start = time.time()
    returns = load_returns()
    joint_feats = build_joint_features(returns)

    # Define configs: (label, asset, n_states, is_joint)
    configs = [
        ("BTC 2 states", "BTC", 2, False),
        ("BTC 3 states", "BTC", 3, False),
        ("BTC 4 states", "BTC", 4, False),
        ("ETH 2 states", "ETH", 2, False),
        ("ETH 3 states", "ETH", 3, False),
        ("SOL 2 states", "SOL", 2, False),
        ("SOL 3 states", "SOL", 3, False),
        ("SOL 4 states", "SOL", 4, False),
        ("Joint multi-asset 3 states", "BTC", 3, True),
    ]

    all_results = {}
    for label, asset, n_states, is_joint in configs:
        print(f"\n--- {label} ---")
        for cost_bps, cost_label in [(COST_BPS_BASELINE, "baseline_10bps"),
                                     (COST_BPS_STRESS, "stress_50bps")]:
            t0 = time.time()
            if is_joint:
                wf = walk_forward_hmm_alpha(
                    None, n_states, SEEDS, N_FOLDS, cost_bps,
                    feature_df=joint_feats,
                    btc_returns_for_joint=returns["BTC"],
                )
            else:
                wf = walk_forward_hmm_alpha(
                    returns[asset], n_states, SEEDS, N_FOLDS, cost_bps,
                )
            dm = aggregate_dm(wf)
            dm["cost_bps"] = cost_bps
            dm["cost_label"] = cost_label
            dm["elapsed_s"] = round(time.time() - t0, 1)
            all_results.setdefault(label, {})[cost_label] = dm

            sharpe_s_ann = dm.get("sharpe_strat_annual", float("nan"))
            sharpe_bh_ann = dm.get("sharpe_bh_annual", float("nan"))
            t_stat = dm.get("t_stat", float("nan"))
            p_val = dm.get("p_value_one_sided", float("nan"))
            print(f"  [{cost_label}] Sharpe strat {sharpe_s_ann:+.3f} vs "
                  f"BH {sharpe_bh_ann:+.3f} | t={t_stat:+.3f} "
                  f"p={p_val:.4f} | verdict={dm['verdict']} "
                  f"({dm['elapsed_s']:.1f}s)")

    elapsed_total = time.time() - t_start
    print(f"\n[total] {elapsed_total:.1f}s ({elapsed_total/60:.2f} min)")

    # GPU thermal snapshot (end)
    try:
        gpu_end = subprocess.run(
            ["nvidia-smi", "--query-gpu=temperature.gpu,memory.used",
             "--format=csv,noheader"],
            capture_output=True, text=True, check=False,
        ).stdout.strip()
        print(f"[thermal] GPU state at end:   {gpu_end}")
    except Exception as e:  # noqa: BLE001
        print(f"[thermal] nvidia-smi end unavailable: {e}")

    # Final summary table
    print("\n" + "=" * 95)
    print("FINAL VERDICTS (Ledoit-Wolf paired Sharpe-diff, HAC Newey-West, "
          "one-sided)")
    print("=" * 95)
    print(f"{'Config':<32} {'cost':<14} {'Sharpe_s':<10} {'Sharpe_BH':<10} "
          f"{'t-stat':<9} {'p-val':<8} {'verdict':<14}")
    print("-" * 95)
    for label, costs in all_results.items():
        for cost_label, dm in costs.items():
            print(f"{label:<32} {cost_label:<14} "
                  f"{dm.get('sharpe_strat_annual', float('nan')):+.3f}     "
                  f"{dm.get('sharpe_bh_annual', float('nan')):+.3f}     "
                  f"{dm.get('t_stat', float('nan')):+.3f}   "
                  f"{dm.get('p_value_one_sided', float('nan')):.4f}   "
                  f"{dm['verdict']}")

    # Count verdicts at baseline cost (primary)
    base_verdicts = [c["baseline_10bps"]["verdict"] for c in all_results.values()]
    n_beats = sum(1 for v in base_verdicts if v == "BEATS")
    n_no = sum(1 for v in base_verdicts if v == "NO BEATS")
    n_inc = sum(1 for v in base_verdicts if v.startswith("INCONCLUSIVE"))
    print(f"\nBilan (baseline 10bps) : {n_beats} BEATS, {n_no} NO BEATS, "
          f"{n_inc} INCONCLUSIVE / {len(base_verdicts)} configs")

    # Save JSON
    out = {
        "experiment": "c875_hmm_alpha_dm_validation",
        "timestamp": pd.Timestamp.now().isoformat(),
        "seeds": SEEDS,
        "n_folds": N_FOLDS,
        "annualization_factor": float(ANNUALIZE),
        "cost_scenarios_bps": [COST_BPS_BASELINE, COST_BPS_STRESS],
        "total_elapsed_s": round(elapsed_total, 1),
        "configs": all_results,
        "summary_baseline_10bps": {
            "n_beats": n_beats,
            "n_no_beats": n_no,
            "n_inconclusive": n_inc,
            "n_configs": len(base_verdicts),
        },
        "methodology": (
            "Per (asset, n_states) config: 5 seeds x 5 walk-forward folds. "
            "Per fold: average strat returns across seeds (seed-ensemble). "
            "Pool folds -> single OOS series. Ledoit-Wolf (2008) paired "
            "Sharpe-diff with Newey-West HAC SE. One-sided p-value "
            "(H0: Sharpe_strat <= Sharpe_BH). Verdict BEATS requires "
            "Sharpe_diff > 0 AND p < 0.05."
        ),
    }
    out_path = RESULTS_DIR / "c875_hmm_alpha_dm.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"\n[output] Results written to {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
