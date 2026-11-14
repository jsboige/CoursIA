"""C875 per-fold diagnostic for the 2 BEATS configs.

Checks whether the pooled DM significance is driven by consistent per-fold
edge or by 1-2 outlier folds. G.9 (doubt before claiming).
"""
from __future__ import annotations
import sys
from pathlib import Path
import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from c875_hmm_alpha_dm_validation import (  # noqa: E402
    load_returns, build_joint_features, walk_forward_hmm_alpha,
    SEEDS, N_FOLDS, COST_BPS_BASELINE, COST_BPS_STRESS, ANNUALIZE,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402


def per_fold_table(wf_df: pd.DataFrame) -> pd.DataFrame:
    """Compute per-fold (seed-averaged) Sharpe strat, Sharpe BH, delta."""
    rows = []
    for fold in sorted(wf_df["fold"].unique()):
        sub = wf_df[wf_df["fold"] == fold].dropna(subset=["sharpe_strat"])
        sub = sub[sub["strat_returns"].apply(len) > 0]
        if len(sub) == 0:
            continue
        lens = sub["strat_returns"].apply(len).unique()
        mn = int(min(lens)) if len(lens) > 1 else int(lens[0])
        strat = np.stack([s[:mn] for s in sub["strat_returns"].values]).mean(axis=0)
        bh = np.stack([b[:mn] for b in sub["bh_returns"].values]).mean(axis=0)
        s_s = np.mean(strat) / np.std(strat) * ANNUALIZE if np.std(strat) > 0 else 0
        s_bh = np.mean(bh) / np.std(bh) * ANNUALIZE if np.std(bh) > 0 else 0
        # Per-fold DM (low power but shows direction)
        _, _, sdiff, se = ledoit_wolf_sharpe_diff_se(strat, bh)
        t = sdiff / se if se and se > 1e-12 else float("nan")
        rows.append({
            "fold": fold,
            "n_days": mn,
            "n_seeds": len(sub),
            "sharpe_strat": round(s_s, 2),
            "sharpe_bh": round(s_bh, 2),
            "delta": round(s_s - s_bh, 2),
            "t_fold": round(t, 2) if not np.isnan(t) else "nan",
            "mean_trades": int(sub["n_trades"].mean()),
        })
    return pd.DataFrame(rows)


def main() -> int:
    print("[diag] Loading data...")
    returns = load_returns()
    joint = build_joint_features(returns)

    for label, asset, n_states, is_joint in [
        ("ETH 3 states", "ETH", 3, False),
        ("SOL 4 states", "SOL", 4, False),
    ]:
        print(f"\n{'=' * 70}")
        print(f"  {label} - per-fold diagnostic (5 seeds)")
        print(f"{'=' * 70}")
        for cost_bps, cost_label in [(COST_BPS_BASELINE, "10bps"),
                                     (COST_BPS_STRESS, "50bps")]:
            print(f"\n--- {cost_label} ---")
            if is_joint:
                wf = walk_forward_hmm_alpha(
                    None, n_states, SEEDS, N_FOLDS, cost_bps,
                    feature_df=joint, btc_returns_for_joint=returns["BTC"],
                )
            else:
                wf = walk_forward_hmm_alpha(
                    returns[asset], n_states, SEEDS, N_FOLDS, cost_bps,
                )
            tbl = per_fold_table(wf)
            print(tbl.to_string(index=False))
            n_pos = (tbl["delta"] > 0).sum()
            n_neg = (tbl["delta"] < 0).sum()
            print(f"\nFolds: {n_pos} positive delta, {n_neg} negative delta "
                  f"(out of {len(tbl)})")
            print(f"Median delta: {tbl['delta'].median():.2f}, "
                  f"mean: {tbl['delta'].mean():.2f}")
            # Sign test (are deltas consistently positive?)
            from scipy.stats import binomtest
            if len(tbl) > 0:
                bt = binomtest(n_pos, len(tbl), p=0.5, alternative="greater")
                print(f"Sign-test (H0: median delta <= 0): p={bt.pvalue:.4f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
