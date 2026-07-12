"""Statistical tests for walk-forward backtesting results.

Multi-seed validation via paired t-test, multi-asset validation via
Bonferroni correction. Follows the multi-seed rule: >=4 seeds, edge >= 2*std.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
from scipy import stats as sp_stats


@dataclass
class SeedTestResult:
    """Result of multi-seed statistical test."""
    metric: str
    n_seeds: int
    mean: float
    std: float
    t_stat: float
    p_value: float
    significant: bool
    edge_threshold: float
    passes_rule: bool  # edge >= 2*std (project convention)

    def to_dict(self) -> dict:
        return {
            "metric": self.metric,
            "n_seeds": self.n_seeds,
            "mean": round(self.mean, 6),
            "std": round(self.std, 6),
            "t_stat": round(self.t_stat, 4),
            "p_value": round(self.p_value, 6),
            "significant": self.significant,
            "edge_threshold": round(self.edge_threshold, 6),
            "passes_rule": self.passes_rule,
        }


def multi_seed_eval(
    seed_results: list[dict[str, float]],
    baseline_value: float = 0.0,
    metric: str = "dir_acc",
    alpha: float = 0.05,
) -> SeedTestResult:
    """Evaluate statistical significance of walk-forward results across seeds.

    One-sample t-test: H0 = the strategy metric equals baseline_value.
    Project rule: the mean edge must be >= 2 * std of the metric across seeds.

    Parameters
    ----------
    seed_results : list of dicts
        Each dict contains mean_metrics from a WalkForwardResult (one per seed).
    baseline_value : float
        Null hypothesis value (e.g., majority class accuracy).
    metric : str
        Key to extract from each seed's metrics.
    alpha : float
        Significance level.

    Returns
    -------
    SeedTestResult with t-test and rule check.
    """
    values = np.array([r[metric] for r in seed_results if metric in r])
    n = len(values)

    if n < 2:
        return SeedTestResult(
            metric=metric, n_seeds=n, mean=float(np.mean(values)) if n else 0.0,
            std=0.0, t_stat=0.0, p_value=1.0, significant=False,
            edge_threshold=0.0, passes_rule=False,
        )

    mean_val = float(np.mean(values))
    std_val = float(np.std(values, ddof=1))

    t_stat, p_value = sp_stats.ttest_1samp(values, baseline_value)

    edge = mean_val - baseline_value
    edge_threshold = 2.0 * std_val

    return SeedTestResult(
        metric=metric,
        n_seeds=n,
        mean=mean_val,
        std=std_val,
        t_stat=float(t_stat),
        p_value=float(p_value),
        significant=p_value < alpha and mean_val > baseline_value,
        edge_threshold=edge_threshold,
        passes_rule=edge >= edge_threshold,
    )


@dataclass
class MultiAssetResult:
    """Result of multi-asset statistical test with Bonferroni correction."""
    n_assets: int
    n_significant_raw: int
    n_significant_bonferroni: int
    alpha_raw: float
    alpha_bonferroni: float
    per_asset: dict[str, SeedTestResult]

    def to_dict(self) -> dict:
        return {
            "n_assets": self.n_assets,
            "n_significant_raw": self.n_significant_raw,
            "n_significant_bonferroni": self.n_significant_bonferroni,
            "alpha_raw": self.alpha_raw,
            "alpha_bonferroni": self.alpha_bonferroni,
            "per_asset": {k: v.to_dict() for k, v in self.per_asset.items()},
        }


def multi_asset_eval(
    asset_results: dict[str, list[dict[str, float]]],
    baseline_value: float = 0.0,
    metric: str = "dir_acc",
    alpha: float = 0.05,
) -> MultiAssetResult:
    """Evaluate multi-asset walk-forward results with Bonferroni correction.

    Parameters
    ----------
    asset_results : dict mapping symbol -> list of seed metric dicts.
    baseline_value : float
        Null hypothesis value for the metric.
    metric : str
        Metric key.
    alpha : float
        Family-wise significance level.

    Returns
    -------
    MultiAssetResult with per-asset tests and Bonferroni-adjusted threshold.
    """
    n_assets = len(asset_results)
    alpha_bonf = alpha / max(n_assets, 1)

    per_asset: dict[str, SeedTestResult] = {}
    for symbol, seed_metrics in asset_results.items():
        per_asset[symbol] = multi_seed_eval(
            seed_metrics, baseline_value=baseline_value,
            metric=metric, alpha=alpha_bonf,
        )

    n_sig_raw = sum(
        1 for r in per_asset.values()
        if r.significant and r.p_value < alpha
    )
    n_sig_bonf = sum(
        1 for r in per_asset.values()
        if r.significant
    )

    return MultiAssetResult(
        n_assets=n_assets,
        n_significant_raw=n_sig_raw,
        n_significant_bonferroni=n_sig_bonf,
        alpha_raw=alpha,
        alpha_bonferroni=alpha_bonf,
        per_asset=per_asset,
    )
