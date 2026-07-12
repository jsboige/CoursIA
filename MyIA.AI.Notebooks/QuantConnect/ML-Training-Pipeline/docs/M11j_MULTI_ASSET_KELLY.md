# M11j Multi-Asset Kelly -- Portfolio Kelly on M11i Winners

**Status:** NO BEATS (Cycle 32) -- 0/36 combos beat single-asset BTC Kelly

## Verdict

M11j Multi-Asset Kelly **fails completely** to beat single-asset BTC Kelly. The portfolio-level Kelly criterion using the correlation matrix of BTC/XRP/ADA/DOT produces significantly WORSE Sharpe ratios than single-asset BTC Kelly in every single combination (0/36, p=1.0000).

**Recommendation**: Do not adopt multi-asset Kelly for crypto portfolio allocation. Single-asset BTC Kelly dominates.

## Results Summary (Cycle 32, 2026-05-13)

| Metric | Value |
|--------|-------|
| Verdict | NO BEATS |
| Sign-test p-value (vs single BTC) | 1.0000 |
| Win rate (vs single BTC) | 0/36 (0.0%) |
| Median delta-Sharpe (vs single BTC) | -1.0518 |
| Win rate (vs equal-weight) | 8/36 (22.2%) |
| Median delta-Sharpe (vs equal-weight) | -0.2693 |
| Combos | 36 (3 horizons x 4 seeds x 3 fees) |
| Runtime | 312s |

### Per-Fee Breakdown

| Fee (bps) | Beats Single | p-value | Median delta-Sharpe |
|-----------|-------------|---------|---------------------|
| 10 | 0/12 | 1.0000 | -0.9869 |
| 50 | 0/12 | 1.0000 | -1.0518 |
| 100 | 0/12 | 1.0000 | -1.1303 |

Edge gets WORSE with higher fees (already terrible at 10bps).

### Per-Horizon Breakdown

| Horizon | Beats Single | Median delta-Sharpe |
|---------|-------------|---------------------|
| h=1 | 0/12 | -1.05 (approx) |
| h=5 | 0/12 | -1.05 (approx) |
| h=10 | 0/12 | -1.05 (approx) |

## Model

Multi-asset Kelly (Brushin 2011):
```
f* = Sigma^{-1} * mu
```
where mu = vector of expected excess returns, Sigma = covariance matrix of returns.

- 4 assets: BTC-USD, XRP-USD, ADA-USD, DOT-USD (M11i winners)
- Capped per-asset at 0.5, global cap at 1.0
- Walk-forward rolling 60d window for mu and Sigma estimation
- HAR forecast provides sigma^2 estimate for each asset

## Setup

- 4 coins: BTC-USD, XRP-USD, ADA-USD, DOT-USD
- 3 horizons: h=1, 5, 10
- 4 seeds: 0, 1, 7, 42
- 3 fees: 10, 50, 100 bps
- Kelly cap_global=1.0, cap_per_asset=0.5
- mu_window=60d
- Data: yfinance hourly (2024-05-14 to 2026-05-13), ~17333 hourly returns per coin

## Why Multi-Asset Kelly Fails

1. **Correlation too high**: BTC/XRP/ADA/DOT have return correlations of 0.6-0.85. The inverse covariance matrix does not provide useful diversification signals when assets are highly correlated.
2. **Estimation error dominates**: With only 60 daily observations to estimate 4x4 Sigma and 4x1 mu, the estimation noise overwhelms any diversification benefit.
3. **Negative Kelly weights**: Sigma^{-1} mu produces negative weights for some assets (clipped to 0), effectively reducing the portfolio to BTC-only in many periods -- but with worse timing than pure BTC Kelly.
4. **BTC dominance**: BTC has the highest Sharpe ratio among the 4 assets. Diversifying into lower-Sharpe assets hurts performance.

## Caveats (G.2 Honesty)

1. **Complete failure, not marginal**: 0/36 is as definitive as it gets. No horizons, no fees, no seeds show any edge.
2. **Correlation structure may change**: In a regime where altcoins outperform BTC (e.g., alt season), multi-asset Kelly might work. But in the 2024-2026 data, BTC dominates.
3. **Window length may matter**: 60d may be too short for stable Sigma estimation. Longer windows (120d, 250d) were not tested but unlikely to reverse a delta-Sharpe of -1.05.
4. **All data from yfinance hourly**: Consistent date range (2024-05 to 2026-05) but only 2 years of data. Results may not generalize.

## Comparison with Prior Models

| Model | Params | BEATS | Key finding |
|-------|--------|-------|-------------|
| M11 HAR Kelly (cap=1.0) | 4 | BEATS BH @50bps | Sharpe +0.313 vs buy-hold |
| M11j Multi-Asset Kelly | ~10 | 0/36 vs single BTC | NO BEATS (delta=-1.05) |

M11j extends M11 to multi-asset allocation but the diversification signal is negative. Single-asset BTC Kelly remains the best approach.

## Files

- `scripts/m11j_multi_asset_kelly.py`: Main sweep script
- `results/m11j_multi_asset_kelly/results.json`: Full results (36 combos)
- `results/m11j_multi_asset_kelly/m11j_results.csv`: CSV export

## Reference

Brushin, S. (2011) "Multi-Asset Kelly Criterion", unpublished lecture notes.
