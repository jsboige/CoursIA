# ARCHIVE - Sector ETF Momentum Rotation

**Status**: ARCHIVED
**Date**: 2026-04-21
**Sharpe ceiling**: ~0.48

## Strategy Summary

Monthly rotation among 11 sector ETFs (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC)
using skip-month vol-adjusted momentum with dual regime filter (SMA200 + SMA20) and -10% stop-loss.

## Iteration History

| Version | Sharpe | CAGR  | MaxDD  | Change                              | Verdict    |
|---------|--------|-------|--------|-------------------------------------|------------|
| v1.0    | 0.216  | 6.5%  | 29.9%  | Baseline monthly rotation           |            |
| v2.1    | 0.411  | 10.8% | 30.1%  | Skip-month + vol-adjusted scores    | Improved   |
| v3.0    | 0.459  | 11.5% | 30.0%  | Dual SMA200+SMA20 regime filter     | Improved   |
| v4.0    | 0.472  | 11.1% | 25.8%  | + stop-loss -10%                    | BEST       |
| v5.0    | 0.398  | -     | -      | Proportional weights                | REJECTED   |
| v6.0    | 0.441  | -     | -      | Trailing stop cuts winners          | REJECTED   |
| v6.1    | 0.460  | -     | -      | TLT risk-off (worse MaxDD)          | REJECTED   |
| v6.2    | 0.395  | -     | -      | Target vol + SMA50 filter           | REJECTED   |

## Why Expansion Doesn't Improve

1. **Asset universe ceiling**: 11 highly correlated sector ETFs limit diversification benefit.
   Monthly rebalance frequency can't extract more alpha from these instruments.

2. **Risk-off alternatives exhausted**: TLT, XLP+XLU defensive, cash — all tested.
   None significantly improve risk-adjusted returns beyond v4.0.

3. **Parameter sensitivity**: Grid search (research.ipynb) shows best config is
   top_n=2 with lookback=252, but this overfits to backtest period. The chosen
   top_n=4 is more robust at the cost of slightly lower Sharpe.

4. **Vol adjustment trade-off**: Vol-adjusted momentum penalizes high-vol sectors
   (XLE, XLF) that often have the strongest absolute momentum. Removing vol
   adjustment loses the smoothing benefit.

## Research Key Findings

- **Best standalone config**: top_n=2, lookback=252, Sharpe 0.153 (research period)
- **Cash > TLT risk-off**: Going to cash during risk-off outperforms rotating to TLT
- **Composite momentum**: 4-window scheme (1/3/6/12m, weights 0.4/0.2/0.2/0.2) gives
  Sharpe 0.490 in research, confirming the ceiling is structural
- **12m-only momentum**: Sharpe 0.612 in research but overfits to lookback period

## Recommendation

**Abandon pure momentum rotation on this universe.** The Sharpe ceiling of ~0.48
is structural to monthly sector ETF rotation. To exceed 0.5, fundamentally different
approaches are needed:

- ML-based regime detection (replace SMA filters)
- Cross-asset momentum (add commodities, international equities)
- Intraday signals with daily rebalance
- Factor-based allocation (value, quality, low-vol) instead of pure momentum

## References

- Jegadeesh & Titman (1993): Returns to Buying Winners and Selling Losers
- Faber (2007): A Quantitative Approach to Tactical Asset Allocation
- Asness (2013): Value and Momentum Everywhere
