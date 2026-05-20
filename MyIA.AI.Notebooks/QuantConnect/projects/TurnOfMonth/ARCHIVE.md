# ARCHIVE - Turn-of-Month Effect

**Status**: ARCHIVED
**Date**: 2026-04-21
**Sharpe ceiling**: ~0.13 (2015-2026 period)

## Strategy Summary

Calendar anomaly strategy exploiting the turn-of-month effect in SPY and QQQ.
Enters 4 days before / exits 4 days after month boundary with 1.5x leverage
and SMA200 regime filter.

## Iteration History

| Version | Sharpe | CAGR  | MaxDD  | Change                              | Verdict    |
|---------|--------|-------|--------|-------------------------------------|------------|
| v1.0    | 0.103  | -     | -      | Baseline ToM window                 |            |
| v2.0    | 0.121  | -     | -      | + SMA200 regime filter              | Improved   |
| v2.1    | 0.128  | 4.8%  | 23.7%  | + QQQ dual instrument               | BEST       |
| v3.0    | -      | -     | -      | Dynamic window sizing               | REJECTED   |
| v3.1    | -      | -     | -      | Vol-targeting leverage              | REJECTED   |
| v3.2    | -      | -     | -      | Sector rotation during ToM          | REJECTED   |
| v3.3    | -      | -     | -      | VIX filter overlay                  | REJECTED   |
| v3.4    | -      | -     | -      | Intraday timing                     | REJECTED   |
| v4.0    | -      | -     | -      | Dynamic sizing (H8)                 | REJECTED   |

## Important Caveat

**This strategy was marked "PENDING" in the ESGF-2026 Stream B dashboard and
was not actively iterated or backtested during the April 2026 optimization pass.**

The iteration history above comes from prior work (pre-ESGF-2026). The v2.1 results
(Sharpe 0.128, CAGR 4.8%) are from an earlier backtest period. No new backtests
were run during the ESGF-2026 iteration cycle to confirm or improve these numbers.

## Why the Sharpe Is Low

1. **Bull market dilution**: The ToM effect is a small anomaly (typically 0.2-0.5%
   excess return per turn). In a strong bull market (2015-2026), the buy-and-hold
   SPY return overwhelms the calendar effect, making the strategy look weak.

2. **Regime dependence**: Research shows the ToM premium is higher during bear
   markets and high-volatility periods. The 2015-2026 backtest period was
   predominantly bullish.

3. **Transaction costs**: Monthly entries/exits with leverage generate significant
   trading costs that erode the thin edge.

4. **Window optimization overfitting**: The 4/4 window is "optimal" in-sample but
   sensitive to the specific backtest period. Shorter windows capture less of the
   effect; longer windows add noise.

## Research Key Findings

- **ToM existence confirmed**: t-statistic 2.38, statistically significant
- **Optimal window**: 4 days before / 3 days after is close to optimal
- **Instruments**: SPY+QQQ dual slightly better than SPY alone
- **Robustness**: Sharpe 0.36 on 2000-2025 (longer period) vs 0.128 on 2015-2026
- **VIX filter (H7)**: No incremental value — the ToM effect exists across vol regimes
- **Dynamic sizing (H8)**: No improvement — sizing doesn't amplify the weak signal
- **Bear market premium**: ToM effect is stronger in bear markets, but this doesn't
  help during extended bull periods

## Recommendation

**Abandon as a standalone strategy.** Calendar anomalies require either:
- Very low transaction costs (institutional execution)
- Combination with other signals (momentum + ToM)
- Shorter backtest periods that include bear markets

The effect is real but too thin for retail execution as a standalone approach.
Could be used as a timing overlay within a broader strategy.

## References

- McConnell & Xu (2008): Equity Returns at the Turn of the Month
- Lakonishok & Smidt (1988): Are Seasonal Anomalies Real?
- Research notebook: `research.ipynb` (6 hypotheses + 3 iteration rounds)
