# DualMomentumNoTLT

**Asset class:** Multi-asset (SPY, QQQ, IEF, GLD, XLP)
**Cloud project ID:** 31244186 (Framework variant)

## Description

Dual momentum rotation excluding long-duration bonds (TLT). Selects top 2 assets by 12-month return among those with positive absolute momentum, with equal-weight allocation. Falls to cash when no asset passes the absolute momentum filter.

Key insight: TLT lost ~40% during 2020-2023 rate hikes. This variant uses IEF (intermediate bonds), GLD, and XLP (consumer staples) as alternatives.

## Strategy Logic

| Component | Parameters | Role |
|-----------|------------|------|
| Universe | SPY, QQQ, IEF, GLD, XLP | 5 diversified assets |
| Lookback | 252 trading days (12 months) | Momentum measurement |
| Absolute filter | 12M return > 0 | Skip negative momentum |
| Selection | Top 2 by 12M return | Relative momentum |
| Weighting | Equal weight | 50% per position |
| Rebalance | Monthly | Calendar rebalance |

## Standalone variant (`main.py`): rebalance moved out of the midnight slice (#20264)

In daily data, Lean delivers dividend notices in a slice dated midnight, which carries no trading bar. IEF pays a dividend every month, and its notice often falls on the first trading day. The month guard of `main.py` was then consumed on that slice: the rebalance decided on the previous day's prices, and its orders left at midnight to be executed at the open. On the coded window, 109 rebalances out of 120 fell at midnight.

Fix in `main.py`: the month is only consumed on a slice carrying a bar of a universe symbol. Measured on QC nodes, brokerage fees included, protocol fixed before the backtests ([#20264, c.6115262186](https://github.com/jsboige/CoursIA/issues/20264#issuecomment-6115262186)):

| Window | Variant | Midnight orders | Sharpe | CAGR | Max drawdown | Orders | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (coded) | before | 210 (101 days) | 0.339 | 8.08% | 23.6% | 233 | `a09a48809bcb4dc878e84f511dc00d65` |
| | after | 0 | 0.441 | 9.96% | 21.4% | 234 | `b2ff070974e440f64029c69473bb7af7` |
| 2025-01-01 → 2026-07-10 (out of sample) | before | 38 (17 days) | 1.094 | 28.02% | 14.1% | 42 | `a5a68f401f9cca13dda2a39dfd02d416` |
| | after | 0 | 1.203 | 30.23% | 14.0% | 42 | `bbf5126ce1eac446800cedc56c04f546` |

Sharpe computed by QC, risk-free rate included. Out of sample, the rule fixed in advance gives **no degradation**.

### Half sessions: the two missing months (#20286)

The fix above makes the rebalance decide on the first bar of the month. In July 2017 and July 2023, that bar is the Monday July 3rd one, a half session closing at 1:00 pm. On that slice, a daily-history request by bar count returns about 21 fewer bars than requested. The length guard then discarded the five symbols, and those two months went by without rebalancing.

`main.py` now requests twice as many bars and keeps the most recent ones. On a full session these are the same bars as before. Measured on QC nodes, protocol and predictions fixed before the backtests ([#20286, c.6131650205](https://github.com/jsboige/CoursIA/issues/20286#issuecomment-6131650205)). The "before" line is the "after" line of the previous table:

| Window | Variant | Rebalanced months | Sharpe | CAGR | Max drawdown | Orders | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (coded) | before | 118 / 120 | 0.441 | 9.96% | 21.4% | 234 | `b2ff070974e440f64029c69473bb7af7` |
| | after | 120 / 120 | 0.446 | 10.05% | 21.4% | 239 | `a32a1a24f317c96e5d0fe2bbb00ca583` |
| 2025-01-01 → 2026-07-10 (out of sample) | before | 19 / 19 | 1.203 | 30.23% | 14.0% | 42 | `bbf5126ce1eac446800cedc56c04f546` |
| | after | 19 / 19 | 1.203 | 30.23% | 14.0% | 42 | `91eae7e7741ff46af96b5cd83dbccc5a` |

The four predictions hold:

- the two July Mondays now have their `REBAL` line, and those are the only added dates;
- up to June 30th 2017, the orders are identical to the previous ones;
- out of sample, no first bar of a month is a half session, and the result is identical to the cent (same orders, same statistics).

On July 3rd 2017, the selection does not change (QQQ and SPY): the rebalance only adjusts quantities. On July 3rd 2023, it sells gold and moves to QQQ and SPY one month earlier than the before variant. The Sharpe gap (+0.005) stays below the 0.05 threshold fixed in advance.

These figures cover the standalone variant, not the Framework variant (measured in the French `README.md`). They are not a strategy verdict: this is the correction of two defects, measured on windows already seen. The Framework variant (`alpha_model.py`) carries the same month guard and the same history call. It is neither fixed nor measured here.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DualMomentumNoTLT"`
**QC Cloud:** Deployed as project 31244186 (Framework variant with alpha_model.py).

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | Dual momentum (no TLT) |
| Universe | SPY, QQQ, IEF, GLD, XLP |
| Rebalance | Monthly |
| Lookback | 12 months |

## Files

- main.py - Strategy (standalone version)
- alpha_model.py - Framework AlphaModel variant
- config_framework.json - QC Framework configuration

## References

- Antonacci (2014), Dual Momentum Investing
