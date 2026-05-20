# InverseVolatility-Rank (HandsOn Ex11)

**Asset class:** Futures (12 contracts)
**Cloud project ID:** 29463533

## Description

Ridge regression inverse volatility ranking on 12 futures contracts. Predicts next-month volatility and allocates inversely.

## How to Run

**Lean CLI:**

**QC Cloud:** Project 29463533. Research notebook not yet executed on QC Cloud (research node unavailable, 2026-05-11). `execution_count` set, outputs pending re-execution.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.124 |
| CAGR | 4.13% |
| Model | Ridge |
| Universe | 12 futures contracts |
| Rebalance | Monthly |

## Files

- main.py - Strategy (v1.0, inverse vol futures)
- research.ipynb - **awaiting QC Cloud execution** (project 29463533). Research node unavailable on 2026-05-11 ("No spare research nodes"). Ridge regression: 12 futures indices/energy/grains, vol features 60/90/180d, inverse-vol allocation vs equal-weight, lookback sensitivity.

## References

- Hands-On AI Trading, Section 06, Example 11
