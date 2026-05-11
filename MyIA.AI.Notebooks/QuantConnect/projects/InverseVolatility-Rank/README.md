# InverseVolatility-Rank (HandsOn Ex11)

**Asset class:** Futures (12 contracts)
**Cloud project ID:** None (local only)

## Description

Ridge regression inverse volatility ranking on 12 futures contracts. Predicts next-month volatility and allocates inversely.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

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
- research.ipynb - **awaiting QC Cloud execution** -> `../../_pending_execution/InverseVolatility-Rank-research.ipynb` (Ridge regression: 12 futures indices/energy/grains, vol features 60/90/180d, inverse-vol allocation vs equal-weight, lookback sensitivity). QC Cloud project 29463533. See tracking issue for execution checklist.

## References

- Hands-On AI Trading, Section 06, Example 11
