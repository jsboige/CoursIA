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
- research.ipynb - Volatility prediction features
## References

- Hands-On AI Trading, Section 06, Example 11
