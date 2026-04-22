# Clustering-Fundamentals-ML (HandsOn Ex10)

**Asset class:** US Equities (top 50)
**Cloud project ID:** None (local only)

## Description

Fundamental factor clustering using Z-score composite ranking (P/E, ROE, debt ratio, earnings growth) to select top stocks.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.244 |
| CAGR | 7.68% |
| Max Drawdown | 44.8% |
| Model | Z-score composite rank + KMeans |
| Rebalance | Monthly |

## Files

- main.py - Strategy (v4, fundamental clustering)
- research.ipynb - Factor analysis and cluster evaluation
## References

- Hands-On AI Trading, Section 06, Example 10
