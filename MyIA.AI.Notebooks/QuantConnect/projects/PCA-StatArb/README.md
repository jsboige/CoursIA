# PCA-StatArb

**Asset class:** US Equities (top 100)
**Cloud project ID:** None (local only)

## Description

PCA statistical arbitrage using numpy/scipy PCA (non-QC Cloud compatible, see PCA-StatArbitrage for sklearn version).

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | PCA + residual mean-reversion |
| Universe | Top 100 US equities |

## Files

- main.py - Strategy (numpy PCA version)

## References

- Avellaneda & Lee (2010), Statistical Arbitrage
