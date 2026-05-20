# AdaptiveAssetAllocation

**Asset class:** US Equities/ETF (diversified)
**Cloud project ID:** None (local only)

## Description

Top-4 ETFs by 6-month momentum with minimum-variance portfolio optimization. Selects from SPY, QQQ, TLT, GLD, EFA, IWM.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | 6M momentum + min-variance |
| Universe | 6 ETFs (top 4) |
| Rebalance | Monthly |

## Files

- main.py - Strategy (iter2c, adaptive allocation)

## References

- Faber (2007), A Quantitative Approach to Tactical Asset Allocation
