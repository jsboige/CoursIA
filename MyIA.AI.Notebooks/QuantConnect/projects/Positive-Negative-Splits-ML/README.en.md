# Positive-Negative-Splits-ML (HandsOn Ex07)

**Asset class:** US Equities (Tech sector)
**Cloud project ID:** None (local only)

## Description

LinearRegression positive/negative split prediction. Uses the split factor (from the split event) and the technology-sector momentum (XLK ROC 22-day) to predict post-split drift.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Positive-Negative-Splits-ML"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 1.511 |
| CAGR | 75.72% |
| Max Drawdown | 37.60% |
| Model | LinearRegression |
| Rebalance | Event-driven (stock splits) |
| Backtest window | 2018-2024 (aligned #1630, see `docs/qc/qc-strategies-status.md` L460) |

## Files

- main.py - Strategy (v1.0, split prediction)
- research.ipynb - Earnings split analysis
## References

- Hands-On AI Trading, Section 06, Example 07
