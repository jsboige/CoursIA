# Positive-Negative-Splits-ML (HandsOn Ex07)

**Asset class:** US Equities (Tech sector)
**Cloud project ID:** None (local only)

## Description

LinearRegression positive/negative split prediction. Uses earnings surprise magnitude and historical split ratios to predict post-earnings drift.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 1.736 |
| CAGR | 90.83% |
| Max Drawdown | 42.4% |
| Model | LinearRegression |
| Rebalance | Event-driven (earnings) |

## Files

- main.py - Strategy (v1.0, split prediction)
- research.ipynb - Earnings split analysis
## References

- Hands-On AI Trading, Section 06, Example 07
