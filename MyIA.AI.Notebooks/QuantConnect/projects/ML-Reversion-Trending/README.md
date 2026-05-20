# ML-Reversion-Trending (HandsOn Ex03)

**Asset class:** US Equities/ETF (5 assets)
**Cloud project ID:** None (local only)

## Description

GradientBoostingClassifier mean-reversion-in-trending. Uses Bollinger Band width, RSI, and return lags to predict next-day direction.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.375 |
| CAGR | 8.44% |
| Max Drawdown | 24.4% |
| Model | GradientBoostingClassifier |
| Rebalance | Weekly |

## Files

- main.py - Strategy (v1.0, GBM reversion/trending)
- research.ipynb - Regime detection and model comparison
## References

- Hands-On AI Trading, Section 06, Example 03
