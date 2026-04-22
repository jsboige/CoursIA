# ML-Trend-Scanning (HandsOn Ex01)

**Asset class:** US Equities/ETF (SPY, TLT, GLD)
**Cloud project ID:** None (local only)

## Description

RandomForestClassifier trend-scanning. Predicts next-day direction using lagged returns, volatility, and volume features on a 3-asset universe. Monthly rebalance.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.292 |
| Model | RandomForestClassifier |
| Universe | SPY, TLT, GLD |
| Rebalance | Monthly |

## Files

- main.py - Strategy (v1.0, RandomForest trend scanning)
- research.ipynb - Feature engineering and model evaluation
## References

- Hands-On AI Trading, Section 06, Example 01
