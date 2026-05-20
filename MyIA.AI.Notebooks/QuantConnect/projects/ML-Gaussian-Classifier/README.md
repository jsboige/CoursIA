# ML-Gaussian-Classifier (HandsOn Ex15)

**Asset class:** US Equities (top 10 tech)
**Cloud project ID:** None (local only)

## Description

GaussianNB direction classifier on top-10 tech stocks. Uses lagged returns, RSI, and MACD features.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.361 |
| CAGR | 12.49% |
| Max Drawdown | 47.4% |
| Model | GaussianNB |
| Rebalance | Daily |

## Files

- main.py - Strategy (v1.0, Gaussian NB classifier)
- research.ipynb - Feature selection and NB evaluation
## References

- Hands-On AI Trading, Section 06, Example 15
