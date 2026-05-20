# Dividend-Harvesting-ML (HandsOn Ex06)

**Asset class:** US Equities (QQQ 100)
**Cloud project ID:** None (local only)

## Description

DecisionTreeRegressor dividend prediction. Predicts dividend yield using fundamental ratios. Buys top-10 predicted high-dividend stocks quarterly.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.468 |
| CAGR | 12.66% |
| Max Drawdown | 30.6% |
| Model | DecisionTreeRegressor |
| Rebalance | Quarterly |

## Files

- main.py - Strategy (v1.0, dividend yield prediction)
- research.ipynb - Dividend feature analysis
## References

- Hands-On AI Trading, Section 06, Example 06
