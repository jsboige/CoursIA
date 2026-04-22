# Stoploss-Volatility-ML (HandsOn Ex08)

**Asset class:** US Equities (KO)
**Cloud project ID:** None (local only)

## Description

Lasso regression stop-loss volatility prediction. Predicts next-day realized volatility. Adjusts stop-loss dynamically based on predicted vol.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.291 |
| CAGR | 7.83% |
| Max Drawdown | 20.0% |
| Model | Lasso |
| Universe | KO (Coca-Cola) |
| Rebalance | Daily |

## Files

- main.py - Strategy (v1.0, ML vol-adjusted stops)
- research.ipynb - Volatility feature engineering
## References

- Hands-On AI Trading, Section 06, Example 08
