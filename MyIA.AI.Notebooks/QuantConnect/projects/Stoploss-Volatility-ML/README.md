# Stoploss-Volatility-ML (HandsOn Ex08)

**Asset class:** US Equities (KO)
**Cloud project ID:** 29463529

## Description

Lasso regression stop-loss volatility prediction. Predicts next-day realized volatility. Adjusts stop-loss dynamically based on predicted vol.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Stoploss-Volatility-ML"`
**QC Cloud:** Project 29463529. Research notebook executed on QC Cloud (2026-05-11).

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
- research.ipynb - QC Cloud executed (2026-05-11, project 29463529). LASSO: rolling vol features 30/60/90d, weekly low return prediction, fixed vs ML stop-loss comparison, drawdown recovery, sensitivity 2-14%. Outputs captured via QC Cloud Research IDE.

## References

- Hands-On AI Trading, Section 06, Example 08
