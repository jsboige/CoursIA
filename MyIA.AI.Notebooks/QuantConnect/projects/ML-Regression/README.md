# ML-Regression

**Asset class:** US Equities (20 large-cap stocks)
**Cloud project ID:** None (local only)

## Description

Ridge regression strategy predicting next-day returns on a 20-stock universe. Uses lagged open-close returns as features. Bi-weekly rebalance with monthly retraining. Selects top-N stocks by predicted return.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Regression"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | Ridge regression |
| Universe | 20 large-cap stocks |
| Rebalance | Biweekly |

## Files

- main.py - Strategy (227L, MLRegressionAlgorithm)
