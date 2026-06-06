# ML-Ensemble

**Asset class:** US Equities (30 large-cap stocks)
**Cloud project ID:** None (local only)

## Description

Ensemble ML strategy combining Ridge regression, Random Forest, and Gradient Boosting on a 30-stock universe. Weekly rebalance with monthly retraining. Uses lagged returns as features for direction prediction.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Ensemble"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Models | Ridge + RF + GradientBoosting ensemble |
| Universe | 30 large-cap stocks |
| Rebalance | Weekly |

## Files

- main.py - Strategy (269L, MLEnsembleAlgorithm)
