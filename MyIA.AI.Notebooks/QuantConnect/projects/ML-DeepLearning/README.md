# ML-DeepLearning

**Asset class:** US Equities (SPY, QQQ, IWM)
**Cloud project ID:** None (local only)

## Description

Deep learning direction prediction using Ridge regression as LSTM proxy. Predicts next-day direction (up/down/flat) on 3 equity ETFs using lagged open-close returns as features. Note: uses sklearn Ridge, not a real neural network (LSTM proxy pattern from Hands-On AI Trading).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-DeepLearning"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | Ridge regression (LSTM proxy) |
| Universe | SPY, QQQ, IWM   |
| Rebalance | Weekly |

## Files

- main.py - Strategy (172L, MLDeepLearningAlgorithm)
