# LSTM-Forecasting

**Asset class:** US Equities/ETF
**Cloud project ID:** None (local only)

## Description

MLPClassifier (not actual LSTM) return prediction. Uses sklearn MLPClassifier with lagged return features. Despite the name, no LSTM is used.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.525 |
| CAGR | 11.3% |
| Max Drawdown | 32.5% |
| Model | MLPClassifier (sklearn) |
| Rebalance | Daily |

## Files

- main.py - Strategy (v2.1, MLP forecasting)
