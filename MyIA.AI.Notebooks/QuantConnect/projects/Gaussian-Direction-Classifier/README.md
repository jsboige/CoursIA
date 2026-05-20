# Gaussian-Direction-Classifier

**Asset class:** US Equities (8 tech stocks)
**Cloud project ID:** None (local only)

## Description

GaussianNB direction classifier on 8 tech stocks. Uses lagged returns, RSI, volume, and volatility features to predict next-day direction.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.761 |
| CAGR | 23.1% |
| Max Drawdown | 25.6% |
| Model | GaussianNB |
| Rebalance | Daily |

## Files

- main.py - Strategy (v2.0, Gaussian direction)
