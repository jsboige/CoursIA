# Chronos-Foundation-Forecasting

**Asset class:** US Equities/ETF (8 ETFs)
**Cloud project ID:** 29443479

## Description

Ensemble GradientBoosting + Ridge using Chronos foundation model embeddings. Predicts returns on 8-ETF universe.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Chronos-Foundation-Forecasting"`

**QC Cloud:** Deployed as project 29443479.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | Ensemble GB + Ridge |
| Universe | 8 ETFs |
| Rebalance | Biweekly |
| Sharpe Ratio (v2) | 0.253 |

## Files

- main.py - Strategy (v2, ensemble with Chronos features)

## References

- Amazon Chronos: Learning the Language of Time Series
