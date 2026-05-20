# Temporal-CNN-Prediction

**Asset class:** US Equities (S&P 500)
**Cloud project ID:** None (local only)

## Description

Temporal CNN forecasting using Conv1D networks on S&P 500 price data.
Separate implementation from HandsOn Ex14 (ML-Temporal-CNN), focused on multi-layer convolutional
architectures for time-series prediction.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Resolution | Daily |
| Model | Conv1D temporal network |
| Universe | S&P 500 |

## Files

- `main.py` - Strategy (temporal CNN prediction pipeline)
- `research.ipynb` - CNN architecture experiments and feature engineering
