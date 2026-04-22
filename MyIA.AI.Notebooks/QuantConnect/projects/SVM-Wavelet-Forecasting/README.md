# SVM-Wavelet-Forecasting

**Asset class:** Forex
**Cloud project ID:** None (local only)

## Description

SVM regression with wavelet-decomposed features for FX forecasting. Decomposes price series then applies SVR on denoised features.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | SVR + wavelet decomposition |
| Asset | Forex pairs |

## Files

- main.py - Strategy
