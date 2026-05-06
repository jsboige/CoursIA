# Markov-Regime-Detection

**Asset class:** US Equities/ETF (SPY, TLT, GLD)
**Cloud project ID:** None (local only)

## Description

Markov regime detection using statsmodels MarkovRegression. Identifies 2-regime (bull/bear) states on SPY returns.

**Consolidated from ML-HMM-Regime** (near-identical copy with same class name, same k_regimes=2, same allocation logic).

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.408 |
| Model | MarkovRegression |
| Regimes | 2 (bull/bear) |

## Files

- main.py - Strategy (v1.1, Markov regime, consolidated from ML-HMM-Regime)
