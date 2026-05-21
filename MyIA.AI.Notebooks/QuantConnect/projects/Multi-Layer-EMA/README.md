# Multi-Layer-EMA

**Asset class:** US Equities/ETF
**Cloud project ID:** 28433748

## Description

Multi-layer EMA strategy with stacked lookbacks. EMA(10), EMA(20), EMA(50) alignment as entry signal.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Multi-Layer-EMA"`

**QC Cloud:** Deployed as project 28433748.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | Multi-layer EMA alignment |
| Rebalance | Daily |
| Sharpe Ratio | Baseline (see issue #143) |

## Files

- main.py - Strategy
