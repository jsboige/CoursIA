# RegimeSwitching

**Asset class:** US Equities/ETF
**Cloud project ID:** None (local only)

## Description

Momentum/mean-reversion regime switching using SMA50/SMA200 crossover. Applies momentum in trending, mean-reversion in sideways.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | SMA50/200 regime switch |
| Strategies | Momentum + Mean-reversion |

## Files

- main.py - Strategy (iter3, regime switching)
