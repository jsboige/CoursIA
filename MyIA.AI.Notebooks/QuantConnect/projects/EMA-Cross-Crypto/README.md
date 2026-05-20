# EMA-Cross-Crypto

**Asset class:** Crypto (BTC, ETH)
**Cloud project ID:** None (local only)

## Description

Dual EMA crossover on cryptocurrency. Goes long when EMA(20) > EMA(60) on BTC/ETH.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | EMA 20/60 crossover |
| Universe | BTC, ETH |
| Rebalance | Daily |

## Files

- main.py - Strategy
