# Dynamic-Options-Wheel

**Asset class:** US Equities (SPY Options)
**Cloud project ID:** None (local only)

## Description

IV percentile-based dynamic options wheel on SPY. Adjusts put strike delta and call skew based on implied volatility rank.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | IV-adaptive options wheel |
| Underlying | SPY |
| DTE | ~21 days |

## Files

- main.py - Strategy (v1.0, dynamic IV wheel)
