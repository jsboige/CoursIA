# BlackLitterman-Momentum

**Asset class:** US Equities/ETF (multi-asset)
**Cloud project ID:** 29816300

## Description

Black-Litterman portfolio with multi-window momentum views (1M, 3M, 6M, 12M). BL optimization produces final weights.

## How to Run

**Lean CLI:**


**QC Cloud:** Deployed as project 29816300.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | Black-Litterman + momentum views |
| Lookbacks | 1M, 3M, 6M, 12M |
| Rebalance | Monthly |

## Files

- main.py - Strategy (v1.0, BL momentum)

## References

- Black & Litterman (1992), Global Portfolio Optimization
