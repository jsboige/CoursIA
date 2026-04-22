# Adaptive-Conformal-Risk

**Asset class:** US Equities/ETF (multi-factor)
**Cloud project ID:** None (local only)

## Description

Adaptive Conformal Inference (ACI) risk overlay on multi-factor momentum. Uses conformal prediction intervals to dynamically size positions based on prediction uncertainty.

## How to Run

**Lean CLI:**


**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | ACI risk overlay + multi-factor |
| Rebalance | Monthly |

## Files

- main.py - Strategy (v1.0, conformal risk sizing)

## References

- Romano et al. (2020), Conformalized Quantile Regression
