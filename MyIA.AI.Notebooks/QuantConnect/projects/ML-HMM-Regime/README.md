# ML-HMM-Regime (HandsOn Ex04)

**Asset class:** US Equities/ETF (SPY, TLT, GLD)
**Cloud project ID:** None (local only)

## Description

Hidden Markov Model regime detection using statsmodels MarkovRegression. Identifies bull/bear/sideways regimes on SPY returns.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.571 |
| Model | MarkovRegression (statsmodels) |
| Universe | SPY, TLT, GLD |
| Regimes | 3 (bull/bear/sideways) |

## Files

- main.py - Strategy (v1.0, HMM regime switching)
- research.ipynb - Regime persistence analysis
## References

- Hands-On AI Trading, Section 06, Example 04
