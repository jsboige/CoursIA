# ML-PCA-StatArb (HandsOn Ex13)

**Asset class:** US Equities (top 100)
**Cloud project ID:** None (local only)

## Description

PCA statistical arbitrage. Extracts principal components from top-100 stock returns, uses LinearRegression on residual mean-reversion signals.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.399 |
| CAGR | 12.65% |
| Max Drawdown | 31.8% |
| Model | PCA + LinearRegression |
| Rebalance | Daily |

## Files

- main.py - Strategy (v1.0, PCA stat arb)
- research.ipynb - Component analysis and signal evaluation
## References

- Hands-On AI Trading, Section 06, Example 13
