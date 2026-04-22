# EMA-Cross-Alpha

**Asset class:** US Equities (Large-cap tech)
**Cloud project ID:** 28885488

## Description

Framework-based EMA crossover alpha strategy on 5 major tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA).
Uses the QuantConnect Alpha Model framework with `EMACrossAlpha` (fast=20, slow=50) and daily portfolio rebalance via `MultiStrategyPCM`.

The alpha model generates insights when the fast EMA crosses the slow EMA for each stock, and the portfolio construction module allocates capital accordingly.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Open project 28885488 in the QuantConnect IDE and click "Backtest".

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | ~1.00 |
| Benchmark | SPY |
| Rebalance | Daily |
| Universe | 5 tech stocks |

## Files

- `main.py` - Strategy entry point (framework alpha model)
- `alpha_models.py` - EMACrossAlpha implementation
- `portfolio_construction.py` - MultiStrategyPCM module
- `quantbook.ipynb` - Research notebook

## References

- QC Framework: Alpha Model + Portfolio Construction pattern
- Ref: Brock et al. (1992), moving average trading rules
