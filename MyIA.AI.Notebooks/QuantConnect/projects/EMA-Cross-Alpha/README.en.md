# EMA-Cross-Alpha

**Asset class:** US Equities (Large-cap tech)
**Cloud project ID:** 28885488

## Description

Framework-based EMA crossover alpha strategy on 5 major tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA).
Uses the QuantConnect Alpha Model framework with `EMACrossAlpha` (fast=20, slow=50) and daily portfolio rebalance via `MultiStrategyPCM`.

The alpha model generates insights when the fast EMA crosses the slow EMA for each stock, and the portfolio construction module allocates capital accordingly.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Alpha"`
```bash
lean backtest --project .
```

**QC Cloud:** Open project 28885488 in the QuantConnect IDE and click "Backtest".

## Backtest Metrics (2015-2024)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | -0.01 |
| CAGR | 2.799% |
| Max Drawdown | 14.000% |
| Net Profit | 31.824% |
| Total Orders | 314 |
| Benchmark | SPY |
| Rebalance | Daily |
| Universe | 5 tech stocks |

> **Provenance**: QC Cloud backtest `8119728de11270cec45b8db81ed30a0b` (2026-08-05),
> project 28885488, IBKR margin, 2516 tradeable days (2015-2024). Re-run via
> QC Cloud to recompute.
>
> **Honest reading**: a Sharpe of -0.01 is a statistically null edge (PSR 0.006%),
> and a CAGR of 2.8% is below the risk-free rate — the strategy **does not beat the benchmark**.
> It is a pedagogical counter-example: a naive EMA crossover (fast=20, slow=50) on
> 5 large tech stocks underperforms the SPY buy & hold over 2015-2024. The unmeasured
> value "~1.00" previously listed here was wrong (two orders of magnitude).

## Files

- `main.py` - Strategy entry point (framework alpha model)
- `alpha_models.py` - EMACrossAlpha implementation
- `portfolio_construction.py` - MultiStrategyPCM module
- `quantbook.ipynb` - Research notebook

## References

- QC Framework: Alpha Model + Portfolio Construction pattern
- Ref: Brock et al. (1992), moving average trading rules
