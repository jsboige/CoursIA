# AdaptiveAssetAllocation

**Asset class:** US Equities/ETF (diversified)
**Cloud project ID:** None (local only)

## Description

Top-4 ETFs by 6-month momentum with minimum-variance portfolio optimization. Selects from SPY, EFA, EEM, VNQ, GLD, DBC, TLT, IEF, TIP, HYG (10 ETFs, top 4).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/AdaptiveAssetAllocation"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Method | 6M momentum + min-variance |
| Universe | 10 ETFs (top 4) |
| Rebalance | Monthly |

## Research

`quantbook.ipynb` - QuantBook study of the AAA strategy (run via QC Cloud): 2008-2026 data loading (a full cycle including a crisis), momentum + min-variance implementation, sweep of the three parameters (Top N, momentum period, volatility window), comparison against SPY/QQQ benchmarks and visualizations. It concludes on the parameters retained in `main.py` (top 4, 126-day momentum, 60-day volatility). Its study universe is widened to US large caps (see the "Docker data availability" comment in the notebook); the deployed strategy (`main.py`) stays on the 10 ETFs above.

## Files

- main.py - Strategy (iter2c, adaptive allocation)
- quantbook.ipynb - Research QuantBook: parameter sweeps, benchmarks, verdict

## References

- Butler, Philbrick, Gordillo (2012), Adaptive Asset Allocation: A Primer, SSRN 2328254
