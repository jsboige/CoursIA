# EMA-Cross-Alpha

**Asset class:** US Equities (Large-cap tech)
**Cloud project ID:** 28885488

## Description

Framework-based EMA crossover alpha strategy on 5 major tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA).
Uses the QuantConnect Alpha Model framework with `EMACrossAlpha` (fast=20, slow=50) and daily portfolio rebalance via `MultiStrategyPouchesPCM`.

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

## Shared module non-regression (#20188)

Since #21140, `main.py` imports `MultiStrategyPouchesPCM` from `SharedPCM/pouches_pcm.py` instead of the local copy `portfolio_construction.py`. Two QC Cloud backtests run on 2026-10-26, with the default parameters and the window 2015-01-01 → 2024-12-31, check that this change alters no order:

- **A**: the `main` code at commit `54f9b9eec1`, with the shared module;
- **B**: the same `main.py` and `alpha_models.py`, with the old `portfolio_construction.py` copy taken at the commit before the migration (`fb3d05db0a^`). The project has a single pouch. The `additive=False` argument, which the old copy does not know, is removed from the call: the non-additive mode is the old copy's only behaviour.

A and B carry the same instrumentation, which places no order. It records the portfolio value every day at midnight, warm-up included (60 sessions). At the end of the backtest it computes a SHA-256 fingerprint per year of the orders (id, date, security, quantity, status, price) and of the recorded values.

| | A (shared module) | B (old copy) |
|---|---|---|
| Orders | 3,812 | 3,812 |
| Recorded values | 3,739 | 3,739 |
| Last recorded value | 2,145,082.06 | 2,145,082.06 |
| Sharpe (QC) | 1.12 | 1.12 |
| CAGR | 35.691% | 35.691% |
| Max drawdown | 37.4% | 37.4% |

The yearly fingerprints are equal: 10 of 10 for the orders, 11 of 11 for the values. The 27 QC statistics are equal, turnover included. The migration therefore does not change the project's behaviour. Traces kept outside the repository: `QC-traces/20188-nr/`.

These figures differ from those of the "Backtest Metrics" section above. That section measures the code of cloud project 28885488, which is not the repository code (checked on 2026-10-26); the re-measurement is tracked in #22654.

## Files

- `main.py` - Strategy entry point (framework alpha model)
- `alpha_models.py` - EMACrossAlpha implementation
- `SharedPCM/pouches_pcm.py` (QC project library) — `MultiStrategyPouchesPCM`, the canonical pouch PCM imported by `main.py` (extraction #19821 brick 1, dedup slice)
- `quantbook.ipynb` - Research notebook

## References

- QC Framework: Alpha Model + Portfolio Construction pattern
- Ref: Brock et al. (1992), moving average trading rules
