# BlackLitterman-Momentum

**Asset class:** US Equities/ETF (multi-asset)
**Cloud project ID:** 29816300

## Description

Black-Litterman portfolio with multi-window momentum views (1M, 3M, 6M, 12M). BL optimization produces final weights.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/BlackLitterman-Momentum"`

**QC Cloud:** Deployed as project 29816300.

## Backtest Metrics

QC Cloud backtest (2026-08-07), period 2015-01-01 → 2026-01-01 (11 years),
Interactive Brokers brokerage (realistic fees), SPY benchmark,
2766 tradeable dates, 2381 orders.

| Metric | Value |
|--------|-------|
| Sharpe ratio | 0.512 |
| CAGR | 9.982% |
| Max drawdown | 16.100% |
| PSR (Probabilistic Sharpe Ratio) | 1.989% |
| Total net profit | 184.986% ($180,804) |
| Rebalance | Monthly |

## Verdict: NO-BEATS (defensive profile, no alpha)

The strategy **does not beat buy-and-hold SPY** over the period: CAGR ~10%
slightly below SPY (≈ 11-12% over 2015-2026), Sharpe 0.512 below SPY, and
PSR ≈ 2% statistically **indistinguishable from noise** (a PSR < 10% means the
observed performance is not reliably distinguishable from a zero Sharpe).
Beyond the benchmark, the low PSR alone invalidates any alpha claim.

However, the **max drawdown (16.1%) is markedly lower** than SPY's worst
drawdowns over the same period (COVID 2020 ≈ 34%, 2022 bear market ≈ 25%) —
roughly half. The strategy therefore delivers a **defensive risk profile**
(reduced drawdown depth) at the cost of a modest return drag. This behaviour
is **consistent with the design**: the sector constraint (30% max per sector),
target volatility (15%) and Ledoit-Wolf regularized covariance structurally
dampen the magnitude of moves, in both directions.

**Honest read.** The Black-Litterman engine — combining market equilibrium
(CAPM implied returns) with multi-window momentum views (1M/3M/6M/12M) under
the He & Litterman uncertainty calibration — generates no alpha beyond US
large-cap equity exposure. It offers **disciplined diversification** (5 sectors,
15 names, bounded 1-20% weights) rather than a predictive edge. No re-tuning of
the parameters (TAU, SIGMOID_STEEPNESS, TARGET_VOL): retrospective adjustment
would be overfitting (EPIC #9768). main.py is delivered as-is; the verdict
applies to the strategy in its current state.

## Files

- main.py - Strategy (v1.0, BL momentum)

## References

- Black & Litterman (1992), Global Portfolio Optimization
