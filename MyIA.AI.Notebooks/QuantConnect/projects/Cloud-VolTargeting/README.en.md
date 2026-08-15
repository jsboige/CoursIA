# Cloud-VolTargeting

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** 30823587

## Description

Volatility targeting strategy with three variants. v1 targets 12% annualized volatility on SPY alone using realized vol scaling (log-returns × √252 over 21 days). v2 extends to a multi-asset portfolio (SPY, QQQ, IEF, GLD) with equal risk contribution targeting 10% annualized vol. v3 adds a 126-day momentum filter to the multi-asset approach, with a defensive retreat to IEF. Monthly rebalance across all variants. Interactive Brokers brokerage (real costs), SPY benchmark.

## How to Run

### Lean CLI

```bash
lean backtest --algorithm Cloud-VolTargeting/main.py
```

### QC Cloud

Project 30823587. Upload `main.py`, compile and run a backtest. Hard-coded period: **2018-01-01 → 2025-01-01** (aligned with the cross-strategy baseline #1630). The default variant (`version=1`, SPY only) is backtested below; pass `version=2` or `3` for the multi-asset variants.

## Backtest Metrics

Fresh backtest via QC Cloud MCP, 2026-08-07 (`VolTargeting-v1-honest-read-2026-08`, project 30823587, compile `BuildSuccess`, 1761 tradeable dates, 54 orders):

| Indicator | Value | Reading |
|---|---|---|
| Sharpe ratio | **0.207** | weakly positive |
| CAGR | **6.717%** | below buy-and-hold SPY (~13-15% over the period) |
| Max drawdown | **38.200%** | high (near SPY ~34%, without the return) |
| Total net profit | **57.671%** (+$32,854) | over the period |
| PSR (Probabilistic Sharpe Ratio) | **0.557%** | indistinguishable from noise |
| Orders | 54 | very low turnover (monthly) |

**Verdict: NO-BEATS.** Vol targeting on SPY alone underperforms buy-and-hold SPY: CAGR 6.7% for a 38.2% drawdown, Sharpe 0.207.

## Honest read (v1 variant)

v1 scales the SPY allocation from realized volatility: `allocation = vol_target / realized_vol`, clamped between 30% and 150%. Weaknesses observed over 2018-2025:

- **Lagged signal (volatility lag).** Realized volatility typically rises **after** a drawdown begins (2020 COVID crash, 2022 bear). The allocation cut therefore arrives too late to avoid the loss tail, but in time to miss the ensuing rebound.
- **30% exposure floor.** Even in high volatility, the strategy stays at least 30% invested — downside protection is partial, while upside return is curtailed.
- **Leverage in calm periods.** `max_allocation = 1.50` adds leverage when vol is low (bull markets), increasing risk without a proportional Sharpe improvement.
- **PSR ≈ 0.** The 0.207 Sharpe is not statistically significant: indistinguishable from noise. Any edge claim would be misleading (rule C, PR-review-discipline §C).

The v2 (multi-asset diversification + equal risk contribution) and v3 (+ momentum + IEF defensive) variants aim to correct these weaknesses (diversifying reduces drawdown, momentum filters declining assets), but are not backtested here: an honest read documents the baseline variant and its honest verdict, without re-tuning. Re-optimizing the vol target, lookback, or allocation bounds to recover a positive Sharpe on this single window would be overfitting until proven otherwise (EPIC #9768, D2 "unfixed window"). The strategy is shipped with its parameters coded as-is, honest verdict rendered.

## Files

| File | Description |
|------|-------------|
| `main.py` | Volatility targeting with 3 variants (v1 SPY only, v2 multi-asset equal-risk, v3 +momentum +IEF defensive) |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
- QC / Trading consolidation EPIC: #1621
- Governed by EPIC #9768 (backtest-metric drift across revisions)

See #1621 (partial contribution: honest-read of a previously-unaudited strategy).
