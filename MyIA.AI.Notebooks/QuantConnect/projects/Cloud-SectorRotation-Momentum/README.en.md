# Cloud-SectorRotation-Momentum

**Asset class:** Equities, Bonds, Commodities (ETF rotation)

**Cloud project ID:** 30821748

## Description

Momentum-weighted trend following on a 5-ETF universe (QQQ, SPY, EFA, GLD, IWM) with SHY as the defensive cash equivalent. Uses a dual filter (price above SMA200 **and** positive 6-month / 126-trading-day momentum) to select trending assets, then allocates proportionally to their rate-of-change (ROC) momentum scores. Rebalances every 21 trading days. Interactive Brokers brokerage (real costs), SPY benchmark.

## How to Run

### Lean CLI

```bash
lean backtest --algorithm Cloud-SectorRotation-Momentum/main.py
```

### QC Cloud

Project 30821748. Upload `main.py`, compile and run a backtest. Hard-coded period: **2018-01-01 → 2025-01-01** (aligned with the cross-strategy baseline #1630; the code sets no moving end date, so the window is fixed by the source dates).

## Backtest Metrics

Fresh backtest via QC Cloud MCP, 2026-08-07 (`SectorRotation-honest-read-2026-08`, 1761 tradeable dates, 345 orders):

| Indicator | Value | Reading |
|---|---|---|
| Sharpe ratio | **−0.029** | near-zero, slightly negative |
| CAGR | **2.118%** | below the risk-free rate over the period |
| Max drawdown | **42.700%** | catastrophic |
| Total net profit | **15.812%** (≈ +$12,369 on $100k) | over ~7 years |
| PSR (Probabilistic Sharpe Ratio) | **0.050%** | performance indistinguishable from noise |
| Orders | 345 (~49/year) | moderate turnover |

**Verdict: NO-BEATS.** The strategy does not beat the buy-and-hold SPY benchmark, and does so with materially higher risk. Over 2018-2025, buy-and-hold SPY posts a double-digit CAGR with a max drawdown on the order of 25-34% (2020 COVID crash + 2022 bear market); here the CAGR collapses to ~2% for a 42.7% drawdown. Risk-adjusted (Sharpe), the strategy destroys value.

## Honest read

The dual filter (SMA200 + positive 126-day momentum) and the momentum-proportional weighting do not protect against the adverse regimes of 2018-2025:

- **Concentration on upside momentum.** ROC-proportional allocation over-exposes the most volatile assets on the way up; when momentum reverses (Q4 2018, COVID 2020, 2022 bear), those positions amplify the drawdown. The SMA200 filter is reactive (it only trips after a breakdown), so the move to defensive SHY arrives too late.
- **Defensive SHY = too late.** The retreat to SHY happens only when **no** asset passes the dual filter — a lagging signal that leaves the strategy fully invested at the start of drawdowns.
- **PSR ≈ 0.** With a PSR of 0.05%, the observed Sharpe is not statistically significant: this result cannot be distinguished from a random draw. Any edge claim would be misleading (rule C, PR-review-discipline §C).

**No re-tuning.** Re-optimizing the parameters (momentum lookback, rebalance period, universe) to recover a positive Sharpe on this single window would be overfitting until proven otherwise — exactly the bias flagged in EPIC #9768 (D2 "unfixed window"). The strategy is shipped with its parameters coded as-is, honest verdict rendered.

## Files

| File | Description |
|------|-------------|
| `main.py` | Sector rotation with momentum-weighted allocation and dual trend filter (v4) |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
- QC / Trading consolidation EPIC: #1621
- Governed by EPIC #9768 (backtest-metric drift across revisions)

See #1621 (partial contribution: honest-read of a previously-unaudited strategy).
