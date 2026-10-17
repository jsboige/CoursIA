# Cloud-RiskParity-Composite

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** 30820857

## Description

Tactical rotation across six asset classes (SPY, TLT, GLD, EFA, EEM, DBC) using a dual filter: price above SMA200 AND positive 6-month momentum. Assets passing both filters receive equal weight. Rebalances every 30 days. Inspired by AQR's Hurst, Ooi, and Pedersen (2014) approach to trend-following with risk parity allocation.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Cloud-RiskParity-Composite/main.py
```

### QC Cloud
Project 30820857. Upload `main.py`, compile and run a backtest. Hard-coded period: **2018-01-01 → 2025-01-01** (aligned with the cross-strategy baseline #1630). Optional parameter `rebalance_days` (default 30).

## Backtest Metrics

Fresh backtest via QC Cloud MCP, 2026-08-14 (`RiskParity-Composite-2018-2025-aligned-status-2026-08`, project 30820857, compile `BuildSuccess`, 1761 tradeable dates, 297 orders):

| Indicator | Value | Reading |
|---|---|---|
| Sharpe ratio | **0.027** | near zero |
| CAGR | **3.50%** | below buy-and-hold SPY over the period |
| Max drawdown | **24.400%** | high |
| Total net profit | **27.282%** (+$17,435) | over the period |
| PSR (Probabilistic Sharpe Ratio) | **0.094%** | indistinguishable from noise |
| Orders | 297 | real backtest |

**Verdict: NO-BEATS.** Sharpe 0.027, CAGR ~3.5%: the dual-filter rotation does not beat buy-and-hold SPY over this window (double-digit CAGR 2018-2025). The structural ceiling of unlevered equal-weight trend-following is confirmed (see the `qc-strategies-status.md` catalog: "pedagogical counter-example").

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Dual-filter Risk Parity | 30 days | SMA200 + 6-month momentum, equal weight among passing assets |

## Midnight slice (#20264)

In daily resolution, Lean delivers dividend notices in a slice dated midnight that carries no bar, and TLT pays a dividend every month. Before the fix, when the 30-day deadline was already due at midnight, that slice triggered the rebalance. Selection and quantities were then computed on the previous day's closes, and the orders filled one session earlier. On other months, the decision was taken at 4:00 pm on the day's close. The guard at the top of `on_data` ignores any slice without a bar: every rebalance now leaves at 4:00 pm. The rebalancing days do not change, only the instant of the decision does.

Measurement before (`main` at `064dc1c732`) and after, on four pre-registered QC backtests ([protocol](https://github.com/jsboige/CoursIA/issues/20264#issuecomment-6149675428)):

| Indicator | Coded, before | Coded, after | Out of sample, before | Out of sample, after |
|---|---|---|---|---|
| Window | 2018-01-01 → 2025-01-01 | same | 2025-01-02 → 2026-07-10 | same |
| Rebalances leaving at midnight | 9 out of 80 | 0 out of 80 | 1 out of 18 | 0 out of 18 |
| Rebalances with a different selection | | 1 out of 80 | | 1 out of 18 |
| Sharpe ratio | 0.029 | 0.035 | 1.014 | 0.963 |
| CAGR | 3.49% | 3.58% | 23.01% | 22.05% |
| Max drawdown | 24.5% | 24.4% | 11.9% | 12.1% |
| Net profit | 27.14% | 27.90% | 36.98% | 35.37% |
| PSR | 0.096% | 0.102% | 45.07% | 42.56% |
| Orders | 298 | 296 | 77 | 76 |
| Backtest | `3a4eae48` | `1b75d5ce` | `d0b4101a` | `42018e5d` |

- **Coded window.** The Sharpe gap (+0.006) stays below the 0.05 threshold set by the protocol: the metrics of the previous section remain the README's, and the NO-BEATS verdict is unchanged. The before variant reproduces 298 orders and a Sharpe of 0.029, against 297 and 0.027 announced on 2026-08-14. A single selection differs: on 2018-08-01, DBC and SPY before, SPY alone after.
- **Out of sample.** The protocol rule classifies the result as a **degradation**: CAGR loses 0.95 point, beyond the 0.5-point threshold, and Sharpe loses 0.051, short of the 0.10 threshold. The gap comes down to a single decision. On 2025-02-03, the before variant decides at midnight on the Friday January 31 close and keeps EEM; the after variant decides at 4:00 pm on the Monday close and drops it, then takes it back at the next rebalance (2025-03-05).

The fix does not aim at performance: it makes every decision leave at the same time, on the close of the rebalancing day.

## Files

| File | Description |
|------|-------------|
| `main.py` | Risk parity rotation with SMA200 + momentum dual filter on 6 multi-asset ETFs |

## References

- Hurst, B., Ooi, Y.H., Pedersen, L.H. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
