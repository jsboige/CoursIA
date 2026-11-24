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
Project 30820857. Upload `main.py`, compile and run a backtest. Default window: **2018-01-01 → 2025-01-01** (aligned with the cross-strategy baseline #1630), adjustable with the `start_date` and `end_date` parameters (`%Y%m%d`). Optional parameters:

- `rebalance_days` (default 30);
- `mode`: `strategy` by default, `spy` and `6040` for the two references of the section [Verdict against held references](#verdict-against-held-references-21534).

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

**Verdict of this measurement (2026-08-14): NO-BEATS.** It compared the strategy's CAGR (~3.5%) with SPY's double-digit CAGR over 2018-2025, without a SPY backtest or a test. The section [Verdict against held references](#verdict-against-held-references-21534) replaces it with a tested comparison: `NO BEATS` on the coded window, `INCONCLUSIVE` out of sample.

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

## Verdict against held references (#21534)

The protocol was written in #21534 before the first backtest, on the model of #21329. For a multi-asset portfolio, the 60/40 (SPY 60%, BND 40%, rebalanced at the start of each month) is the natural reference; held SPY sets the threshold of the `NO BEATS` verdict. Both references run in the same algorithm as the strategy:

- with the same six subscriptions;
- under the same brokerage model;
- with the same 252-session warm-up.

In reference mode, `on_data` does nothing.

In reference mode only, `settings.seed_initial_prices` seeds each security's price as soon as it is subscribed: it is a precaution so that a reference's order never leaves on a zero price. The `strategy` mode does not enable it and stays the original code, which the innocuity check below verifies.

The compared series are the portfolio value at each SPY open (`shadow` trace). The tests go through `Paradox46Benchmarks/significance.py`, with a zero risk-free rate:

- Ledoit-Wolf Sharpe difference;
- stationary bootstrap;
- Newey-West difference of means.

On each window, the Holm correction covers the six p-values.

Verdict rule, written before the measurement:

- `BEATS`: positive and significant Sharpe difference (Holm < 0.05) against both references;
- `NO BEATS`: strategy Sharpe below that of held SPY;
- `INCONCLUSIVE`: all other cases.

**Innocuity check: held.** In `strategy` mode, on the coded window, the instrumented code (project 38145133) reproduces the backtest of the original code (`63302edb192f3ac25750fe0021c1016b`, project 38145130):

- 296 orders out of 296, with no difference in date, symbol or quantity;
- 27 QC statistics out of 27.

The strategy's orders are timestamped 4:00 pm New York, at the session close, on both windows; none is placed at midnight. The strategy stays in cash during its first 30 days, because the rebalancing counter starts at the start date; those sessions count in its series.

| Window | Sessions | Strategy Sharpe (zero rate) | Held SPY (zero rate) | 60/40 (zero rate) | Holm p (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Coded, 2018-01-02 → 2024-12-31 | 1761 | 0.350 | 0.758 | 0.751 | 1.0 / 1.0 | **NO BEATS** |
| Out of sample, 2025-01-02 → 2026-07-22 | 388 | 1.500 | 1.063 | 1.180 | 1.0 / 1.0 | **INCONCLUSIVE** |

QC statistics (computed by QC with its own risk-free rate). Their Sharpe ratios do not compare with those of the table above: QC subtracts a non-zero risk-free rate and starts from its own daily series, whereas the protocol uses a zero rate on the portfolio value at the open. The ranking of the portfolios can therefore change from one table to the other, and the verdict is read on the table above.

| Window | Mode | QC Sharpe (QC rate, other scale) | CAGR | Worst drawdown | Orders | Backtest |
|---|---|---|---|---|---|---|
| Coded | strategy | 0.035 | 3.58% | 24.4% | 296 | `612dcc9e67a272b2dafe85a6dc982e8b` |
| Coded | held SPY | 0.496 | 13.58% | 33.7% | 3 | `be5102e822d65d785a742dc384db68ab` |
| Coded | 60/40 | 0.378 | 8.66% | 21.7% | 147 | `d82b8a947cadca01d14cb0714f916811` |
| Out of sample | strategy | 0.989 | 22.47% | 12.1% | 76 | `fe725f78b216a529e3dbd78c29772ba2` |
| Out of sample | held SPY | 0.647 | 18.40% | 18.7% | 2 | `6cd30dea278e0861f1fe727231f53780` |
| Out of sample | 60/40 | 0.548 | 12.71% | 11.2% | 30 | `5f210726035d1da458622076e2d9d102` |

The out-of-sample backtest was requested up to 2026-10-20, but it stops on 2026-07-22: the QC nodes used cut backtests about 90 days before the current date. No parameter was tuned on this period.

**Reading.** On the coded window, the strategy is below both references in Sharpe, without the gap being significant: the raw Ledoit-Wolf p-values are 0.23 against held SPY and 0.25 against the 60/40. Against the 60/40, at an almost equal annual volatility according to QC (10.2% versus 10.1%), it returns 3.6% a year versus 8.7%, for a deeper worst drawdown. Out of sample, its Sharpe is the highest of the three, with no significant gap: over 388 sessions, the 95% bootstrap interval of the gap against held SPY runs from −0.90 to +1.67. Its mean daily return there barely exceeds that of held SPY (Newey-West, raw p 0.80), with a lower volatility (11.8% versus 14.6%). The current code therefore beats neither reference measurably, and falls below held SPY on its own window.

## Files

| File | Description |
|------|-------------|
| `main.py` | Dual-filter SMA200 + momentum rotation on 6 multi-asset ETFs; `mode`, `start_date` and `end_date` parameters, `shadow` trace (#21534) |

## References

- Hurst, B., Ooi, Y.H., Pedersen, L.H. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
