# Vol-Ensemble-Conservative

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** See `config.json` (local-id: 818573377)

## Description

Conservative ensemble volatility forecasting combining GARCH(1,1) and HAR-RV models on six assets (SPY, EFA, EEM, TLT, GLD, DBC). Uses the maximum of the two volatility forecasts (conservative approach). Targets 8% annualized volatility (half the normal 16% target). Applies SMA200 regime filter with 50% position reduction in bear markets, and SMA50 for trade direction. Weekly rebalance. Most conservative of the three volatility strategies.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Vol-Ensemble-Conservative/main.py
```

### QC Cloud
Open the cloud project (local-id: 818573377), compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Ensemble GARCH+HAR (conservative max) | Weekly | Vol target 8%, SMA200 regime (-50% bear), SMA50 direction, 500-day window |

### Aligned baseline (2018-2025)

Standardized #1630 backbone run (QC Cloud project `33248352`, backtest `db77ae49`).

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.265 |
| CAGR | 6.142% |
| Max Drawdown | 10.40% |
| Probabilistic Sharpe Ratio | 13.6% |
| Tradeable dates | 1761 |

Interpretation: MaxDD 10.40% = tightest backbone baseline yet (beats Vol-GARCH-Target 10.80%, GlobalMacro-Regime 22.8%, HAR-RV-J-Kelly 37.1%). Positive Sharpe 0.265 but below single-GARCH Vol-GARCH-Target (0.325): the conservative overlay (max-of-ensemble HAR+GARCH forecast, half vol-target 8%, SMA200 regime -50% bear, SMA50 direction) tightened the drawdown at the cost of return, and the HAR component did not add risk-adjusted value over GARCH alone. Promoted Tier 4 -> 2 (Historique). totalOrders = 0 = wrapper extraction artifact (CAGR 6.14% implies real trades).

## Measurement against held references (#26322)

`main.py` is measured against two held references — SPY held and the 60/40 (SPY 60%, BND 40%) — plus two diagnostics: `ew6` (the six universe ETFs at equal weight) and `noregime` (the same rule without the SMA200 regime filter). The protocol is written in #26322 before the first backtest; the `mode` parameter adds these runs without touching the strategy's decision. All backtests ran on QC nodes the same day (2026-11-13, compile of head `1d12269`). Tests come from `Paradox46Benchmarks/significance.py`, at zero risk-free rate: Ledoit-Wolf Sharpe diff, stationary bootstrap and Newey-West mean diff.

- **Verdict.** It compares the strategy to SPY held and the 60/40, with Holm correction over six p-values. `BEATS` requires a positive Sharpe diff and a Holm (Ledoit-Wolf) p below 0.05 against both references. `NO BEATS` means a Sharpe below SPY held. Every other case is `INCONCLUSIVE`.
- **Diagnostics.** `ew6` and `noregime` run in a separate execution, with Holm over six p-values. `ew6` asks whether the ensemble vol-targeting adds anything over holding the equal-weight universe; `noregime`, whether the SMA200 filter improves the strategy. They do not change the verdict.

**Innocuity check: held.** On the coded window, the instrumented code (backtest `8e7e531a`) and the original code (`28f542c7`, launched the same day) each produce 884 orders and 1761 tradeable dates, with statistics identical to the cent: Sharpe 0.27, CAGR 6.148%, drawdown 10.400%, PSR 0.933%, net profit $50,485.89, final equity $151,875.62, fees −$1,508.92. The verified identity is that of counters and statistics; the order-by-order diff was not extracted.

**Windows.** The strategy only invests after accumulating 500 returns; its 250-session warm-up supplies half of them. The window-1 trace stays at $100,000 for 251 sessions: its first movement dates from 2019-01-02. The whole of 2018 is therefore spent in cash, while SPY held loses 7.0% and the 60/40 3.7% there (measured on the traces). That year counts in the measurement: it spares the strategy the 2018 drawdown, and its zero-return sessions weigh on its Sharpe.

- **Window 1**: 2018-01-02 → 2024-12-31, 1761 sessions.
- **Window 2**: 2025-01-02 → 2026-06-30, 373 sessions on the trace (QC reports 374 tradeable dates); the effective end was read on the trace.

Annualized Sharpe of the `shadow` trace, zero risk-free rate. The diff is the strategy minus the reference.

| Window | Sessions | Strategy | SPY held (diff, LW p, Holm p) | 60/40 (diff, LW p, Holm p) | Verdict |
|---|---|---|---|---|---|
| 2018-01-02 → 2024-12-31 | 1761 | 0.783 | 0.744 (+0.039; 0.920; 1.0) | 0.742 (+0.042; 0.916; 1.0) | `INCONCLUSIVE` |
| 2025-01-02 → 2026-06-30 | 373 | 0.847 | 0.983 (−0.136; 0.887; 1.0) | 1.137 (−0.290; 0.762; 1.0) | `NO BEATS` |

`ew6` and `noregime` diagnostics, same convention, separate execution. The correlation is that of daily returns.

| Window | Mode | Trace Sharpe | Correlation | Diff | LW p | Holm p |
|---|---|---|---|---|---|---|
| 2018 → 2024 | `ew6` | 0.527 | 0.625 | +0.256 | 0.453 | 1.0 |
| 2018 → 2024 | `noregime` | 0.844 | 0.989 | −0.061 | 0.217 | 0.867 |
| 2025 → 2026-06 | `ew6` | 1.813 | 0.555 | −0.965 | 0.215 | 1.0 |
| 2025 → 2026-06 | `noregime` | 0.867 | 0.998 | −0.020 | 0.570 | 1.0 |

Annualized volatility, annualized return and max drawdown of the same traces:

| Mode | Window | Volatility | Annualized return | Max drawdown |
|---|---|---|---|---|
| strategy | 2018-2024 | 8.1% | 6.2% | 10.4% |
| SPY held | 2018-2024 | 19.4% | 13.4% | 33.7% |
| 60/40 | 2018-2024 | 12.2% | 8.7% | 21.7% |
| `ew6` | 2018-2024 | 11.5% | 5.6% | 21.5% |
| `noregime` | 2018-2024 | 8.5% | 7.1% | 10.4% |
| strategy | 2025-01 → 2026-06-30 | 7.5% | 6.3% | 5.4% |
| SPY held | 2025-01 → 2026-06-30 | 17.9% | 17.3% | 18.7% |
| 60/40 | 2025-01 → 2026-06-30 | 11.1% | 12.7% | 11.2% |
| `ew6` | 2025-01 → 2026-06-30 | 12.2% | 23.8% | 9.1% |
| `noregime` | 2025-01 → 2026-06-30 | 7.6% | 6.5% | 5.4% |

QC statistics of the same backtests. The QC Sharpe subtracts a risk-free rate, the trace one does not: the two tables do not compare column for column.

| Mode | Window | QC Sharpe | CAGR | Max drawdown | PSR | Orders |
|---|---|---|---|---|---|---|
| strategy | 2018-2024 | 0.27 | 6.15% | 10.4% | 0.93% | 884 |
| SPY held | 2018-2024 | 0.483 | 13.27% | 33.7% | 4.19% | 1 |
| 60/40 | 2018-2024 | 0.371 | 8.58% | 21.7% | 2.05% | 449 |
| `ew6` | 2018-2024 | 0.171 | 5.54% | 21.5% | 0.40% | 914 |
| `noregime` | 2018-2024 | 0.345 | 7.05% | 10.4% | 1.68% | 861 |
| strategy | 2025-01 → 2026-06-30 | −0.023 | 5.57% | 5.4% | 6.35% | 76 |
| SPY held | 2025-01 → 2026-06-30 | 0.6 | 17.53% | 18.7% | 24.79% | 1 |
| 60/40 | 2025-01 → 2026-06-30 | 0.533 | 12.67% | 11.2% | 22.22% | 85 |
| `ew6` | 2025-01 → 2026-06-30 | 1.169 | 23.02% | 9.1% | 53.24% | 203 |
| `noregime` | 2025-01 → 2026-06-30 | −0.001 | 5.77% | 5.4% | 6.78% | 74 |

**Reading.** On window 1, the strategy returns less than half of SPY held (6.2% vs 13.4% per year on the traces), with 2.4× lower volatility and a three times smaller drawdown; at a zero rate it stands level with SPY held and the 60/40 (0.783 vs 0.744 and 0.742), with no measurable diff. On window 2, it returns 6.3% vs 17.3% (SPY held) with a third of the volatility, but its zero-rate Sharpe stays behind both references: `NO BEATS`, with no diff reaching significance (373 sessions).

**The Sharpe convention changes the ranking — the window-1 prediction is refuted.** The prediction written in #26322 announced `NO BEATS` on window 1. Under the QC convention, the strategy is behind SPY held (0.27 vs 0.483); at a zero rate it is ahead on point (0.783 vs 0.744). The strategy is 2.4× less volatile (8.1% vs 19.4% per year on the traces): the same risk-free deduction weighs that much more on its QC Sharpe — the mechanism documented by Vol-GARCH-Target (#21778). The measured verdict is `INCONCLUSIVE`. The other predictions: innocuity held; "strategy below or equal to `ew6`" refuted on point (0.783 vs 0.527, diff +0.256 not significant — the question stays open); "`noregime` diff not significant" held (`noregime` ahead by 0.061, LW p 0.217).

**On window 2, the vol-targeting adds nothing measurable over holding the universe.** `ew6` dominates there: trace Sharpe 1.813 vs 0.847, diff −0.965, Newey-West mean-diff raw p 0.043 (Holm 0.257). On window 1, the point ordering reverses (+0.256), without significance. Across both windows, no execution separates the strategy from the equal-weight universe significantly after Holm.

**The SMA200 filter changes nothing measurable.** Strategy and `noregime` daily returns correlate at 0.989 (window 1) and 0.998 (window 2); the diffs (−0.061, then −0.020) are never significant. The conservative overlay tightens the drawdown with no measurable Sharpe cost or gain.

**Gap with the baseline above.** The control recovers the baseline figures — Sharpe 0.27 vs 0.265, CAGR 6.148% vs 6.142%, drawdown 10.400% vs 10.40% (rounding and price refresh between June and November) — but not its PSR: 13.6% is not reproduced (0.933%). The baseline's `totalOrders = 0` was indeed an extraction artifact: the control counts 884 orders.

**Code properties, kept as-is in this measurement.** Daily returns are computed in `on_data` via `history(sym, 2, Resolution.DAILY)`, without checking that the second-to-last bar is the eve of the current one; any offset would affect the five modes alike. The account is declared on IBKR margin; the 0.25 per-asset cap and the normalization bound gross exposure. The first `w1-6040` run (`74c62256`) died with a runtime error — BND subscribed but absent from the state dictionaries — hence the guard in commit `1d12269`; the retried run (`1cdcde24`, same parameters) is the one recorded here.

**Traces and basket.** The `shadow` traces of the ten runs, the eleven backtest re-reads and the outputs of the four `significance.py` executions are deposited in the shared QC traces folder, under `26322-vol-ensemble-conservative-held-references/` (the full path is read in the consignation PR). The strategy is registered as a candidate in the weekly correlation-matrix basket (#19821 brick 4), declared default variant: `w1-strategy`.

## Files

| File | Description |
|------|-------------|
| `main.py` | Conservative ensemble volatility targeting (max of GARCH + HAR) with regime filter |
| `config.json` | Project configuration (local-id) |
| `research.ipynb` | Research notebook with ensemble model comparison and conservative parameter analysis |

## References

- Bollerslev, T. (1986). *Generalized Autoregressive Conditional Heteroskedasticity*. Journal of Econometrics.
- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
