# Markov-Regime-Detection-Equity-Options

**Asset class:** US Equities (SPY) and equity options
**Cloud project ID:** `37338046`

## Description

Port of example **06/04/02 — Equity Options** from *Hands-On AI Trading with Python, QuantConnect, and AWS* (Jared Broad et al., Wiley, 2025), repository [QuantConnect/HandsOnAITradingBook](https://github.com/QuantConnect/HandsOnAITradingBook) at commit `e025f21`.

Same model as [06/04/01](../Markov-Regime-Detection/) — statsmodels `MarkovRegression`, `k_regimes=2`, `switching_variance=True` on trailing SPY returns — but the view is expressed **in options** instead of rotating assets:

| Detected regime | Position opened |
|---|---|
| Low volatility (regime 0) | **short straddle**, nearest expiry |
| High volatility (regime 1) | **long straddle**, furthest expiry |

Both legs sit at the strike closest to the underlying. The book's expiry filter is kept: `min_expiry` 180 days, `max_expiry` 365 days, `min_hold_period` 7 days.

## Faithfulness, and declared deviations

The model, the regime table, the expiry filter, the straddle construction and the assignment handler are **the book's**. Five deviations are declared — four guards the book leaves implicit, its code being teaching code that lets several calls throw, and one brokerage setting that moves the measurement:

1. **Series length before fitting** — the book fits whatever it has; below ~100 points the fit diverges or raises.
2. **Empty expiry list** — the book calls `min()`/`max()` on a list the filter can empty.
3. **`try/except` around the fit**, with a counter published as a runtime statistic, instead of letting the scheduled handler die for the day.
4. **Parameters** `start_year`, `end_year`, `cash`, `lookback_years`, whose defaults are **the book's own** (2019, 2024, 100 000, 3): the book window replays exactly and an out-of-sample window needs no code fork.
5. **Brokerage model** — the book sets none. The port fixes Interactive Brokers on a margin account, without which a short straddle of this size is refused for lack of buying power. The fees applied are therefore Interactive Brokers', not QuantConnect's default model: of the five deviations this is the only one that **moves the measurement** rather than avoiding a throw.

The first four are guards; the fifth is a setting. The performance benchmark is also pinned to the underlying — for this variant that is already QuantConnect's default, so the call changes nothing.

The structural diff of `self.*` calls between the book's `main.py` and this port contains **additions only** — no book call was dropped.

## How to run

**QC Cloud:** project `37338046`. Parameters: `start_year`/`end_year` (default 2019/2024), `cash` (default 100 000), `lookback_years` (default 3), `min_expiry`/`max_expiry`/`min_hold_period` (default 180/365/7), `quantity` (default 1).
**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Markov-Regime-Detection-Equity-Options"`

## Backtest metrics

Book window: 2019-01-01 → 2024-01-01, capital 100,000 (the book's value). Replayed through the QC MCP, project `37338046`, backtest `book-window-2019-2024`. Figures taken from `measures/qc_statistics.json`, where they are written from the platform.

| Metric | Value |
|---|---|
| Sharpe Ratio | **-2.188** |
| CAGR (`Compounding Annual Return`) | **-6.808%** |
| Drawdown | **33.100%** |
| Probabilistic Sharpe Ratio | 0.000% |
| Net Profit | **-29.698%** (-$28,048) |
| Orders | 430 |
| Fees | $430 |
| Portfolio Turnover | 0.77% |
| Alpha / Beta | -0.06 / -0.089 |
| Win rate | 37% (63% losing) |

Runtime counters of the port: 107 regime flips, **54 short straddles and 54 long straddles**, 0 fit failures, 0 empty option chains, 0 assignments. The declared guards never fired: the strategy did open 108 straddles, and it is the outcome that is negative.

Note that the model alternates (54 short, 54 long) — it does not get stuck on one side. The fit runs on **past** returns over a trailing three-year window: the port does not anticipate regimes, it observes them.

### Comparison against SPY held over the same period

| Arm | Sharpe | CAGR | Drawdown | Total return |
|---|---|---|---|---|
| 06/04/02 (this project) | -2.188 | -6.808% | 33.100% | **-29.698%** |
| SPY held | 0.796 | +15.61% | — | **+106.16%** |

The SPY figure is measured outside QuantConnect (total return, dividends reinvested, on `SPY` from 2019-01-02 to 2023-12-29, the 4.99 years of the window). Alpha and beta reported by the platform against that same benchmark: -0.06 and -0.089, consistent with a clearly positive benchmark.

**Verdict: `NO BEATS`.** The port reproduces the book's mechanics — 108 straddles opened, no guard triggered — and those mechanics lose: -29.7% against +106.2% for the underlying held, over the same window and capital.

### Out-of-sample period

Window 2024-01-01 → 2026-01-01 (502 sessions), capital 100,000, same rules — the window moves through the `start_year`/`end_year` parameters, no code fork. The `oos-2024-2026` backtest carries `parameterSet: {'start_year': 2024, 'end_year': 2026}` and 502 tradeable dates: the parameters are applied, not merely recorded.

| Metric | Value |
|---|---|
| Sharpe Ratio | **-1.850** |
| CAGR (`Compounding Annual Return`) | **-2.475%** |
| Drawdown | **7.500%** |
| Probabilistic Sharpe Ratio | 0.000% |
| Net Profit | **-4.895%** (-$6,177) |
| Orders | 90 |
| Fees | $90 |
| Portfolio Turnover | 0.46% |
| Alpha / Beta | -0.044 / -0.205 |
| Win rate | 45% |

Runtime counters: 22 regime flips, 12 short straddles and 11 long, 0 fit failures, 0 empty chains, 0 assignments. Same profile as the book window, compressed: the model alternates, the guards never fire, and the outcome stays negative.

| Arm | Sharpe | Total return |
|---|---|---|
| 06/04/02, out-of-sample | -1.850 | **-4.895%** |
| SPY held, out-of-sample | 1.282 | **+47.84%** |

**Out-of-sample verdict: `NO BEATS`.** The 2024-2026 window is a strong bull market (+47.8% for SPY): the worst terrain for a short straddle, and the model did not flip long often enough to compensate.

## See also

- [BOOK_MAPPING.md](../../BOOK_MAPPING.md) — book inventory, rows 04/02
- [Markov-Regime-Detection](../Markov-Regime-Detection/) — example 04/01, SPY/TLT rotation
- [Markov-Regime-Detection-Index-Options](../Markov-Regime-Detection-Index-Options/) — example 04/03, same rules on SPX
