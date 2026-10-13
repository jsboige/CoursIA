# Markov-Regime-Detection-Index-Options

**Asset class:** S&P 500 index (SPX) and index options
**Cloud project ID:** `37338052`

## Description

Port of example **06/04/03 — Index Options** from *Hands-On AI Trading with Python, QuantConnect, and AWS* (Jared Broad et al., Wiley, 2025), repository [QuantConnect/HandsOnAITradingBook](https://github.com/QuantConnect/HandsOnAITradingBook) at commit `e025f21`.

Same regime model and same straddle expression as [06/04/02](../Markov-Regime-Detection-Equity-Options/), moved onto **SPX index options**. The book's stated reason: European style, cash settled, and no early exercise — so a short straddle cannot be assigned before expiry, which is exactly the failure mode the equity-options variant has to handle with an explicit assignment branch.

| Detected regime | Position opened |
|---|---|
| Low volatility (regime 0) | **short straddle**, nearest expiry |
| High volatility (regime 1) | **long straddle**, furthest expiry |

## What differs from the equity-options variant, and what the book keeps

- The **rollover trigger** is time based (`expiry - now < min_expiry`) rather than assignment driven, because an index straddle is never assigned early.
- `liquidate()` **with no argument** clears the whole portfolio — the book's call — rather than walking the contracts one by one.
- Starting cash is **1 000 000** (the book's) rather than 100 000: an index contract multiplier is far larger than an equity option's.

## Faithfulness, and declared deviations

The model, the regime table, the expiry filter, the straddle construction and the rollover branch are **the book's**. Five deviations are declared — the same guards as the 06/04/02 port, plus the brokerage setting the book does not make:

1. **Series length before fitting** — the book fits whatever it has; below ~100 points the fit diverges or raises.
2. **Empty expiry list** — the book already guards this one, the port keeps it.
3. **`try/except` around the fit**, with a counter published as a runtime statistic.
4. **Parameters** `start_year`, `end_year`, `cash`, `lookback_years`, whose defaults are **the book's own** (2019, 2024, 1 000 000, 3).
5. **Brokerage model** — the book sets none. The port fixes Interactive Brokers on a margin account, without which a short index straddle is refused for lack of buying power. The fees applied are therefore Interactive Brokers', not QuantConnect's default model: of the five deviations this is the only one that **moves the measurement** rather than avoiding a throw.

The first four are guards; the fifth is a setting. The performance benchmark is also pinned to the SPX index where QuantConnect takes SPY by default: the Sharpe ratio does not depend on it, the reported alpha and beta do.

The structural diff of `self.*` calls between the book's `main.py` and this port contains **additions only** — no book call was dropped.

## How to run

**QC Cloud:** project `37338052`. Parameters: `start_year`/`end_year` (default 2019/2024), `cash` (default 1 000 000), `lookback_years` (default 3), `min_expiry`/`max_expiry`/`min_hold_period` (default 180/365/7), `quantity` (default 1).
**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Markov-Regime-Detection-Index-Options"`

## Backtest metrics

Book window: 2019-01-01 → 2024-01-01, capital 1,000,000 (the book's value). Replayed through the QC MCP, project `37338052`, backtest `book-window-2019-2024`. Figures taken from `measures/qc_statistics.json`, where they are written from the platform.

| Metric | Value |
|---|---|
| Sharpe Ratio | **-1.832** |
| CAGR (`Compounding Annual Return`) | **-3.568%** |
| Drawdown | **20.700%** |
| Probabilistic Sharpe Ratio | 0.000% |
| Net Profit | **-16.602%** (-$167,190) |
| Orders | 470 |
| Fees | $470 |
| Portfolio Turnover | 0.78% |
| Alpha / Beta | -0.039 / -0.082 |
| Win rate | 44% (56% losing) |

Runtime counters of the port: 98 regime flips, **67 short straddles and 51 long straddles**, 49 rollovers, 0 fit failures, **32 empty expiry lists**. Unlike the equity variant, guard #2 did fire: on 32 scheduled days the 180-365 day filter emptied the SPX expiry list and the strategy simply held no position that day. The fit itself never failed — and there is no assignment counter, since a European index straddle cannot be assigned early.

Note that the model leans short (67 vs 51): the "low volatility" regime slightly dominates the window. The fit runs on **past** returns over a trailing three-year window: the port does not anticipate regimes, it observes them.

### Comparison against SPX held over the same period

| Arm | Sharpe | CAGR | Drawdown | Total return |
|---|---|---|---|---|
| 06/04/03 (this project) | -1.832 | -3.568% | 20.700% | **-16.602%** |
| SPX held | 0.610 | +13.92% | — | **+91.89%** |

The SPX figure is measured outside QuantConnect (index price `^GSPC` from 2018-12-28 to 2023-12-29, the 1259 sessions of the window; SPX is a price index, no dividends). Alpha and beta reported by the platform against that same benchmark: -0.039 and -0.082, consistent with a clearly positive benchmark.

**Verdict: `NO BEATS`.** The port reproduces the book's mechanics — 118 straddles opened, no fit failure — and those mechanics lose: -16.6% against +91.9% for the index held, over the same window and capital.

### Out-of-sample period

Window 2024-01-01 → 2026-01-01 (502 sessions), capital 1,000,000, same rules — the window moves through the `start_year`/`end_year` parameters, no code fork.

| Metric | Value |
|---|---|
| Sharpe Ratio | **-2.635** |
| CAGR (`Compounding Annual Return`) | **-2.400%** |
| Drawdown | **7.100%** |
| Probabilistic Sharpe Ratio | 0.000% |
| Net Profit | **-4.750%** (-$48,516) |
| Orders | 126 |
| Fees | $126 |
| Portfolio Turnover | 0.60% |
| Alpha / Beta | -0.052 / -0.133 |
| Win rate | 52% |

Runtime counters: 28 regime flips, 21 short straddles and 11 long, 25 rollovers, 0 fit failures, 20 empty expiry lists. The short lean deepens out-of-sample (21 vs 11): the "low volatility" regime dominates the 2024-2026 window, and the win rate rises to 52% — but the losses of the short straddles in a market up more than 40% carry the result anyway.

| Arm | Sharpe | Total return |
|---|---|---|
| 06/04/03, out-of-sample | -2.635 | **-4.750%** |
| SPX held, out-of-sample | 1.140 | **+43.52%** |

**Out-of-sample verdict: `NO BEATS`.** As with the equity variant, the 2024-2026 window is a strong bull market: the worst terrain for a short straddle.

## See also

- [BOOK_MAPPING.md](../../BOOK_MAPPING.md) — book inventory, rows 04/03
- [Markov-Regime-Detection](../Markov-Regime-Detection/) — example 04/01, SPY/TLT rotation
- [Markov-Regime-Detection-Equity-Options](../Markov-Regime-Detection-Equity-Options/) — example 04/02, same rules on SPY
