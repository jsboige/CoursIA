# HighBookToMarketFScore-QC

**Asset class:** US Equities (value stocks)
**QC projects:** 29687591 (library clone, 2026-04-05, cited by `main.py`) · 32732820 (June 2026 cloud copy: fixed 2018-2025 window; its code, read on 2026-11-08, declares no brokerage model) · 39089903 (repository code, measures of 2026-11-08, course backtest space) · 39104413 (code of the June copy, relaunched on 2026-11-08 in the same space)

## Description

Clone of **QC Strategy Library #343** (*High Book-to-Market High F-Score Quality Value* by **Louis Szeto**). Systematic value+quality strategy selecting stocks with high book-to-market filtered by Piotroski F-Score ≥ 8, equally-weighted, monthly rebalance.

## Measures (2026-11-08, #25264)

> **Reminder (#1621, #9434)**: the 2.09 / 18.44% / 24.20% figures in the `main.py` docstring are the **library page** figures, not a backtest of this repository. The catalogue later compared them with the Sharpe of an eight-year backtest (0.41) and concluded to a collapse. The measures below show that the two numbers do not cover the same window.

### What the library page publishes

Library page #343 shows **rolling windows**, recomputed at each reading: the figures change from one reading to the next while the strategy does not.

| Library page reading | OOS 1-year Sharpe | 5-year CAGR | 5-year max drawdown | 5-year PSR | 3-month return |
|---|---|---|---|---|---|
| 2026-04-05 (`main.py` docstring) | 2.09 | 18.44% | 24.20% | — | — |
| 2026-11-08 (public `strategies/read` API, `strategyId` 343) | 0.99 | 14.86% | 28% | 4.9% | -8.3% |

Between the two readings, the one-year Sharpe went from 2.09 to 0.99: the window slid by seven months, and the last quarter loses 8.3%.

### The five backtests

The repository code accepts two parameters, `start` and `end`, which fix the window (see "How to Run"). Three runs of 2026-11-08 on project 39089903, the June cloud copy for comparison, and the code of that copy relaunched on 2026-11-08:

| Run | Backtest | Launched | Window | Sharpe (QC) | CAGR | Max drawdown | PSR | Orders | Fees (% of starting capital) |
|---|---|---|---|---|---|---|---|---|---|
| Library 5-year window | `fec0c0b0ea8174206890d3c52b11ed4c` | 2026-11-08 | 2021-08-10 → 2026-08-10 | 0.507 | 17.09% | 28.0% | 7.4% | 1,539 | 2.4% |
| Library 1-year window | `64ac60f2761444e554b6664c7b5c889f` | 2026-11-08 | 2025-08-10 → 2026-08-10 | 1.707 | 43.50% | 8.2% | 71.0% | 262 | 0.5% |
| Fixed 2018-2025 window | `90e709b101113920550ef73a0bc5f285` | 2026-11-08 | 2018-01-01 → 2025-12-31 | 0.320 | 10.93% | 65.0% | 0.85% | 2,405 | 3.9% |
| June cloud copy (project 32732820) | `26976196c313a99d65f090e0af9d919e` | 2026-06-14 | 2018-01-01 → 2025-12-31 | 0.411 | 14.51% | 60.4% | 4.5% | 2,299 | 5.1% |
| Code of the June copy, relaunched (project 39104413) | `26444efa68228f367c63a1d91719c645` | 2026-11-08 | 2018-01-01 → 2025-12-31 | 0.320 | 10.93% | 65.0% | 0.85% | 2,405 | 3.9% |

**Effective end of the windows.** The course backtest space cuts backtests 90 days before the run date, without any error message: the 5-year and 1-year windows therefore stop on 2026-08-10, about three months before those of the library page read the same day.

**Sharpe.** QC's Sharpe subtracts a risk-free rate. Recomputed at a zero rate on the daily equity curve: 0.79 (5 years), 2.04 (1 year), 0.49 (2018-2025).

**Yearly return** (daily equity curve; 2021 and 2026 partial):

| Window | 2018 | 2019 | 2020 | 2021 | 2022 | 2023 | 2024 | 2025 | 2026 |
|---|---|---|---|---|---|---|---|---|---|
| 2018-2025 | -19.2% | +14.1% | +3.0% | +48.8% | +4.4% | +35.4% | +4.2% | +9.6% | — |
| 5 years (from 2021-08-10) | — | — | — | +2.0% | +1.8% | +35.4% | +4.2% | +9.9% | +63.9% |

The two windows do not hold the same portfolio at the start: their common years can differ by a few points (2022), then converge (2023, 2024).

**Dated drawdowns** (daily equity curve):

- 2018-2025: -64.0% from 2018-07-09 to 2020-03-19, recovered on 2021-02-08 (in 2020, the year loses up to 56.6% from its high);
- 5 years: -28.0% from 2024-10-18 to 2025-04-09, recovered on 2025-09-15;
- 1 year: -8.2% from 2025-09-18 to 2025-10-10, recovered on 2025-11-26.

### Reading

1. **The 2.09 and the 0.41 do not measure the same thing.** The first is a one-year out-of-sample Sharpe, read on a page that slides; the second, an eight-year Sharpe. Their gap demonstrates neither a collapse nor period overfitting.
2. **On the library windows, the repository code recovers the published order of magnitude.** 5-year drawdown: 28.0%, as on the library page read the same day. 5-year CAGR: 17.1% against 14.9%; the library window ends three months later, on a quarter at -8.3%. One-year Sharpe: 1.71 in QC's sense (2.04 at a zero rate). The windows do not coincide: this is an order of magnitude, not a point-for-point reproduction.
3. **The risk lies outside the library windows.** Between July 2018 and March 2020, the strategy loses 64% (value drawdown, then the March 2020 crash) and only regains its high in February 2021. No five-year window read in 2026 contains this episode.
4. **The long measure does not support a high Sharpe.** The PSR computed by QC stays low on the long windows: 7.4% over 5 years, 0.85% over 2018-2025 (4.9% on the library page). Only the one-year run exceeds 50%, over a single year.
5. **Fees do not explain the gap.** On the same 2018-2025 window, the June copy, whose code (read on 2026-11-08) declares no brokerage model, paid more fees (5.1% of starting capital) than the 2026-11-08 run with the brokerage model declared by `main.py` (3.9%). LEAN's default model (`DefaultBrokerageModel`, source read on 2026-11-08) already charges equities with the fee schedule that `main.py` declares: both runs pay under the same schedule, and the fee gap comes from the size of the orders (fewer of them, 2,299 against 2,405, but placed on a portfolio that grew faster), not from the schedule. Switching to brokerage fees is not what separates 2.09 from 0.41.
6. **The fundamentals feed changed between the two 2018-2025 runs.** On 2026-09-23, QuantConnect migrated its Morningstar fundamentals history: about a third of the values differ, usually by more than 20%. Ratios, per-share values and averages are now dated at their filing (median: 63 days after the period end) instead of the period end; according to the documentation, a backtest that reads them no longer sees a figure before it was public, and earlier backtests no longer reproduce. The F-Score reads four of these ratios (`operation_ratios.roa`, `current_ratio`, `gross_margin`, `assets_turnover`, `one_year` horizon) and the universe reads `valuation_ratios.pb_ratio`. The June copy read the old feed; on the same window, the 2026-11-08 run loses 3.6 CAGR points (14.5% → 10.9%) and goes from a Sharpe of 0.41 to 0.32. The code of the June copy, relaunched as is on 2026-11-08 (project 39104413), returns exactly the repository run: same statistics, same 2,405 orders, same fees, and an equity curve identical point for point. The brokerage model declared by `main.py` therefore changes nothing in this backtest: with the same code, the gap with June comes from the data read between 2026-06-14 and 2026-11-08. The fundamentals migration is the documented change over that period; this replay does not separate it from a possible rewrite of adjusted prices.
7. **The fix suggested by the earlier version of this README does not exist.** `DataNormalizationMode` has eight members (`RAW`, `ADJUSTED`, `SPLIT_ADJUSTED`, `TOTAL_RETURN`, `FORWARD_PANAMA_CANAL`, `BACKWARDS_PANAMA_CANAL`, `BACKWARDS_RATIO`, `SCALED_RAW`); none is called `POINT_IN_TIME_FUNDAMENTALS`, and this mode applies to prices, not to fundamentals. Dating at filing is now done by the data provider (point 6).

### Verdict

The library's 2.09 was not a long-term Sharpe, and the catalogue's 0.41 is not a collapse: they are two windows. On the library windows, the repository code recovers the published order of magnitude. Over eight years, the strategy earns 10.9% a year, but it goes through a 64% loss in twenty months and its PSR stays below 1%. Status: **historical**, with a measured risk profile. The decline since June over 2018-2025 (Sharpe 0.41 → 0.32) does not come from the brokerage model: the June code, relaunched on 2026-11-08, returns the same run point for point. It comes from the data, which changed between the two dates.

## How to Run

**QC Cloud:** copy `main.py`, `piotroski_score.py`, `piotroski_factors.py`, `universe.py` and `symbol_data.py` into a project. Without parameters, the window ends on 2025-01-01 and starts twelve years before the run date (the start slides with the run date). The project parameters `start` and `end` (`YYYY-MM-DD` format, both together) fix an explicit window: for instance `start = 2021-08-10`, `end = 2026-08-10` for the 5-year window above. The `score_threshold` (8 by default) and `max_universe_size` (100) parameters set the F-Score filter and the universe size.

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/HighBookToMarketFScore-QC"`; the same parameters are declared in the `parameters` key of the project's `config.json`. US fundamentals data must be available locally.

## Files

- `main.py` - Strategy (QC Strategy Library #343 clone, Piotroski F-Score value screen monthly rebalance)
- `piotroski_score.py` - F-Score computation (Profitability + Leverage/Liquidity + Operating Efficiency, 9 binary signals)
- `piotroski_factors.py` - Individual fundamental factors (ROA, CFO, ΔROA, ACCRUAL, ΔLEVER, ΔLIQUID, EQ_OFFER, ΔMARGIN, ΔTURN)
- `universe.py` - PiotroskiScoreUniverseSelectionModel (universe selection + F-Score ≥ 8 filter)
- `symbol_data.py` - Helpers to load fundamentals data

## References

- QuantConnect Strategy Library #343 — *High Book-to-Market High F-Score Quality Value* by Louis Szeto: `https://www.quantconnect.com/strategies/343`
- `main.py:5-11` docstring: library source + URL + QC Project ID 29687591 + author Louis Szeto
- QuantConnect documentation, *US Fundamental Data*, "Migration" section (read on 2026-11-08): `https://www.quantconnect.com/docs/v2/writing-algorithms/datasets/morningstar/us-fundamental-data`
- Piotroski (2000), "Value Investing: The Use of Historical Financial Statement Information to Separate Winners from Losers", *Journal of Accounting Research* 38(suppl.) — founding paper of the F-Score
- #25264 — measures in this README (library windows, 2018-2025 run, comparison with the June copy, replay of its code)
- c.1281-L3 ★★ (DynamicVIXSpyRegime-QC) — library claim misattribution pattern, reproducible arche to drain the other QC library clone READMEs
