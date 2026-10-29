# Cloud-MeanReversion-Sectors

**Asset class:** Equities (GICS sector ETFs)

**Cloud project ID:** 30822855

## Description

RSI(14) mean reversion strategy on 11 GICS sector ETFs (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC). Three variants with increasing sophistication: v1 uses raw RSI oversold/overbought signals; v2 adds an SMA200 regime filter (only trade in bull markets); v3 adds an 8% stop-loss rule. Scans daily 30 minutes after market open. Interactive Brokers brokerage (real costs), SPY benchmark.

The v1 variant, the only one measured here, buys ETFs whose RSI(14) drops below 35, most oversold first, at most three lines at 1/3 of the portfolio each. It exits above 55 or after 20 trading days held.

## How to Run

### Lean CLI

```bash
lean backtest --algorithm Cloud-MeanReversion-Sectors/main.py
```

### QC Cloud

Project 30822855. Upload `main.py`, compile and run a backtest. The `version` parameter (`v1`/`v2`/`v3`) selects the variant; without it, the code uses `v1`. Default period: **2018-01-01 → 2025-01-01** (aligned with the cross-strategy baseline #1630).

**Measurement parameters** (#23257):

| Parameter | Values | Default |
|-----------|--------|---------|
| `mode` | `strategy` (the strategy); `spy` (SPY 100% held); `6040` (SPY 60% / BND 40%); `ew11` (the universe's sector ETFs at equal weight, among those already trading) | `strategy` |
| `fix` | `on` (corrected execution, below); `off` (code before #23257, for the control) | `on` |
| `start_date`, `end_date` | `YYYY-MM-DD` dates | `2018-01-01`, `2025-01-01` |

The three reference modes rebalance on the first trading day of the month, 30 minutes after the open, at the strategy's scan time. The `shadow` chart traces the portfolio value at each SPY session open. It is the input of the significance computation (`Paradox46Benchmarks/significance.py`). Three runtime statistics are recorded:

- `reentries` counts ETFs re-selected on the day they exit;
- `short_days` counts opens where a line is short;
- `max_gross` gives the maximum gross exposure read at the open.

## Execution fix (#23257)

The daily scan handled exits first with `self.liquidate(symbol)`, then looked for entries. An ETF exiting after its 20 holding days while its RSI stayed below 35 was re-selected the same day and received `self.set_holdings(symbol, 1/3)`. At daily resolution, both orders fill at the close. `set_holdings`, computed against the not-yet-sold position, only sent the difference: the line ended at a few shares. The strategy still counted it as a full position for 20 trading days, and the slot stayed taken. The same defect was fixed on `projects/MeanReversion` (#23199).

Replaying the original code's orders finds **8 cases over 2018-2024**, each time leaving the line at 0.5% to 8.2% of the portfolio instead of 33%:

| Date | ETF | Shares sold | Shares bought back | Line weight after |
|------|-----|-------------|--------------------|-------------------|
| 2018-12-26 | XLE | 1583 | 82 | 1.7% |
| 2019-06-03 | XLE | 1530 | 32 | 0.7% |
| 2020-03-24 | XLE | 1890 | 512 | 8.2% |
| 2020-10-07 | XLE | 2074 | 200 | 3.0% |
| 2022-10-04 | XLRE | 1041 | 40 | 1.2% |
| 2023-10-04 | XLP | 589 | 16 | 0.9% |
| 2023-10-20 | XLRE | 1249 | 29 | 0.8% |
| 2023-12-08 | XLE | 1032 | 17 | 0.5% |

Over 2025 → mid-2026 there are two: XLY on 2026-03-16 (4 shares kept out of 340) and XLF on 2026-03-17 (15 out of 771). None goes short.

**Fix.** Exits are liquidated once the entries are known. An ETF re-selected on its exit day now only receives `set_holdings(symbol, 1/3)`, and the line ends at 1/3. Thresholds, variants, exit rule, regime filter, stop and cadence are unchanged. On the order replay, the fixed code has **no same-day sell-and-rebuy and no short position** on either window. Every line still held after an order weighs at least 31% of the portfolio, and the fixed code sends eight fewer orders (265 versus 273).

**Innocuity control.** The `main` code (sha256 `6cda5ec4b0c7`) and the instrumented code with `fix=off` ran on the same day over the same window. They produce the same 273 orders (date, symbol, quantity) and the same QC statistics. The instrumentation therefore changes nothing in the orders. The backtest published on 2026-08-14 has the same 273 orders by date, symbol and direction. Quantities differ by a few shares on 257 of them, and the Sharpe moves from 0.067 to 0.069. The cause of these differences between two runs of the same code is not isolated here.

**Gross exposure still exceeds 1.** It reaches 1.039 with the fix, versus 1.032 with the original code. The fix does not introduce this excess. From reading the code, it comes from new lines sized at 1/3 of the portfolio value while held lines are never brought back to 1/3. This explanation has not been measured date by date.

## Backtest Metrics

QC Cloud backtests of 2026-10-29, `version=v1`, starting capital 100,000, brokerage fees modeled by Lean. The instrumented code has sha256 `9b9a01006f3a`. Results read after `completed: true`.

**w1: 2018-01-01 → 2025-01-01** (1761 sessions, 2018-01-02 to 2024-12-31)

| Arm | QC Sharpe | CAGR | Max drawdown | PSR | Net profit | Orders |
|-----|-----------|------|--------------|-----|------------|--------|
| **`strategy`** (fixed) | **0.162** | **5.64%** | **41.0%** | 0.38% | 46.9% | 265 |
| `strategy`, `fix=off` (original code) | 0.069 | 3.79% | 41.7% | 0.15% | 29.8% | 273 |
| `spy` (reference) | 0.496 | 13.58% | 33.7% | 4.54% | 144.0% | 3 |
| `6040` (reference) | 0.378 | 8.66% | 21.7% | 2.16% | 78.9% | 147 |
| `ew11` (diagnostic) | 0.393 | 10.91% | 36.0% | 2.36% | 106.5% | 459 |

**w2: 2025-01-01 → 2026-07-01** (373 sessions, 2025-01-02 to 2026-06-30)

| Arm | QC Sharpe | CAGR | Max drawdown | PSR | Net profit | Orders |
|-----|-----------|------|--------------|-----|------------|--------|
| **`strategy`** (fixed) | **0.418** | **11.92%** | **7.7%** | 17.0% | 18.4% | 52 |
| `strategy`, `fix=off` (original code) | 0.307 | 9.97% | 7.2% | 13.4% | 15.3% | 54 |
| `spy` (reference) | 0.665 | 18.96% | 18.7% | 27.5% | 29.7% | 2 |
| `6040` (reference) | 0.59 | 13.37% | 11.2% | 24.7% | 20.7% | 30 |
| `ew11` (diagnostic) | 0.632 | 15.84% | 14.9% | 26.7% | 24.6% | 107 |

QC's Sharpe subtracts a risk-free rate. The tests below use a zero-rate Sharpe, computed on the daily returns of the `shadow` chart.

**Significance** (Ledoit-Wolf, stationary bootstrap, Newey-West). The Holm correction covers the two verdict references on one side, the diagnostic on the other:

| Window | Comparison | Zero-rate Sharpe (strategy / arm) | Holm p, Sharpe difference (Ledoit-Wolf; bootstrap) |
|--------|------------|-----------------------------------|----------------------------------------------------|
| w1 | vs `spy` | 0.40 / 0.76 | 0.64; 0.64 |
| w1 | vs `6040` | 0.40 / 0.75 | 0.64; 0.64 |
| w1 | vs `ew11` | 0.40 / 0.65 | 0.60; 0.60 |
| w2 | vs `spy` | 0.93 / 1.05 | 1.0; 1.0 |
| w2 | vs `6040` | 0.93 / 1.21 | 1.0; 1.0 |
| w2 | vs `ew11` | 0.93 / 1.15 | 1.0; 1.0 |

## Verdict: NO BEATS on both windows

The protocol (#23012, reused in #23257) gives BEATS only if the Sharpe exceeds held SPY's **and** the difference stays significant after Holm against both references. It gives NO BEATS if the Sharpe is below held SPY's, and INCONCLUSIVE otherwise. The v1 parameters predate the 2018 alignment: w1 is inside the sample of any tuning, so its verdict is only indicative. w2, out of sample, decides.

- **w2 (2025 → mid-2026): NO BEATS.** Sharpe 0.418 versus 0.665 for held SPY, CAGR 11.9% versus 19.0%. The drawdown is lower (7.7% versus 18.7%), but the zero-rate Sharpe stays below all three arms (0.93 versus 1.05 for SPY). With 373 sessions, the test has low power.
- **w1 (2018-2024): NO BEATS.** Sharpe 0.162 versus 0.496 for held SPY. The strategy returns 5.6% a year versus 13.6% for SPY, with a deeper drawdown (41.0% versus 33.7%).

**What the `ew11` diagnostic measures.** The eleven ETFs at equal weight do better than the strategy on both windows (zero-rate Sharpe 0.65 versus 0.40 on w1, 1.15 versus 0.93 on w2), with no significant difference after Holm. Picking the most oversold sectors adds nothing measurable over holding them all.

**What the fix changes.** On w1, the Sharpe goes from 0.069 to 0.162 and the CAGR from 3.8% to 5.6%. The drawdown stays at the same level (41.0% versus 41.7%). The eight residual lines each took a slot for 20 trading days with almost nothing invested, about 3% of the window's slot-days (8 × 20 out of 3 × 1761). The low exposure the registry called "near-cash" therefore comes mostly from the signal: on order dates, the strategy usually holds only two lines out of three (median on the replay), with or without the fix. The verdict does not change. No parameter re-tuning: a retrospective adjustment would be overfitting (EPIC #9768).

> **Measurement history (traceability):** (1) 2026-04-28 run on pre-#1630 code (2014-2025, 2768 days): v1 Sharpe 0.288 / DD 42.4%, v2 0.214, **v3 0.278 / DD 14.7%**; (2) 2026-08-07 run on the same stale code: v1 0.176 / DD 41.7%; (3) 2026-08-14 run, the first on the #1630-aligned code (2018-2025): v1 0.067 / DD 41.7%; (4) **the 2026-10-29 measurement above** (#23257): original code 0.069, fixed code 0.162 on the same window, plus the out-of-sample window and the held references. Pre-August 2026 figures cited in old catalogs (0.278 / 14.7%) are the **v3** variant over 2014-2025. They cannot be compared with the others without the variant and period label.

## Reading (v1 variant)

- **Value trap in downtrends.** RSI stays oversold as the decline continues, and the "buy oversold" signal accumulates losers in bear markets (Q4 2018, COVID 2020, 2022). With no regime filter, v1 stays fully exposed, hence a 41% drawdown over 2018-2024, deeper than held SPY's.
- **Concentration on the three most oversold.** The three most oversold ETFs are often those falling together (XLE appears in five of the eight re-entries in the table above).
- **No measurable edge.** Not against held SPY, not against the 60/40, not against the eleven sectors at equal weight.

The v2 (+ SMA200 filter) and v3 (+ 8% stop-loss) variants are designed to address these weaknesses but are not measured here. The execution fix applies to all three variants.

## Files

| File | Description |
|------|-------------|
| `main.py` | RSI(14) mean reversion with 3 variants (v1 pure RSI, v2 +SMA200 regime, v3 +8% stop-loss) on 11 GICS sector ETFs; same-day re-entry fixed by #23257, reference modes |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
- QC / Trading consolidation EPIC: #1621
- Governed by EPIC #9768 (backtest-metric drift across revisions)
- Measurement against held references and execution fix: #23257 (same defect on `projects/MeanReversion`: #23199)
