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

Measured on 2026-10-10 on QC nodes over the coded window 2018-01-01 → 2025-01-01, **before and after** the midnight-slice fix (#20264). The protocol was pre-registered on the issue before both runs (comment `c.6099402027`). The "before" column is the code on `main` at commit `a492cda2b3`, run unchanged.

| Indicator | Before the fix | Fixed code |
|---|---|---|
| Sharpe ratio | −0.026 | **0.224** |
| CAGR | 2.141% | **6.837%** |
| Max drawdown | 42.600% | **27.600%** |
| Total net profit | 15.998% | **58.917%** |
| PSR (Probabilistic Sharpe Ratio) | 0.052% | **0.637%** |
| Orders | 343 | 309 |
| Fees | 447.94 USD | 377.80 USD |
| Orders dated midnight, New York time | **27**, on 5 days | **0** |
| QC backtest | `a772737bfde57dad91cb64801eb0939c` (project 37630569) | `a8e7809afb021ce8b42e8b59d61e9e1b` (project 37630571) |

The "before" column reproduces the run published earlier (2026-08-07, `SectorRotation-honest-read-2026-08`: Sharpe −0.029, CAGR 2.118%, drawdown 42.700%, 345 orders). The two-order gap comes from data revisions between the two dates.

### The fixed defect (#20264)

At daily resolution, Lean delivers dividend and split notices in a slice dated midnight, with no price bar. The `days_since_rebalance` counter counted those slices as sessions, with two effects.

1. **Forced liquidation.** When the 21st count landed on a midnight slice, none of the five tickers had data there. The qualified list was empty and `_go_defensive()` sold everything and went 100% SHY until the next rebalance, about a month later. This happened five times: 2018-03-01, 2018-11-01, 2023-06-01, 2024-04-01 and 2024-06-24.
2. **Drifting calendar.** SHY pays a dividend every month, and QQQ, SPY, IWM and EFA several times a year, so the counter ran faster than the sessions. Four of the five forced liquidations indeed fall on the first business day of a month, in step with SHY's dividends. The 2018 rebalances fell on 03/26, 04/24, 05/22 and 06/18 before the fix, and fall on 04/03, 05/02, 06/01 and 07/02 after it.

The fix adds a guard at the top of `on_data`, before the counter increment, that skips any slice where none of the five tickers has a bar. The counter now counts sessions, as the description states. The parameters are unchanged.

### What the gap measures, and what it does not

The gap between the two columns **is not the cost of the five liquidations alone**. The corrected calendar also moves every rebalance, and for a monthly rotation the date alone weighs heavily. The gap is concentrated in 2018-2020, while later years stay close (yearly returns read from the QC equity curve):

| Year | 2018 | 2019 | 2020 | 2021 | 2022 | 2023 | 2024 |
|---|---|---|---|---|---|---|---|
| Before the fix | −16.8% | −1.8% | +1.1% | +20.7% | −19.6% | +22.2% | +18.2% |
| Fixed code | −2.5% | +7.1% | +22.1% | +20.5% | −25.6% | +20.3% | +15.5% |

In March 2020, for example, the code before the fix rebalanced on 03/20 (into SHY near the low) and then on 04/16; the fixed code does so on 03/04 and then on 04/02. This is a difference of dates, not of rules: **no strategy verdict is drawn from this gap**, as pre-registered.

### Known residual defect (#20286)

In both runs, a rebalance landing on a half-day session (13:00 close, New York time) also sends everything to SHY while the market is rising: 2019-11-29 before the fix, 2019-07-03 after it. A guard on the history length is suspected, not yet verified. This defect is not fixed here (one topic per PR), so the "fixed code" figures still include one month spent in SHY by mistake, July 2019.

**Verdict: NO-BEATS**, rendered on 2026-08-07 on the code before the fix. This measurement does not render a new one. Descriptively, the fixed code still trails SPY held over the same window in return (double-digit CAGR for SPY, against 6.8% here). Its 27.6% max drawdown, however, is no longer above SPY's, on the order of 34% in the 2020 crash.

## Honest read

On the fixed code, the dual filter (SMA200 + positive 126-day momentum) and the momentum-proportional weighting still do not protect against the adverse regimes of 2018-2025. The worst drawdown runs from 2021-12-28 to 2022-12-29:

- **Concentration.** When a single ticker passes the dual filter, it receives 100% of the portfolio. In 2022 the position is entirely in SPY in February, entirely in GLD in March, then in May and June. From February to December 2022, the portfolio never holds more than two lines.
- **Late defense.** The retreat to SHY happens only when **no** asset passes the dual filter. In 2022 it arrives only on 07/05, after SPY's first-half decline. The exit, on 12/01 into SPY and IWM, comes just before the December decline.
- **PSR ≈ 0.** With a PSR of 0.637%, the observed Sharpe is not statistically significant: this result cannot be distinguished from a random draw. Any edge claim would be misleading (rule C, PR-review-discipline §C).

**No re-tuning.** Re-optimizing the parameters (momentum lookback, rebalance period, universe) to recover a Sharpe on this single window would be overfitting until proven otherwise — exactly the bias flagged in EPIC #9768 (D2 "unfixed window"). The #20264 fix is not tuning: it makes the code do what its description states (rebalance every 21 sessions), without touching the parameters.

## Files

| File | Description |
|------|-------------|
| `main.py` | Sector rotation with momentum-weighted allocation and dual trend filter (v4) |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
- QC / Trading consolidation EPIC: #1621
- Governed by EPIC #9768 (backtest-metric drift across revisions)

See #1621 (partial contribution: honest-read of a previously-unaudited strategy).
