# SectorMomentum

**Asset class:** US Equities + Bonds + Gold (SPY, TLT, GLD)
**Cloud project ID:** None (local only)
**Status:** ARCHIVED (Sharpe ceiling ~0.56)

## Description

Dual momentum strategy with composite multi-lookback (1, 3, 6, 12 month, weights 0.4/0.2/0.2/0.2) on 3 assets: SPY (risk-on), TLT (bonds), GLD (gold).

When SPY has positive absolute momentum AND is above SMA200 AND outperforms TLT/GLD: hold SPY at 98% of the portfolio (see "Refused buys" below).
Otherwise: rotate to the better-performing defensive asset (TLT or GLD).
Daily SMA200 exit protection (intra-month stops if SPY breaks below SMA200).

**Archived because:** Sharpe ceiling ~0.56 for dual momentum on 3-5 assets. Target of 0.8 requires a fundamentally different approach. See ARCHIVE.md for full details.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/SectorMomentum"`
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

### Current code

Measured on QC backtest nodes, brokerage fees included, after fixes #20264, #20286 and #20388. Sharpe computed by QC, risk-free rate included:

| Window | Sharpe | CAGR | Worst drawdown | Orders | Backtest |
|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (coded) | −0.014 | 1.88% | 31.7% | 118 | `823521a0e0b62048e9d70beab0e99e6d` |
| 2025-01-01 → 2026-07-10 (out of sample) | 1.397 | 44.62% | 18.8% | 10 | `f20b86164adec7106643bc01483166d2` |
| 2015-01-01 → 2026-07-10 | 0.240 | 6.85% | 31.7% | 128 | `98cf0d0fb42825ff9885c93f56647ed8` |

The following sections trace, in order, what each fix changed.

### Historical table: not reproduced

This README used to report, for "2015-2026", a Sharpe of 0.555, a CAGR of 13.0% and a worst drawdown of 22.8% (monthly rebalancing of entries, daily SMA200 exit). Those values do not reproduce (#20264). The `main` code at `0d7487cec6`, run on QC nodes, yields:

- over the 2015-01-01 → 2026-07-10 window: Sharpe 0.480, CAGR 11.48%, worst drawdown 22.8%;
- over the window coded in `main.py` (2015-01-01 → 2024-12-31): Sharpe 0.275, CAGR 6.85%, worst drawdown 22.8%.

### Month guard and midnight slice (#20264)

In daily resolution, Lean delivers TLT's monthly dividend notice alone, in a slice dated midnight, with no bar. The `rebalance_month` guard consumed the month on that slice: the order left at midnight and filled at the same day's open, on the previous day's closes. On other months it left at the close of the first session and filled at the next open. The fix only consumes the month on a slice carrying an SPY, TLT or GLD bar. The daily SMA200 exit is untouched.

Pre-registered measurement on #20264 before any backtest. Before = `main` at `0d7487cec6`, after = this fix; outside the coded window, only the two date lines change. Six backtests on QC nodes, each read at `completed: true`, orders re-read at the source until the statistics count matched.

| Window | Dates | Midnight orders before → after | Orders | QC Sharpe | CAGR | Worst drawdown |
|---|---|---|---|---|---|---|
| coded | 2015-01-01 → 2024-12-31 | 71 (44 months) → 0 | 95 → 111 | 0.275 → −0.096 | 6.85 → 0.53% | 22.8 → 38.2% |
| out of sample | 2025-01-01 → 2026-07-10 | 4 (3 months) → 0 | 5 → 6 | 1.419 → 1.261 | 45.96 → 40.83% | 19.2 → 19.2% |
| historical table | 2015-01-01 → 2026-07-10 | 75 (47 months) → 0 | 100 → 118 | 0.480 → 0.157 | 11.48 → 5.26% | 22.8 → 38.2% |

Out of sample, the verdict fixed in advance is **`DEGRADATION`**: the Sharpe gap (−0.158) and the CAGR gap (−5.13 pt) exceed the thresholds (−0.10 and −0.5 pt).

**A second defect weighs on both columns.** `set_holdings(..., 1.0)` is sent while the previous position is not yet sold: sells leave as `MarketOnOpen` and are not executed at the time of the buy. The margin account then refuses the buy ("Insufficient buying power"), and the book stays in cash until the next rebalance, while `in_spy` believes it is invested. Refused buys, before → after: 8 → 10 on the coded window, 0 → 1 out of sample, 8 → 11 on the historical-table window. Not the same months.

An off-QC estimate (adjusted closes, return of the target asset during each cash period) quantifies those refusals. On the coded window, they saved 5.2% for the before variant and cost 14.8% for the after variant. They explain about a third of the final-wealth gap. The rest comes from decisions taken one day later, on different closes. Out of sample, the gap is almost entirely one refused SPY buy on 2026-05-01 in the after variant (missed SPY return: 5.4%).

A Sharpe that moves by 0.37 for a one-day calendar shift does not describe a robust strategy. These figures measure the defects, not the strategy, which stays archived. The buying-power defect is tracked in #20388.

QC backtest ids, before / after:
- coded: `f324e3f5b1ad19720069b8619e4c41f6` / `d1169673f6ec0f798cb1cd644de0993b`
- out of sample: `5df75d4a31c556aeca917cc0b0d2540e` / `db52460299013407854f1a83940d37fa`
- historical table: `c696e01af0a4feb63ea32fac06fa8507` / `b307b836ccde0930031371b122fc3af8`

### Half sessions (#20286)

When July 3rd falls on a Monday, it is both the first trading day of the month and a half session closing at 1:00 pm New York time: in 2017 and 2023 on the windows above. On the closing slice of a half session, `history()` returns about 21 fewer daily bars than requested (measured in #20286 on another project). `_composite_momentum` requested `max_lookback` bars (252) and returned `None` below that. The month was already marked as handled, and `on_data` returned without writing anything to the log: July 2017 and July 2023 went by without rebalancing. The daily SMA200 exit calls the same function for TLT and GLD: on a half session it was postponed to the next session.

Fix in `main.py`: `_composite_momentum` requests twice the bars and keeps the latest 252. On a full session these are the same bars as before. No log line shows the short history: the cause is deduced from the code, and the return of the missing months with this single change confirms it.

Measured on QC nodes, brokerage fees included, protocol fixed before the backtests ([#20286, c.6117521094](https://github.com/jsboige/CoursIA/issues/20286#issuecomment-6117521094)). The before variant reuses the "after" backtests of the previous section, whose code is that of `main` (fingerprints compared):

| Window | Variant | Rebalanced months | Sharpe | CAGR | Worst drawdown | Orders | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (coded) | before | 118 / 120 | −0.096 | 0.53% | 38.2% | 111 | `d1169673f6ec0f798cb1cd644de0993b` |
| | after | 120 / 120 | −0.081 | 0.78% | 38.2% | 112 | `a90623a7e25fe53321d26d9228d4a3a1` |
| 2025-01-01 → 2026-07-10 (out of sample) | before | 19 / 19 | 1.261 | 40.83% | 19.2% | 6 | `db52460299013407854f1a83940d37fa` |
| | after | 19 / 19 | 1.261 | 40.83% | 19.2% | 6 | `bbf4f63bc43a7e460835b39057542615` |
| 2015-01-01 → 2026-07-10 (historical table) | before | 137 / 139 | 0.157 | 5.26% | 38.2% | 118 | `b307b836ccde0930031371b122fc3af8` |
| | after | 139 / 139 | 0.169 | 5.49% | 38.2% | 119 | `c62cedc7e6b7a29582d9a3c6bb2fb933` |

Sharpe computed by QC, risk-free rate included. The four predictions fixed in advance held:

- the rebalances of the Mondays July 3rd 2017 and 2023 return on both windows containing them, as `[RISK ON]` both times;
- before 2017-07-03, the orders are identical (date, symbol, quantity: 38 out of 38); the allowed exception for an SMA200 exit on a half session was not used, the 11 SMA200 exits have the same dates before and after;
- the rebalance dates are the previous ones, plus the two Mondays;
- out of sample, no month starts with a half session, and the two variants are identical to the cent.

The 2017-07-03 rebalance sends no order: the book is already invested in SPY. The 2023-07-03 one buys SPY. Before the fix, the book had stayed in cash since the refused buy of 2023-06-01 (#20388) and only bought SPY back on 2023-08-01: the half-session defect extended by one month a cash period opened by the buying-power defect. Orders differ only from that Monday on. The count of refused buys does not change (10, 1 and 11). The Sharpe gap (+0.015 on the coded window, +0.012 on the historical-table one) stays below the 0.05 threshold fixed in advance: the figures of the previous section are not rewritten. This is not a strategy verdict: this is the correction of a defect, measured on windows already seen.

### Refused buys (#20388)

The backtest account is a margin account, leverage 2. In daily resolution every order becomes a `MarketOnOpen`, and a buy is checked twice: at submission, then at the next open, in submission order. `set_holdings(target, 1.0)` left before the `liquidate`s: at the open, the buy was checked against the old position, not yet sold, and refused ("Insufficient buying power"). The book stayed in cash until the next rebalance, while `in_spy` believed it invested.

Fix in `main.py`: a `_rotate_to` function replaces the three rotations. It computes the target quantity before any sell, as `set_holdings` did, sends the sells, then the buy, at 98% of the portfolio instead of 100%. A counter writes every refused order to the log (`REFUSED`), and the end line carries `done refused=N`.

Measurement fixed before the backtests ([#20388, c.6145097278](https://github.com/jsboige/CoursIA/issues/20388#issuecomment-6145097278)), with the decision rules of #20264. The before variant reuses the "after" backtests of the previous section. The first arm (sells first, target 1.0) still left 4 refused buys on each of the two long windows. Those are four GLD exits, refused at submission while the GLD line was still held: free margin was short by less than 1% of the requested margin. The second arm, planned by the protocol (target 0.98), leaves none. That is the retained one.

| Window | Variant | Refused buys | Sharpe | CAGR | Worst drawdown | Orders | Backtest |
|---|---|---|---|---|---|---|---|
| coded | before | 10 | −0.081 | 0.78% | 38.2% | 112 | `a90623a7e25fe53321d26d9228d4a3a1` |
| | sells first, 1.0 | 4 | −0.084 | 0.65% | 40.0% | 111 | `d7d9a30a98027647d70ced57b03a2898` |
| | sells first, 0.98 | 0 | −0.014 | 1.88% | 31.7% | 118 | `823521a0e0b62048e9d70beab0e99e6d` |
| out of sample | before | 1 | 1.261 | 40.83% | 19.2% | 6 | `bbf4f63bc43a7e460835b39057542615` |
| | sells first, 1.0 | 0 | 1.406 | 45.57% | 19.2% | 5 | `54920a832f63325978f8961b64ad08ca` |
| | sells first, 0.98 | 0 | 1.397 | 44.62% | 18.8% | 10 | `f20b86164adec7106643bc01483166d2` |
| historical table | before | 11 | 0.169 | 5.49% | 38.2% | 119 | `c62cedc7e6b7a29582d9a3c6bb2fb933` |
| | sells first, 1.0 | 4 | 0.186 | 5.83% | 40.0% | 117 | `7467a7cf8f77510757fe72be1c35d815` |
| | sells first, 0.98 | 0 | 0.240 | 6.85% | 31.7% | 128 | `98cf0d0fb42825ff9885c93f56647ed8` |

The rebalancing calendar does not change (120, 19 and 139 months), and all orders remain `MarketOnOpen`. The extra orders of the 0.98 arm are mostly small adjustments of the held line, 10 shares at most: on the coded window, 19 filled orders of that size, against 10 in the before variant.

On the coded window, the Sharpe gap (+0.067) exceeds the 0.05 threshold: the figures of the current code, at the top of this section, are rewritten. Out of sample, the verdict fixed in advance is **`NO DEGRADATION`**: Sharpe +0.136, CAGR +3.79 pt, worst drawdown −0.4 pt. This is not a strategy verdict, which stays archived: these figures measure the fixed code on windows already seen.

## Files

- `main.py` - Strategy (v3.2, confirmed best)
- `research.ipynb` - Multi-lookback optimization and expanded universe tests

## References

- Antonacci (2014), "Dual Momentum Investing"
- Faber (2007), "A Quantitative Approach to Tactical Asset Allocation"
- ARCHIVE.md - Full iteration history and ceiling analysis
