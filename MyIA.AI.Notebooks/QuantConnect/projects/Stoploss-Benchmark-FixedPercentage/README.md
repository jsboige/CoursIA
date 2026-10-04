# Stoploss-Benchmark-FixedPercentage (HandsOn Ex08/01)

**Asset class:** US Equities (KO)
**Cloud project ID:** 37362370 (sweep) + 37363104 (buy-and-hold baseline)

## Description

Fixed-percentage stop-loss benchmark from Hands-On AI Trading, Section 06, Example 08, part 01. Allocates 100% of the portfolio to KO, places a stop market order `stop_loss_percent` below the price at 9:32 AM on the first trading day of each week, liquidates at the next week's open if the stop was not hit. Book claims: 17/20 of the swept stop distances outperform buy-and-hold KO (Sharpe 0.263); Sharpe collapses for stops tighter than 0.985; published parameter 0.95.

Sweep (per book footnotes): `stop_loss_percent` from 0.900 to 0.995, step 0.005 = 20 values. Period 2018-12-31 to 2024-04-01, $100k, RAW normalization.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Stoploss-Benchmark-FixedPercentage"`
**QC Cloud:** project 37362370, one backtest per `stop_loss_percent` parameter value; baseline project 37363104 (buyhold.py).

## Backtest Metrics

| stop_loss_percent | Sharpe | CAGR | Max DD | Net Profit | vs buy-and-hold |
|---|---|---|---|---|---|
| buy-hold | TBD | | | | reference |
| 0.900 | 0.272 | 7.983% | 31.300% | 49.740% | TBD |

(Results table filled by the rejeu campaign of 2026-10-04/05; see BOOK_MAPPING.md row 08/01.)

## Files

- main.py - Book algorithm verbatim (commit e025f21), parameter-driven sweep
- buyhold.py - Buy-and-hold KO baseline (main.py of cloud project 37363104)

## References

- Hands-On AI Trading, Section 06, Example 08, Part 01 (Benchmark - Fixed Percentage Stop Loss)
