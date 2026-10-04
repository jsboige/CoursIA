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
| --- | --- | --- | --- | --- | --- |
| buy-hold | TBD | | | | reference |
| 0.900 | 0.272 | 7.983% | 31.300% | 49.740% | TBD |
| 0.905 | 0.284 | 8.286% | 30.300% | 51.956% | TBD |
| 0.910 | 0.281 | 8.196% | 29.500% | 51.299% | TBD |
| 0.915 | 0.286 | 8.306% | 28.700% | 52.105% | TBD |
| 0.920 | 0.306 | 8.800% | 27.900% | 55.787% | TBD |
| 0.925 | 0.336 | 9.501% | 25.400% | 61.141% | TBD |
| 0.930 | 0.360 | 10.073% | 24.200% | 65.615% | TBD |
| 0.935 | 0.374 | 10.382% | 23.100% | 68.072% | TBD |
| 0.940 | 0.418 | 11.392% | 22.700% | 76.318% | TBD |
| 0.945 | 0.433 | 11.706% | 22.300% | 78.943% | TBD |
| 0.950 | 0.405 | 10.984% | 21.900% | 72.950% | TBD |
| 0.955 | 0.404 | 10.908% | 21.400% | 72.321% | TBD |
| 0.960 | 0.380 | 10.250% | 21.000% | 67.015% | TBD |

(Results table filled by the rejeu campaign of 2026-10-04/05; see BOOK_MAPPING.md row 08/01.)

## Files

- main.py - Book algorithm verbatim (commit e025f21), parameter-driven sweep
- buyhold.py - Buy-and-hold KO baseline (main.py of cloud project 37363104)

## References

- Hands-On AI Trading, Section 06, Example 08, Part 01 (Benchmark - Fixed Percentage Stop Loss)
