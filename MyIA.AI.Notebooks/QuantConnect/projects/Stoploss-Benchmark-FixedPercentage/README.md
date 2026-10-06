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

| stop_loss_percent | Sharpe | CAGR | Max DD | Net Profit | vs buy-and-hold (Sharpe) |
| --- | --- | --- | --- | --- | --- |
| buy-hold | 0.264 | 7.679% | 36.100% | 47.533% | reference |
| 0.900 | 0.272 | 7.983% | 31.300% | 49.740% | +0.008 |
| 0.905 | 0.284 | 8.286% | 30.300% | 51.956% | +0.020 |
| 0.910 | 0.281 | 8.196% | 29.500% | 51.299% | +0.017 |
| 0.915 | 0.286 | 8.306% | 28.700% | 52.105% | +0.022 |
| 0.920 | 0.306 | 8.800% | 27.900% | 55.787% | +0.042 |
| 0.925 | 0.336 | 9.501% | 25.400% | 61.141% | +0.072 |
| 0.930 | 0.360 | 10.073% | 24.200% | 65.615% | +0.096 |
| 0.935 | 0.374 | 10.382% | 23.100% | 68.072% | +0.110 |
| 0.940 | 0.418 | 11.392% | 22.700% | 76.318% | +0.154 |
| 0.945 | 0.433 | 11.706% | 22.300% | 78.943% | +0.169 |
| 0.950 | 0.405 | 10.984% | 21.900% | 72.950% | +0.141 |
| 0.955 | 0.404 | 10.908% | 21.400% | 72.321% | +0.140 |
| 0.960 | 0.380 | 10.250% | 21.000% | 67.015% | +0.116 |
| 0.965 | 0.422 | 11.130% | 20.600% | 74.146% | +0.158 |
| 0.970 | 0.453 | 11.494% | 20.200% | 77.166% | +0.189 |
| 0.975 | 0.461 | 11.518% | 19.800% | 77.364% | +0.197 |
| 0.980 | 0.296 | 7.843% | 24.400% | 48.722% | +0.032 |
| 0.985 | -0.072 | 1.101% | 28.900% | 5.927% | -0.336 |
| 0.990 | -0.301 | -1.853% | 30.800% | -9.366% | -0.565 |
| 0.995 | -0.481 | -2.741% | 24.900% | -13.593% | -0.745 |

## Verdict vs the book

| Claim of the book | Measured on QC Cloud | Verdict |
| --- | --- | --- |
| 17 of 20 stop levels beat buy-and-hold KO | **17 of 20** (all but 0.985, 0.990, 0.995) | reproduced exactly |
| buy-and-hold KO Sharpe 0.263 | **0.264** | reproduced (rounding) |
| Sharpe collapses for stops tighter than 0.985 | 0.985 is already negative (-0.072); 0.990 and 0.995 fall further (-0.301, -0.481) | reproduced; the threshold is **0.985 inclusive**, not strictly below it |
| published parameter 0.95 | Sharpe 0.405, CAGR 10.984%, Max DD 21.9%, +0.141 over the baseline | reproduced |

The best level measured is **0.975** (Sharpe 0.461, Max DD 19.8%), above the published 0.95. The book presents 0.95 as a choice, not as an optimum, and the curve between 0.940 and 0.980 is flat enough (0.405 to 0.461) that the gap is not a contradiction.

## Method notes

- One backtest per stop level, executed serially on the shared QC Cloud node (the organization exposes a single free node, so the runs do not parallelize). The baseline is a separate project.
- One run (stop 0.990) first completed with an **empty result** — 0 orders, every statistic `-`. A rerun at the same level returned a fully populated row (656 orders) and it is the one carried above. The empty render is a QC-side artifact, not a property of the level; no row in this table comes from a first-render anomaly.
- `main.py` is the book algorithm at the byte (source commit e025f21), with `stop_loss_percent` driven by `get_parameter`. `buyhold.py` is the baseline project's `main.py`.

## Files

- main.py - Book algorithm verbatim (commit e025f21), parameter-driven sweep
- buyhold.py - Buy-and-hold KO baseline (main.py of cloud project 37363104)

## References

- Hands-On AI Trading, Section 06, Example 08, Part 01 (Benchmark - Fixed Percentage Stop Loss)
