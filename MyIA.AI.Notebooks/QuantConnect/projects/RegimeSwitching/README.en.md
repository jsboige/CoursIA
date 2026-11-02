# RegimeSwitching

**Asset class:** US Equities/ETF
**Cloud project ID:** None (local only)

## Description

Switches between momentum and mean reversion according to a regime read on SPY (SMA50 and SMA200). The universe is SPY, QQQ, IEF and GLD.

- **Bull regime** (SPY above its SMA200 and SMA50 above SMA200): risk-adjusted momentum over 63 sessions. The best of SPY/QQQ takes 70 %, the other 30 %, and IEF and GLD are sold.
- **Bear or sideways regime**: mean reversion.
  - A risky ETF whose RSI(14) falls below 30 is bought (30 % split), with GLD and IEF at 35 % each.
  - Without an oversold ETF, a risky ETF whose RSI rises back above 50 is sold. GLD and IEF then go to 50 % each in a bear regime, or GLD 35 %, IEF 35 % and SPY 30 % in a sideways regime.

Rebalancing happens at the start of each month and on every regime change (daily check). A −10 % trailing stop applies to the risky ETFs, and a weight gap below 5 points is not traded.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/RegimeSwitching"`
**QC Cloud:** no persistent cloud project. The backtests below ran in measurement projects; copy `main.py` into a new QC Cloud project to run it again.

**Parameters** (#23221):

| Parameter | Values | Default |
|-----------|--------|---------|
| `mode` | `strategy` (the strategy); `spy` (SPY 100 % held); `6040` (SPY 60 % / BND 40 %); `ew4` (SPY, QQQ, IEF, GLD equal-weight) | `strategy` |
| `fix` | `on` (both fixes below); `room` (first fix only); `off` (original code) | `on` |
| `start_date`, `end_date` | `YYYY-MM-DD` dates | `2015-01-01`, `2024-12-31` |

The three reference modes rebalance on the first trading day of the month, 30 minutes after the open, at the time of the strategy's monthly rebalance. The `shadow` chart plots the portfolio value at each SPY session open; it is the input of the significance computation (`Paradox46Benchmarks/significance.py`). The runtime statistics `gross_max`, `gross_max_day`, `gross_over_1005` and `gross_months` measure the gross exposure (sum of absolute position values over portfolio value), read at each open.

## Execution fix (#23221)

The account is declared on margin (`AccountType.MARGIN`): Lean fills any order that exceeds the cash by borrowing. The strategy declares no leverage, yet two defects of the mean-reversion branch created some.

**1. The defensive basket was added on top of the kept risky positions.** The GLD and IEF weights assumed an empty risky pocket. But a risky ETF whose RSI is between 30 and 50 is not sold, and a non-oversold ETF is not resized when the other one is. SPY and QQQ could thus stay held together (risky pocket at 1.0), with GLD and IEF at 0.5 each on top. Over 2015-2024 the original code reaches a gross exposure of **1.981** (2016-01-20), with 224 sessions above 1.005 spread over 22 months.

The `room` fix limits the defensive basket to the room left by the risky pocket. The risky pocket is the oversold ETFs bought that day plus the kept risky ETFs at their current weight. The nominal defensive weights are multiplied by min(1, room / sum of nominal weights).

**2. SPY was sold and bought back on the same day.** In a sideways regime without an oversold ETF, SPY is sold in full when its RSI exceeds 50 (`liquidate`), then put back to 30 % by `set_holdings`. At daily resolution both orders fill at the same close, and `set_holdings` sizes its quantity against the position still held: it sells the difference a second time. On 2018-11-30 SPY ends at **−252 shares** in the original code, a short position. The first defect hid this one: with the `room` fix alone, the exposure peak stays at 1.090 (2018-12-03) and SPY ends at −234 shares on the same day. It is the mechanism measured on MeanReversion (#23199).

The `on` fix adds to the first one: a risky ETF that exits on RSI > 50 while the basket of the day targets it again (SPY in a sideways regime) is no longer liquidated, and `set_holdings` alone brings it back to its weight.

The signal rules (regime, RSI, momentum), the stop, the 5-point threshold and the cadence are unchanged.

**What the replay of filled orders measures:**

| Arm | Max gross exposure (day) | Sessions > 1.005 | Short positions | Same-day sell and buy of the same ETF |
|-----|--------------------------|------------------|-----------------|---------------------------------------|
| w1, `fix=off` (original code) | 1.981 (2016-01-20) | 224 (22 months) | 1 (SPY, 2018-11-30) | 0 (two sells on 2018-11-30) |
| w1, `fix=room` | 1.090 (2018-12-03) | 46 (6 months) | 1 (SPY, 2018-11-30) | 4 |
| **w1, `fix=on`** | **1.016 (2023-03-02)** | **43 (5 months)** | **0** | **0** |
| w2, `fix=off` | 1.318 (2025-04-07) | 49 (6 months) | 0 | 0 |
| w2, `fix=room` | 1.012 (2025-01-15) | 20 (2 months) | 0 | 0 |
| **w2, `fix=on`** | **1.012 (2025-01-15)** | **20 (2 months)** | **0** | **0** |

The `fix=on` residual, at most 1.6 % above 1, has not been attributed order by order. It involves no short position and no double order. It is consistent with the 5-point threshold, which can leave a line slightly above its target, and with orders sized earlier in the session filling at the close.

**Innocuity check.** On its coded window, the `main` code from before PR #23224 ran unmodified. The code of PR #23224 ran with `fix=off` on the same window, the same day. The two order logs are identical: 263 orders out of 263 (date, symbol, quantity, status), and no QC statistic differs.

## Backtest Metrics

QC Cloud backtests of 2026-10-29, starting capital 100,000, brokerage fees modelled by Lean. The retained strategy is the code of PR #23224 with `fix=on` (`main.py` sha256 `dd78d4640e34`); the references are the same code in `mode` `spy`, `6040` and `ew4`. Results read after `completed: true`.

Depuis #23253, le titre de section de `main.py` ne cite plus de « Beta-annealing » : ce mécanisme n'a jamais été implémenté. Seul ce commentaire change, et l'empreinte du fichier passe de `dd78d4640e34` à `cb2ad1684e8a`. Toutes les lignes hors commentaires sont identiques : les ordres et les mesures ci-dessous restent ceux de l'empreinte `dd78d4640e34`.

**w1: 2015-01-01 → 2024-12-31** (2516 tradable dates)

| Arm | QC Sharpe | CAGR | Max drawdown | PSR | Net profit | Orders |
|-----|-----------|------|--------------|-----|------------|--------|
| **`strategy`, `fix=on`** | **0.556** | **11.95 %** | **26.2 %** | 3.7 % | 209.4 % | 259 |
| `strategy`, `fix=off` (original code) | 0.596 | 12.97 % | 26.3 % | 5.1 % | 239.0 % | 263 |
| `spy` (reference) | 0.542 | 13.18 % | 33.7 % | 3.3 % | 245.1 % | 2 |
| `6040` (reference) | 0.454 | 8.55 % | 21.4 % | 1.6 % | 127.3 % | 202 |
| `ew4` (diagnostic) | 0.611 | 10.38 % | 21.6 % | 5.7 % | 168.7 % | 372 |

**w2: 2025-01-01 → 2026-07-01** (374 tradable dates, last session on 2026-06-30)

| Arm | QC Sharpe | CAGR | Max drawdown | PSR | Net profit | Orders |
|-----|-----------|------|--------------|-----|------------|--------|
| **`strategy`, `fix=on`** | **0.275** | **9.96 %** | **15.1 %** | 13.7 % | 15.3 % | 39 |
| `strategy`, `fix=off` (original code) | 0.285 | 10.23 % | 15.7 % | 14.0 % | 15.7 % | 41 |
| `spy` (reference) | 0.619 | 17.89 % | 18.6 % | 25.6 % | 28.0 % | 2 |
| `6040` (reference) | 0.548 | 12.80 % | 11.2 % | 22.9 % | 19.8 % | 25 |
| `ew4` (diagnostic) | 0.978 | 20.73 % | 9.7 % | 43.3 % | 32.6 % | 47 |

The QC Sharpe subtracts a risk-free rate. The tests below use a zero-rate Sharpe, computed on the daily returns of the `shadow` chart.

**Significance** (Ledoit-Wolf, stationary bootstrap, Newey-West). The Holm correction covers the two verdict references on one side and the diagnostic on the other:

| Window | Comparison | Zero-rate Sharpe (strategy / arm) | Holm p, Sharpe difference (Ledoit-Wolf; bootstrap) |
|--------|------------|------------------------------------|----------------------------------------------------|
| w1 | vs `spy` | 0.86 / 0.80 | 1.0; 1.0 |
| w1 | vs `6040` | 0.86 / 0.82 | 1.0; 1.0 |
| w1 | vs `ew4` | 0.86 / 1.01 | 1.0; 1.0 |
| w2 | vs `spy` | 0.69 / 1.01 | 1.0; 1.0 |
| w2 | vs `6040` | 0.69 / 1.16 | 1.0; 1.0 |
| w2 | vs `ew4` | 0.69 / 1.55 | 0.29; 0.31 |

## Verdict: NO BEATS out of sample (2025-2026), INCONCLUSIVE in sample (2015-2024)

The protocol (#23012, reused in #23221) gives BEATS only if the Sharpe difference is positive **and** stays significant after Holm against both references. It gives NO BEATS if the Sharpe is below that of held SPY, and INCONCLUSIVE otherwise. The coded window is 2015-2024: w1 is in the sample of any tuning, and its verdict is only indicative. w2, which comes later, decides; with 373 sessions its power is low.

- **w2 (2025 → mid-2026): NO BEATS.** Sharpe 0.275 against 0.619 for held SPY, CAGR 10.0 % against 17.9 %. The zero-rate Sharpe is also below that of all three arms (0.69 against 1.01 for SPY).
- **w1 (2015-2024): INCONCLUSIVE.** Sharpe 0.556 against 0.542 for held SPY, but the difference is not significant after Holm (p = 1.0 against both references). The strategy returns less than SPY (CAGR 11.9 % against 13.2 %); its drawdown is lower (26.2 % against 33.7 %).

**What the `ew4` diagnostic measures.** The four ETFs of the universe at equal weight, rebalanced monthly, have a higher zero-rate Sharpe than the strategy on both windows (1.01 against 0.86 on w1, 1.55 against 0.69 on w2), with no significant difference after Holm. The regime switch adds nothing measurable to simply holding its universe.

**What the fix costs.** The original code has a slightly higher QC Sharpe (0.596 against 0.556 on w1): it borrowed up to 98 % of the portfolio, and undeclared leverage inflates the return of a rising period. At a zero rate the gap is small (0.90 against 0.86 on w1, 0.695 against 0.695 on w2; daily correlation 0.99), and none of these figures measures the strategy as described.

**What changes compared with the published figures.** The registry cited 4593 days, a Sharpe of 0.540 and a net profit of 627.9 %. These figures cover a window of about 12.6 years that the code does not contain: it runs from 2015 to 2024. They have not been reproduced. The `main.py` docstring also announced a three-day progressive weight transition and a causal filter that were never implemented; these mentions are removed. The parameters are not re-tuned: a retrospective adjustment would be overfitting (EPIC #9768).

## Files

- `main.py` - Strategy (iter3, regime switching; exposure fixed by #23221, reference modes)
- `quantbook.ipynb` - Research QuantBook: analysis of the RegimeSwitching strategy
