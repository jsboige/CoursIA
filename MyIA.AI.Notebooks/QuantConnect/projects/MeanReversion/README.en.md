# MeanReversion

**Asset class:** US Sector ETFs
**Cloud project ID:** None (local only)

## Description

Short-term mean reversion strategy on 11 GICS sector ETFs (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC).
Every day at 10:00 (New York), it buys the most oversold ETFs (RSI(14) < 40) whose three-month return is no more than 10 points below SPY's. At most 4 positions at 25% each.
Exit: RSI > 65, 15-day holding period, or a -10% stop-loss.

SMA200 regime filter on SPY: in a bear market, new positions take 12.5% instead of 25%; open positions are not liquidated.
An ETF with fewer than 63 sessions of history (XLRE in late 2015, XLC in 2018) gets a zero three-month return.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/MeanReversion"`
```bash
lean backtest --project .
```

**QC Cloud:** no persistent cloud project. The backtests below ran in measurement projects; copy `main.py` to a new QC Cloud project to run it again.

**Parameters** (#23199):

| Parameter | Values | Default |
|-----------|--------|---------|
| `mode` | `strategy` (the strategy); `spy` (SPY 100% held); `6040` (SPY 60% / BND 40%); `ew11` (the universe's sector ETFs at equal weight, among those trading) | `strategy` |
| `start_date`, `end_date` | `YYYY-MM-DD` dates | `2015-01-01`, `2024-12-31` |

The three reference modes rebalance on the first trading day of the month, 30 minutes after the open, at the time of the strategy's scan. The `shadow` chart records the portfolio value at each SPY session open. It is the input of the significance computation (`Paradox46Benchmarks/significance.py`). The `reentries` runtime statistic counts the ETFs selected again on the day of their exit.

## Execution fix (#23199)

The daily scan first handled exits with `self.liquidate(symbol)`, then looked for entries. An ETF that had just exited could be selected again the same day if its RSI was still below 40, which often happens after a stop or a 15-day exit. It then received `self.set_holdings(symbol, w)`. At daily resolution, both orders fill at the close. `set_holdings`, computed against the position not yet sold, only sent the difference: the line ended with a few shares, or short, while the strategy counted it as a full position for 15 days.

Replaying the orders of the backtest published so far (`ad190cab96bc`, #20346) measured it: **37 same-day re-entries**. In 35 cases the sale is followed by a buyback, and in **29** of them that buyback is only 7 to 70 shares (XLF on 2015-01-29: 1606 shares sold, 21 bought back). In the other **2** cases, the target was below the position, `set_holdings` sold on top of the liquidation, and the line went short (XLE on 2018-10-30, XLF on 2020-03-02); these short positions stayed open over 7 fill dates. Re-run on 2026-10-29, the code before the fix reproduces this order log exactly, order by order (704 orders, same statistics).

An exit followed by a re-entry of the same ETF on the same day no longer sends a liquidation order: only `set_holdings(symbol, w)` is sent, and the line ends at `w`. The signal rules (RSI, relative strength, SMA200 filter, stop, holding period) do not change. Replaying the orders, the fixed code has **no same-day sale and buyback and no short position** on both windows. Every line still held after an order weighs 11.6% of the portfolio or more, for targets of 12.5% and 25%. The `reentries` statistic is 45 on w1 and 6 on w2.

## Backtest Metrics

QC Cloud backtests of 2026-10-29, starting capital 100,000, brokerage fees modelled by Lean. Each row is a run of the fixed code (`main.py` sha256 `8a3399323c43`) with the given `mode`. Results read after `completed: true`.

**w1: 2015-01-01 → 2024-12-31** (2516 tradeable dates)

| Arm | QC Sharpe | CAGR | Max drawdown | PSR | Net profit | Orders |
|-----|-----------|------|--------------|-----|------------|--------|
| **`strategy`** | **0.584** | **10.20%** | **19.5%** | 4.7% | 164.2% | 667 |
| `spy` (reference) | 0.533 | 12.97% | 33.7% | 3.0% | 238.9% | 1 |
| `6040` (reference) | 0.442 | 8.41% | 21.7% | 1.5% | 124.4% | 201 |
| `ew11` (diagnostic) | 0.438 | 10.66% | 36.1% | 1.4% | 175.5% | 615 |

**w2: 2025-01-01 → 2026-07-01** (374 tradeable dates, last session 2026-06-30)

| Arm | QC Sharpe | CAGR | Max drawdown | PSR | Net profit | Orders |
|-----|-----------|------|--------------|-----|------------|--------|
| **`strategy`** | **0.179** | **7.70%** | **8.0%** | 10.7% | 11.8% | 98 |
| `spy` (reference) | 0.665 | 18.96% | 18.7% | 27.5% | 29.7% | 2 |
| `6040` (reference) | 0.59 | 13.37% | 11.2% | 24.7% | 20.7% | 30 |
| `ew11` (diagnostic) | 0.632 | 15.84% | 14.9% | 26.7% | 24.6% | 107 |

The QC Sharpe subtracts a risk-free rate. The tests below use a zero-rate Sharpe, computed on the daily returns of the `shadow` chart.

**Significance** (Ledoit-Wolf, stationary bootstrap, Newey-West). The Holm correction covers the two verdict references on one side and the diagnostic on the other:

| Window | Comparison | Zero-rate Sharpe (strategy / arm) | Holm p, Sharpe difference (Ledoit-Wolf; bootstrap) |
|--------|------------|-----------------------------------|----------------------------------------------------|
| w1 | vs `spy` | 0.97 / 0.79 | 1.0; 1.0 |
| w1 | vs `6040` | 0.97 / 0.81 | 1.0; 1.0 |
| w1 | vs `ew11` | 0.97 / 0.69 | 0.41; 0.41 |
| w2 | vs `spy` | 0.82 / 1.05 | 1.0; 1.0 |
| w2 | vs `6040` | 0.82 / 1.21 | 1.0; 1.0 |
| w2 | vs `ew11` | 0.82 / 1.15 | 1.0; 1.0 |

## Verdict: NO BEATS out of sample (2025-2026), INCONCLUSIVE in sample (2015-2024)

The protocol (#23012, carried over in #23199) gives BEATS only if the Sharpe exceeds held SPY's **and** the difference stays significant after Holm against both references. It gives NO BEATS if the Sharpe is below held SPY's, and INCONCLUSIVE otherwise. The v5.x parameters were chosen on 2015-2024 (`main.py` docstring history): w1 is in sample, and its verdict is only indicative. w2, out of sample, decides.

- **w2 (2025 → mid-2026): NO BEATS.** Sharpe 0.179 vs 0.665 for held SPY, CAGR 7.7% vs 19.0%. The drawdown is lower (8.0% vs 18.7%), but the zero-rate Sharpe is also below all three arms (0.82 vs 1.05 for SPY).
- **w1 (2015-2024): INCONCLUSIVE.** Sharpe 0.584 vs 0.533 for held SPY, but the difference is not significant after Holm (p = 1.0 against both references). The strategy returns less than SPY (CAGR 10.2% vs 13.0%). Its Sharpe comes from lower volatility: most of the time it holds only two lines (median in the order replay), and its drawdown is 19.5% vs 33.7%.

**What the `ew11` diagnostic measures.** On w1, the eleven ETFs at equal weight have a zero-rate Sharpe of 0.69, vs 0.97 for the strategy. The difference is not significant after Holm (p = 0.41). On w2, the strategy is below the equal-weight universe (0.82 vs 1.15), with no significant difference either.

**What changes from the published figures.** Backtest `ad190cab96bc` (#20346) gave a Sharpe of 0.675, a CAGR of 10.42% and a drawdown of 11.1% on 2015-2024. Part of its entries never happened: 29 re-entries held only a residual of 7 to 70 shares, 2 others were short, and the book was less invested than the strategy intends. Fixed, it has a Sharpe of 0.584 and a drawdown of 19.5%. That backtest already did not reproduce the docstring's v5.2 figures (Sharpe 0.810). No re-tuning of the parameters: a retrospective adjustment would be overfitting (EPIC #9768).

Before #20346, the code crashed on 2018-09-11 with an index error (XLC, too young for the history guard), so it could not produce any metric over its coded window. The figures this README cited before (2015-2026, Sharpe 0.294) do not come from the v5.2 code.

## Files

- `main.py` - Strategy (v5.2, sector ETF mean reversion; same-day re-entry fixed by #23199, reference modes)
- `research.ipynb` - RSI optimization, stop-loss, and holding period tests

## References

- Jegadeesh (1990), "Evidence of Predictable Behavior of Security Returns"
- De Bondt & Thaler (1985), "Does the Stock Market Overreact?"
