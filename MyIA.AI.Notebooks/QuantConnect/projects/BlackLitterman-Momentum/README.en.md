# BlackLitterman-Momentum

**Asset class:** US Equities/ETF (multi-asset)
**Cloud project ID:** 29816300

## Description

Black-Litterman portfolio with multi-window momentum views (1M, 3M, 6M, 12M). BL optimization produces final weights.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/BlackLitterman-Momentum"`

**QC Cloud:** Deployed as project 29816300.

**Parameters** (#23186):

| Parameter | Values | Default |
|-----------|--------|---------|
| `mode` | `strategy` (the strategy); `spy` (SPY 100% held); `6040` (SPY 60% / BND 40%); `ew15` (the fifteen universe stocks, equal weight) | `strategy` |
| `start_date`, `end_date` | `YYYY-MM-DD` dates | `2015-01-01`, `2026-01-01` |

The four modes follow the same schedule: first trading day of the month, 30 minutes after the open. The `shadow` chart records the portfolio value at each SPY session open. It is the input of the significance computation (`Paradox46Benchmarks/significance.py`).

## Execution fix (#23186)

Until #23186, the rebalance called `liquidate()`, then one `set_holdings` per stock. At daily resolution, orders placed during the session fill at the close. The second call therefore computed its quantities against positions that were not sold yet, and only sent the difference. When a stock's target was below its position, that difference added to the liquidation sale and the line went short. The strategy is designed without short selling (weights bounded between 1 and 20%).

Replaying the orders of the backtest published on 2026-08-07 measured it: **119 rebalance dates out of 132** left at least one short position. Re-run on 2026-10-28, the same code leaves shorts at **126 dates out of 132**, with 8 invalid orders. The figures published until then described this book of residuals, not the strategy.

The rebalance now calls `self.transactions.cancel_open_orders()`, then a single `set_holdings([PortfolioTarget(...)], liquidate_existing_holdings=True)` on the final targets. The Black-Litterman computation is unchanged: covariance, views, posterior, optimization and volatility targeting are identical. Replaying the orders, the fixed code has **no short position and no invalid order** on both windows.

## Backtest Metrics

QC Cloud backtests of 2026-10-28, starting capital 100,000, brokerage fees modelled by Lean, monthly rebalance. Each row is a run of the fixed code with the given `mode`. Results read after `completed: true`.

**w1: 2015-01-01 → 2024-12-31** (2516 tradeable dates)

| Arm | QC Sharpe | CAGR | Max drawdown | PSR | Net profit |
|-----|-----------|------|--------------|-----|------------|
| **`strategy`** | **0.895** | **18.45%** | **21.5%** | 26.0% | 444.5% |
| `spy` (reference) | 0.542 | 13.18% | 33.7% | 3.3% | 245.1% |
| `6040` (reference) | 0.453 | 8.55% | 21.4% | 1.6% | 127.3% |
| `ew15` (diagnostic) | 0.944 | 23.90% | 35.0% | 30.0% | 754.0% |

**w2: 2025-01-01 → 2026-07-01** (374 tradeable dates, last session 2026-06-30)

| Arm | QC Sharpe | CAGR | Max drawdown | PSR | Net profit |
|-----|-----------|------|--------------|-----|------------|
| **`strategy`** | **-0.14** | **2.33%** | **19.2%** | 4.6% | 3.5% |
| `spy` (reference) | 0.619 | 17.89% | 18.6% | 25.6% | 28.0% |
| `6040` (reference) | 0.548 | 12.80% | 11.2% | 22.9% | 19.8% |
| `ew15` (diagnostic) | 0.676 | 18.71% | 19.1% | 28.4% | 29.3% |

The QC Sharpe subtracts a risk-free rate. The tests below use a zero-rate Sharpe, computed on the daily returns of the `shadow` chart.

**Significance** (Ledoit-Wolf, stationary bootstrap, Newey-West). The Holm correction covers the two verdict references on one side and the diagnostic on the other:

| Window | Comparison | Zero-rate Sharpe (strategy / arm) | Holm p, Sharpe difference (Ledoit-Wolf; bootstrap) |
|--------|------------|-----------------------------------|----------------------------------------------------|
| w1 | vs `spy` | 1.23 / 0.80 | 0.143; 0.135 |
| w1 | vs `6040` | 1.23 / 0.82 | 0.183; 0.183 |
| w1 | vs `ew15` | 1.23 / 1.21 | 1.0; 1.0 |
| w2 | vs `spy` | 0.19 / 1.01 | 0.671; 0.671 |
| w2 | vs `6040` | 0.19 / 1.16 | 0.671; 0.671 |
| w2 | vs `ew15` | 0.19 / 1.07 | 0.188; 0.188 |

On w1, the mean daily return difference against the 60/40 stays significant after Holm (p = 0.016). The tests on the Sharpe difference do not.

## Verdict: INCONCLUSIVE on 2015-2024, NO BEATS on 2025-2026

The protocol (#23012, carried over in #23186) gives BEATS only if the Sharpe exceeds held SPY's **and** the difference stays significant after Holm against both references. It gives NO BEATS if the Sharpe is below held SPY's, and INCONCLUSIVE otherwise.

- **w1 (2015-2024): INCONCLUSIVE.** Once the execution is fixed, the strategy does better than held SPY: Sharpe 0.895 vs 0.542, CAGR 18.5% vs 13.2%, drawdown 21.5% vs 33.7%. But the Sharpe difference is not significant after Holm (p = 0.14 against SPY, p = 0.18 against the 60/40).
- **w2 (2025 → mid-2026): NO BEATS.** Sharpe -0.14 vs 0.619 for held SPY, CAGR 2.3% vs 17.9%. The drawdown (19.2%) is not lower than SPY's (18.6%).

**What the `ew15` diagnostic measures.** The fifteen-stock universe was chosen in hindsight: it contains NVDA and TSLA. On w1, the fifteen stocks at equal weight have a zero-rate Sharpe of 1.21, the strategy 1.23, and the difference is not measurable (p = 1.0 after Holm). The edge over SPY is therefore found in the universe alone, without the Black-Litterman engine. The engine lowers the drawdown compared with `ew15` (21.5% vs 35.0%), through volatility targeting and the sector cap, but it returns less (CAGR 18.5% vs 23.9%), and the Sharpe does not move. On w2, the strategy is below the fifteen stocks at equal weight (Sharpe 0.19 vs 1.07), with no significant difference after Holm (p = 0.19).

**What changes from the verdict published on 2026-08-07.** That verdict concluded NO-BEATS with a defensive profile (16.1% drawdown), and compared the CAGR with an estimate of SPY. Both rested on the book of residual short positions. Re-run unchanged on 2026-10-28, the same code does not reproduce its figures either: Sharpe 0.457, CAGR 10.53%, drawdown 22.7%, PSR 1.18%. A book made of monthly differences is sensitive to small rewrites of adjusted prices between two runs. No re-tuning of the parameters (TAU, SIGMOID_STEEPNESS, TARGET_VOL): a retrospective adjustment would be overfitting (EPIC #9768).

## Files

- main.py - Strategy (BL momentum; execution fixed by #23186, reference modes)

## References

- Black & Litterman (1992), Global Portfolio Optimization
