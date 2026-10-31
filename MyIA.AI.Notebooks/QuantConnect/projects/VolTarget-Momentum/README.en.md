# VolTarget-Momentum

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** 30784745

## Description

Rank-based allocation on six risky assets (SPY, EFA, EEM, TLT, GLD, DBC) with BND as a defensive safe harbor. v5 best variant achieved Sharpe 0.65, CAGR 14.72%. Uses SMA200 plus 6-month and 12-month momentum filters for asset selection. Targets 15% annualized volatility using 60-day realized volatility for position sizing, with leverage constrained to 0.3-1.5x. Monthly rebalance.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm VolTarget-Momentum/main.py
```

### QC Cloud
Open the cloud project (ID: 30784745), compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Rank-based vol targeting + momentum | Monthly | Vol target 15%, 60-day realized vol, leverage 0.3-1.5x, SMA200 + 6m/12m momentum |

## Refused buys, re-sent at the next session

At daily resolution every order goes out as `MarketOnClose`: submitted at 10:00 New York time, filled at the close. Lean checks the buying power of a buy before any sell of the same rebalance has filled, and charges it the margin of the buys already accepted that day. Since exposure goes up to 150% (volatility scalar capped at 1.5), some rebalance buys were refused (status `Invalid`) and never re-sent: the line stayed empty until the next rebalance. On 2015-09-01 and 2018-11-01 the refused BND buy (100% target, `BEAR` regime) left the portfolio fully in cash for a month.

`main.py` now re-sends a refused buy at the next session: `on_order_event` records the refusal, a daily event calls `set_holdings` towards the last rebalance target, and each re-send writes a `RETRY` log line. Before/after measurement on QC Cloud, under a protocol posted before the runs (#20523):

| Window | Refused buys | Re-sent and filled | Sharpe | Compounded annual return | Max drawdown |
|---|---|---|---|---|---|
| 2015-01-01 -> 2025-01-01 (coded) | 11 before, 13 after | 0 before, 13 after | 0.470 -> 0.441 | 10.55% -> 10.13% | 21.1% -> 20.8% |
| 2025-01-01 -> 2026-07-10 (out of sample) | 1 before, 1 after | 0 before, 1 after | 1.051 -> 1.072 | 28.19% -> 28.84% | 10.2% -> 10.1% |

The metric gap carries no sign worth keeping: it depends on what the market did in the months a line was missing, favourable on the coded window, unfavourable out of sample (the 50% GLD line left empty in February 2025). What the fix brings is a backtest that measures the strategy as described. On the rebalance day the refused buy is still refused: the gap now lasts one session instead of one month.

The figures in the description (v5: Sharpe 0.65, 14.72% annual return) come from an earlier measurement that the pre-fix run does not reproduce (Sharpe 0.470 on the coded window); that gap is not investigated here.

## Files

| File | Description |
|------|-------------|
| `main.py` | Volatility targeting with momentum filters and rank-based allocation on 6 risky + 1 defensive asset |
| `config.json` | Project configuration (cloud-id, organization-id, language) |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
