# TurnOfMonth

**Asset class:** US Equities (SPY + QQQ)
**Cloud project ID:** None (local only)
**Status:** ARCHIVED (Sharpe ceiling ~0.13)

## Description

Turn-of-the-month calendar anomaly strategy: buys SPY+QQQ around month boundaries.
Window: last 4 + first 4 trading days of each month. 1.5x leverage (75% SPY, 75% QQQ).
SMA200 regime filter: stays flat in bear markets.

**Why the ceiling is structural:** The ToM effect has Sharpe ~0.36 on 2000-2025 because it outperforms in bear markets (forced institutional rebalancing). In 2015-2026 (~90% bull market), every day has similar returns, so the ToM premium is diluted. The strategy correctly demonstrates the anomaly but is period-constrained.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.128 |
| CAGR | 4.8% |
| Max Drawdown | 23.7% |
| Academic Sharpe (2000-2025) | ~0.36 |
| Leverage | 1.5x |

## Files

- `main.py` - Strategy (v2.1, confirmed best after 5 iterations)
- `research.ipynb` - Calendar anomaly analysis and 9 hypothesis tests (H1-H9)

## References

- Ariel (1987), "A Monthly Effect in Stock Returns"
- Lakonishok & Smidt (1988), "Are Seasonal Anomalies Real?"
- ARCHIVE.md - Full iteration history and structural ceiling analysis
