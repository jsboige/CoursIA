# FamaFrench

**Asset class:** US Factor ETFs
**Cloud project ID:** None (local only)

## Description

Factor ETF rotation strategy using risk-adjusted momentum (12m-1m return / 63d realized volatility) with skip-month.
Universe of 5 Fama-French factor ETFs: VLUE (value), MTUM (momentum), SIZE (size), QUAL (quality), USMV (low-vol).

SMA200 regime filter on SPY: in bear markets, rotates to USMV as risk-off asset.
Dynamic top_n selection (all factors with positive score). Per-position stop-loss at -12%.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.540 |
| CAGR | 12.1% |
| Max Drawdown | 24.2% |
| Net Return | +258% |
| Rebalance | Monthly |

## Files

- `main.py` - Strategy (v3, risk-adjusted momentum with skip-month)
- `research.ipynb` - Factor analysis and signal robustness tests

## References

- Fama & French (1993), "Common risk factors in the returns on stocks and bonds"
- Barroso & Santa-Clara (2015), "Momentum has its moments"
