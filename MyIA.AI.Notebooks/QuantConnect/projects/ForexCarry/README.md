# ForexCarry

**Asset class:** G10 Currencies (FX)
**Cloud project ID:** None (local only)

## Description

Cross-sectional G10 currency momentum strategy on 4 FX pairs (EURUSD, AUDUSD, USDJPY, USDCAD).
Uses risk-adjusted momentum (information ratio = 6m return / 21d realized vol) with skip-month (excludes last 21 days of mean-reversion noise).

Long-only top-2 momentum currencies vs USD, monthly rebalance. Signal is inverted for USD/XXX pairs (USDJPY, USDCAD).

**Structural limitation:** G10 FX momentum earns ~1-2% CAGR vs T-bill ~2.5% average in 2018-2026. Extended start to 2013 for better regime coverage.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (2013-2026)

| Metric | Value |
|--------|-------|
| Target Sharpe | -0.3 to -0.5 |
| Rebalance | Monthly |
| Universe | 4 G10 FX pairs |
| Leverage | Standard (100% allocated) |

## Files

- `main.py` - Strategy (v4.0, risk-adjusted momentum with skip-month)
- `research.ipynb` - FX momentum signal analysis (H1-H4)

## References

- Menkhoff et al. (2012), "Currency momentum strategies"
- Barroso & Santa-Clara (2015), risk-adjusted momentum
- Okunev & White (2003), skip-month momentum
