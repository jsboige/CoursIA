# MeanReversion

**Asset class:** US Sector ETFs
**Cloud project ID:** None (local only)

## Description

Short-term mean reversion strategy on 11 GICS sector ETFs (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC).
Buys the most oversold ETFs (RSI(14) < 40) and holds for 15 days or until RSI > 60.

SMA200 regime filter on SPY: exits all positions in bear markets.
Stop-loss at -8% to cut real breakdowns. Max 4 concurrent positions at 25% each.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.294 |
| CAGR | 7.53% |
| Max Drawdown | 16.5% |
| Net Return | +80.9% |
| Rebalance | Daily scan |

## Files

- `main.py` - Strategy (v4.0, sector ETF mean reversion)
- `research.ipynb` - RSI optimization, stop-loss, and holding period tests

## References

- Jegadeesh (1990), "Evidence of Predictable Behavior of Security Returns"
- De Bondt & Thaler (1985), "Does the Stock Market Overreact?"
