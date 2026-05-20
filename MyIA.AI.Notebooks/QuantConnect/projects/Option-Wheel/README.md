# Option-Wheel

**Asset class:** US Equities (SPY Options)
**Cloud project ID:** None (local only)

## Description

Options wheel strategy on SPY: sells OTM put options (5% OTM, ~21 DTE) to collect premium.
If assigned, sells OTM covered calls on the resulting SPY position. Full wheel cycle.

VIX regime filter: skips put selling when VIX > 20 (high volatility). Aggressive selling when VIX < 15.
Cash-secured puts with 80% max exposure and margin disabled for safety. Minute-resolution backtest.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Starting Capital | $1,000,000 |
| Resolution | Minute |
| Put OTM | 5% |
| DTE | 21 days |
| VIX Filter | Skip selling if VIX > 20 |

## Files

- `main.py` - Strategy (wheel: short put -> covered call)
- `research.ipynb` - Options premium analysis and DTE/OTM optimization

## References

- Options wheel strategy: systematic premium collection via put/call selling
- Interactive Brokers brokerage model (cash account)
