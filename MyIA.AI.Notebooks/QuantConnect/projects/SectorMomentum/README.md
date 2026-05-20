# SectorMomentum

**Asset class:** US Equities + Bonds + Gold (SPY, TLT, GLD)
**Cloud project ID:** None (local only)
**Status:** ARCHIVED (Sharpe ceiling ~0.56)

## Description

Dual momentum strategy with composite multi-lookback (1, 3, 6, 12 month, weights 0.4/0.2/0.2/0.2) on 3 assets: SPY (risk-on), TLT (bonds), GLD (gold).

When SPY has positive absolute momentum AND is above SMA200 AND outperforms TLT/GLD: go 100% SPY.
Otherwise: rotate to the better-performing defensive asset (TLT or GLD).
Daily SMA200 exit protection (intra-month stops if SPY breaks below SMA200).

**Archived because:** Sharpe ceiling ~0.56 for dual momentum on 3-5 assets. Target of 0.8 requires a fundamentally different approach. See ARCHIVE.md for full details.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.555 |
| CAGR | 13.0% |
| Max Drawdown | 22.8% |
| Rebalance | Monthly (entries), Daily (SMA200 exit) |

## Files

- `main.py` - Strategy (v3.2, confirmed best)
- `research.ipynb` - Multi-lookback optimization and expanded universe tests

## References

- Antonacci (2014), "Dual Momentum Investing"
- Faber (2007), "A Quantitative Approach to Tactical Asset Allocation"
- ARCHIVE.md - Full iteration history and ceiling analysis
