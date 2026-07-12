# Cloud-MeanReversion-Sectors

**Asset class:** Equities (GICS sector ETFs)

**Cloud project ID:** N/A

## Description

RSI(14) mean reversion strategy on 11 GICS sector ETFs (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC). Three variants with increasing sophistication: v1 uses raw RSI oversold/overbought signals; v2 adds SMA200 regime filtering (only trade in bull markets); v3 incorporates stop-loss rules. Scans daily 30 minutes after market open.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Cloud-MeanReversion-Sectors/main.py
```

### QC Cloud
Create a new project, upload `main.py`, compile and run a backtest (default: 2015-01-01 to 2024-12-31).

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| RSI Mean Reversion (3 variants) | Daily scan | RSI period 14, SMA200 regime filter (v2+), stop-loss (v3) |

## Files

| File | Description |
|------|-------------|
| `main.py` | Mean reversion algorithm with 3 variants (RSI, +regime filter, +stop-loss) on 11 sector ETFs |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
