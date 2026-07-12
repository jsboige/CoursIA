# Cloud-SectorRotation-Momentum

**Asset class:** Equities, Bonds, Commodities (ETF rotation)

**Cloud project ID:** N/A

## Description

Momentum-weighted trend following on a 5-ETF universe (QQQ, SPY, EFA, GLD, IWM) with SHY as the defensive cash equivalent. Uses a dual filter (price above SMA200 AND positive 6-month momentum) to select trending assets, then allocates proportionally to their rate-of-change (ROC) momentum scores. Rebalances every 21 trading days.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Cloud-SectorRotation-Momentum/main.py
```

### QC Cloud
Create a new project, upload `main.py`, compile and run a backtest (default: 2015-01-01 to 2024-12-31).

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Momentum-weighted trend following | 21 days | SMA200 + 6m momentum dual filter, ROC proportional weighting |

## Files

| File | Description |
|------|-------------|
| `main.py` | Sector rotation with momentum-weighted allocation and dual trend filter |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
