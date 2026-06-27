# Cloud-VolTargeting

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** N/A

## Description

Volatility targeting strategy with three variants. v1 targets 12% annualized volatility on SPY alone using realized vol scaling. v2 extends to a multi-asset portfolio (SPY, QQQ, IEF, GLD) with equal risk contribution targeting 10% annualized vol. v3 adds a 126-day momentum filter to the multi-asset approach. Monthly rebalance across all variants.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Cloud-VolTargeting/main.py
```

### QC Cloud
Create a new project, upload `main.py`, compile and run a backtest (default: 2015-01-01 to 2024-12-31).

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Vol targeting (3 variants) | Monthly | Vol target 10-12%, momentum filter 126 days (v3), equal risk contribution (v2/v3) |

## Files

| File | Description |
|------|-------------|
| `main.py` | Volatility targeting algorithm with 3 variants (single-asset, multi-asset ERC, +momentum) |

## References

- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
