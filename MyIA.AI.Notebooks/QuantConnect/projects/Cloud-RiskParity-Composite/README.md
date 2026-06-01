# Cloud-RiskParity-Composite

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** N/A

## Description

Tactical rotation across six asset classes (SPY, TLT, GLD, EFA, EEM, DBC) using a dual filter: price above SMA200 AND positive 6-month momentum. Assets passing both filters receive equal weight. Rebalances every 30 days. Inspired by AQR's Hurst, Ooi, and Pedersen (2014) approach to trend-following with risk parity allocation.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Cloud-RiskParity-Composite/main.py
```

### QC Cloud
Create a new project, upload `main.py`, compile and run a backtest (default: 2015-01-01 to 2024-12-31).

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Dual-filter Risk Parity | 30 days | SMA200 + 6-month momentum, equal weight among passing assets |

## Files

| File | Description |
|------|-------------|
| `main.py` | Risk parity rotation with SMA200 + momentum dual filter on 6 multi-asset ETFs |

## References

- Hurst, B., Ooi, Y.H., Pedersen, L.H. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
