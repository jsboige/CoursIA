# Cloud-DualMomentum-NoTLT

**Asset class:** Equities, Bonds, Commodities (multi-asset ETF rotation)

**Cloud project ID:** N/A

## Description

Dual Momentum strategy (Antonacci 2014) with three controlled variants via the `version` parameter. All variants use a 252-day lookback and monthly rebalance. No TLT allocation, avoiding long-duration Treasury exposure.

- **v1:** Classic absolute + relative momentum on SPY/EFA + BND bond allocation.
- **v2:** Broadened universe (SPY, QQQ, IEF, GLD, XLP) selecting top 2 by momentum score.
- **v3:** SPY/QQQ/EFA/GLD top 3 momentum-weighted allocation.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Cloud-DualMomentum-NoTLT/main.py
```

### QC Cloud
Create a new project, upload `main.py`, compile and run a backtest (default: 2015-01-01 to 2024-12-31).

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Dual Momentum (3 variants) | Monthly | Lookback 252 days, version 1/2/3 |

## Files

| File | Description |
|------|-------------|
| `main.py` | Dual Momentum algorithm with 3 strategy variants controlled by `version` parameter |

## References

- Antonacci, G. (2014). *Dual Momentum Investing*. McGraw-Hill.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
