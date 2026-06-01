# GlobalMacro-Regime

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** N/A

## Description

Rank-based Risk Parity with Regime Switching (v3 BEST: Sharpe 0.607, CAGR 11.62%, MaxDD 23.6%). Uses SMA200 + 6-month momentum for regime classification. In bull markets, allocates to trending risky assets (SPY, EFA, EEM, TLT, GLD, DBC) with rank-weighted inverse-volatility positioning. In bear markets, shifts to risk parity on defensive assets (BND, TLT, GLD). Monthly rebalance.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm GlobalMacro-Regime/main.py
```

### QC Cloud
Create a new project, upload `main.py`, compile and run a backtest (default: 2015-01-01 to 2024-12-31).

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Regime-switching Risk Parity (v3) | Monthly | SMA200 + 6m momentum regime, rank-based inverse-vol weighting |

## Files

| File | Description |
|------|-------------|
| `main.py` | Global macro regime-switching strategy with rank-based risk parity allocation |

## References

- Hurst, B., Ooi, Y.H., Pedersen, L.H. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
