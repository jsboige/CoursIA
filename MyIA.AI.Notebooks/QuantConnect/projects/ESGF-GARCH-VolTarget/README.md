# ESGF-GARCH-VolTarget

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** See `config.json` (local-id: 209093652)

## Description

GARCH(1,1) volatility targeting strategy on six assets (SPY, EFA, EEM, TLT, GLD, DBC). Each asset targets 10% annualized volatility with position sizes adjusted by the GARCH forecast. Uses SMA200 for trend direction (long in uptrend, reduce in downtrend). Model is refit every 22 trading days on a 500-day training window. Weekly rebalance on Mondays.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm ESGF-GARCH-VolTarget/main.py
```

### QC Cloud
Open the cloud project (local-id: 209093652), compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| GARCH(1,1) vol targeting | Weekly (Monday) | Vol target 10%, SMA200 trend, 500-day window, refit every 22 days |

## Files

| File | Description |
|------|-------------|
| `main.py` | GARCH(1,1) volatility targeting with SMA200 trend filter on 6 multi-asset ETFs |
| `config.json` | Project configuration (local-id) |
| `research.ipynb` | Research notebook with GARCH model analysis and parameter exploration |

## References

- Bollerslev, T. (1986). *Generalized Autoregressive Conditional Heteroskedasticity*. Journal of Econometrics.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
