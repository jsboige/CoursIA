# ESGF-VolEnsemble-Conservative

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** See `config.json` (local-id: 818573377)

## Description

Conservative ensemble volatility forecasting combining GARCH(1,1) and HAR-RV models on six assets (SPY, EFA, EEM, TLT, GLD, DBC). Uses the maximum of the two volatility forecasts (conservative approach). Targets 8% annualized volatility (half the normal 16% target). Applies SMA200 regime filter with 50% position reduction in bear markets, and SMA50 for trade direction. Weekly rebalance. Most conservative of the three ESGF volatility strategies.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm ESGF-VolEnsemble-Conservative/main.py
```

### QC Cloud
Open the cloud project (local-id: 818573377), compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Ensemble GARCH+HAR (conservative max) | Weekly | Vol target 8%, SMA200 regime (-50% bear), SMA50 direction, 500-day window |

## Files

| File | Description |
|------|-------------|
| `main.py` | Conservative ensemble volatility targeting (max of GARCH + HAR) with regime filter |
| `config.json` | Project configuration (local-id) |
| `research.ipynb` | Research notebook with ensemble model comparison and conservative parameter analysis |

## References

- Bollerslev, T. (1986). *Generalized Autoregressive Conditional Heteroskedasticity*. Journal of Econometrics.
- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
