# ESGF-HAR-RV-Kelly

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** See `config.json` (local-id: 230839018)

## Description

HAR-RV (Heterogeneous Autoregressive Realized Variance, Corsi 2009) model for forecasting 5-day realized variance on six assets (SPY, EFA, EEM, TLT, GLD, DBC). Uses the Kelly Criterion at 1/4 fraction for position sizing based on the HAR forecast. Includes 5-day momentum direction. Model refit via OLS every 22 days on a 500-day rolling window. Weekly rebalance.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm ESGF-HAR-RV-Kelly/main.py
```

### QC Cloud
Open the cloud project (local-id: 230839018), compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| HAR-RV + Kelly Criterion | Weekly | Kelly fraction 1/4, 5-day forecast, OLS refit every 22 days, 500-day window |

## Files

| File | Description |
|------|-------------|
| `main.py` | HAR-RV volatility forecasting with Kelly Criterion sizing on 6 multi-asset ETFs |
| `config.json` | Project configuration (local-id) |
| `research.ipynb` | Research notebook with HAR-RV model analysis and Kelly fraction exploration |

## References

- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- Kelly, J.L. (1956). *A New Interpretation of Information Rate*. Bell System Technical Journal.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
