# Vol-Ensemble-Conservative

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** See `config.json` (local-id: 818573377)

## Description

Conservative ensemble volatility forecasting combining GARCH(1,1) and HAR-RV models on six assets (SPY, EFA, EEM, TLT, GLD, DBC). Uses the maximum of the two volatility forecasts (conservative approach). Targets 8% annualized volatility (half the normal 16% target). Applies SMA200 regime filter with 50% position reduction in bear markets, and SMA50 for trade direction. Weekly rebalance. Most conservative of the three volatility strategies.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Vol-Ensemble-Conservative/main.py
```

### QC Cloud
Open the cloud project (local-id: 818573377), compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Ensemble GARCH+HAR (conservative max) | Weekly | Vol target 8%, SMA200 regime (-50% bear), SMA50 direction, 500-day window |

### Aligned baseline (2018-2025)

Standardized #1630 backbone run (QC Cloud project `33248352`, backtest `db77ae49`).

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.265 |
| CAGR | 6.142% |
| Max Drawdown | 10.40% |
| Probabilistic Sharpe Ratio | 13.6% |
| Tradeable dates | 1761 |

Interpretation: MaxDD 10.40% = tightest backbone baseline yet (beats Vol-GARCH-Target 10.80%, GlobalMacro-Regime 22.8%, HAR-RV-J-Kelly 37.1%). Positive Sharpe 0.265 but below single-GARCH Vol-GARCH-Target (0.325): the conservative overlay (max-of-ensemble HAR+GARCH forecast, half vol-target 8%, SMA200 regime -50% bear, SMA50 direction) tightened the drawdown at the cost of return, and the HAR component did not add risk-adjusted value over GARCH alone. Promoted Tier 4 -> 2 (Historique). totalOrders = 0 = wrapper extraction artifact (CAGR 6.14% implies real trades).

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
