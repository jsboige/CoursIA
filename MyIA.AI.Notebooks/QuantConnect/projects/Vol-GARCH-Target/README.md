# Vol-GARCH-Target

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** See `config.json` (local-id: 209093652)

## Description

GARCH(1,1) volatility targeting strategy on six assets (SPY, EFA, EEM, TLT, GLD, DBC). Each asset targets 10% annualized volatility with position sizes adjusted by the GARCH forecast. Uses SMA200 for trend direction (long in uptrend, reduce in downtrend). Model is refit every 22 trading days on a 500-day training window. Weekly rebalance on Mondays.

## How to Run

### Lean CLI
```bash
lean backtest --algorithm Vol-GARCH-Target/main.py
```

### QC Cloud
Open the cloud project (local-id: 209093652), compile and run a backtest.

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| GARCH(1,1) vol targeting | Weekly (Monday) | Vol target 10%, SMA200 trend, 500-day window, refit every 22 days |

### Aligned baseline (2018-2025)

Verified on QC Cloud (project 33245149, backtest `a0f7a5b59e878becd574612b85791d51`).

| Period | Sharpe | CAGR | MaxDD | PSR |
|--------|--------|------|-------|-----|
| 2018-2025 (aligned) | 0.325 | 6.97% | 10.80% | 14.9% |

The strategy's strength is risk control, not return. MaxDD 10.80% is the tightest of
the backbone baselines to date (cf GlobalMacro-Regime 22.8%, HAR-RV-J-Kelly 37.1%,
Cloud-VolTargeting single-asset 38.2%) -- the GARCH(1,1) variance forecast, the 30%
per-asset cap and the SMA200 trend filter combine into genuine risk budgeting that
holds drawdowns in check. Sharpe 0.325 is positive but modest, and PSR 14.9% is
non-significant. Notably it beats Cloud-VolTargeting (single-asset SPY, realized-vol,
150% clamp) on both Sharpe (0.325 vs 0.207) and MaxDD (10.8% vs 38.2%): GARCH
forecasting plus multi-asset diversification outperforms a naive realized-vol single
asset with a leverage clamp. Promoted Tier 4 (Untested) to Tier 2 (Historique). See
the comparative-backtests doc for the cross-strategy table.

## Files

| File | Description |
|------|-------------|
| `main.py` | GARCH(1,1) volatility targeting with SMA200 trend filter on 6 multi-asset ETFs |
| `config.json` | Project configuration (local-id) |
| `research.ipynb` | Research notebook with GARCH model analysis and parameter exploration |

## References

- Bollerslev, T. (1986). *Generalized Autoregressive Conditional Heteroskedasticity*. Journal of Econometrics.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
