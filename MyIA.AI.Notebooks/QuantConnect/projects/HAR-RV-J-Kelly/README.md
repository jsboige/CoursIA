# HAR-RV-J-Kelly

**Asset class:** Crypto (BTCUSDT, ETHUSDT, LTCUSDT, BCHUSDT on Binance)

**Cloud project ID:** 31650567

## Description

HAR-RV-J (Heterogeneous Autoregressive Realized Variance with Jumps, Corsi 2009 + Andersen, Bollerslev & Diebold 2007) for forecasting 5-day realized variance on crypto assets. Extends HAR Classic with jump component from Huang-Tauchen bipower variation. Kelly 1/4 fraction for position sizing.

Set parameter `use_jumps=1` for HAR-RV-J (6 features) or `use_jumps=0` for HAR Classic (3 features).

## How to Run

### QC Cloud
Open cloud project 31650567, compile and run a backtest.

## Backtest Metrics

| Variant | Sharpe | CAGR | Max DD | Trades |
|---------|--------|------|--------|--------|
| HAR-RV-J Kelly v2 (Binance, USDT) | **0.645** | 27.1% | 41.1% | 513 |
| HAR Classic Baseline (use_jumps=0) | 0.642 | 27.0% | 41.1% | 513 |

## Files

| File | Description |
|------|-------------|
| `main.py` | HAR-RV-J volatility forecasting with Kelly Criterion sizing on 4 crypto assets |

## References

- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- Andersen, T.G., Bollerslev, T., & Diebold, F.X. (2007). *Roughing It Up: Including Jump Components in the Measurement, Modeling, and Forecasting of Return Volatility*. Review of Economics and Statistics.
