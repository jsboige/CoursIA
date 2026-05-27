# ESGF-ML-XGBoost

**Asset class:** Equities (AAPL, MSFT, GOOGL, AMZN, NVDA)

**Cloud project ID:** 29686997

## Description

XGBoost classifier on 5 tech stocks (variant of ESGF-ML-RandomForest). Features (6): returns 1/5/20d, normalized RSI, SMA20/SMA50 ratio, 20d volatility. Label: 5d return > +1% -> Buy (2), < -1% -> Avoid (0), else Flat (1). Monthly retraining on 2-year rolling window.

## How to Run

### QC Cloud
Open cloud project 29686997, compile and run a backtest.

## Backtest Metrics

| Variant | Sharpe | CAGR | Max DD | Trades |
|---------|--------|------|--------|--------|
| XGBoost 5 stocks | **0.782** | 28.3% | 43.6% | 243 |

## Files

| File | Description |
|------|-------------|
| `main.py` | XGBoost classifier with monthly retraining on tech stocks |

## References

- Chen, T. & Guestrin, C. (2016). *XGBoost: A Scalable Tree Boosting System*. KDD.
- [QuantConnect ML Classification Documentation](https://www.quantconnect.com/docs/)
