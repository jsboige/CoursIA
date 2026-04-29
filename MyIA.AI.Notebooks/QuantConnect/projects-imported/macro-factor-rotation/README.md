# Macro Factor Rotation (AI Stocks-Bonds Rotation)

## Source
- **QC Library**: AI Stocks-Bonds Rotation
- **Concept**: DecisionTreeRegressor using FRED macro factors to predict asset returns
- **QC Cloud Project**: 29687828 (cloned 2026-04-28)

## Concept
Uses 3 macro factors (VIX, yield curve spread, federal funds rate) from FRED to train a DecisionTreeRegressor per asset. Predicts 21-day forward returns, allocates to assets with positive predictions using a 1.5x leverage multiplier. Bitcoin exposure capped at 10%.

## Universe
| Ticker | Asset Class | Role |
|--------|-------------|------|
| SPY | US Equities | Core equity |
| GLD | Gold | Inflation hedge |
| BND | US Bonds | Fixed income |
| BTCUSD | Bitcoin | Crypto exposure (Bitfinex) |

## Macro Factors (FRED)
| Ticker | Description |
|--------|-------------|
| VIXCLS | CBOE Volatility Index (VIX) |
| T10Y3M | 10-Year minus 3-Month Treasury spread (yield curve) |
| DFF | Federal Funds Effective Rate |

## Parameters
- **Model**: DecisionTreeRegressor (max_depth=12)
- **Training lookback**: 4 years (configurable)
- **Prediction horizon**: 21 trading days
- **Leverage**: 1.5x total
- **Max BTC weight**: 10% (configurable)
- **Rebalance**: Monthly
- **Warmup**: 35 days

## Backtest Results (10-year)
See `research.ipynb` for detailed analysis.

## License
QuantConnect Community Strategy - open source
