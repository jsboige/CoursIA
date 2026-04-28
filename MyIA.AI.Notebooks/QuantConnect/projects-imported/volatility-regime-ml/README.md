# Volatility Regime ML (Volatility Harvest)

## Source
- **QC Library**: Volatility Harvest ML
- **Concept**: VIX regime detection with RandomForest ML overlay for tactical allocation
- **QC Cloud Project**: 29687293 (cloned 2026-04-28)

## Concept
Detect volatility regimes using VIX statistics and SPY momentum/volatility features. A RandomForest classifier predicts bullish probability (>0.6) as an overlay on 5 regime-based allocation states. Monthly model retraining with 2-year minimum training window.

## Universe
| Ticker | Asset Class | Role |
|--------|-------------|------|
| SPY | US Equities | Core equity holding |
| TLT | US Treasuries | Flight to safety |
| GLD | Gold | Crisis hedge |
| BIL | Treasury Bills | Cash equivalent |
| VIX | Volatility Index | Regime signal (CBOE custom data) |

## ML Features (11 inputs)
| Feature | Description |
|---------|-------------|
| current_vix | VIX close |
| vix_zscore | VIX z-score vs 20-day |
| vix_percentile | Historical percentile rank |
| vix / vix_sma20 | Short-term VIX ratio |
| vix / vix_sma50 | Medium-term VIX ratio |
| spy_5d_ret | SPY 5-day return |
| spy_10d_ret | SPY 10-day return |
| spy_20d_ret | SPY 20-day return |
| spy / spy_sma50 | SPY vs 50-day SMA |
| spy / spy_sma200 | SPY vs 200-day SMA |
| spy_vol * sqrt(252) | Annualized SPY volatility |

## Regime Logic
1. **VIX spike + oversold**: VIX > 80th percentile AND SPY -3% in 5 days -> Buy SPY (85-100%)
2. **VIX very low + extended**: VIX < 13 AND SPY > 5% above 50-SMA -> Reduce risk (40/30/20/10)
3. **VIX elevated but falling**: VIX > 20 AND VIX < 20-SMA -> Recovery (70-85% equity)
4. **VIX rising**: VIX > 1.2x SMA -> Defensive (30/40/20/10)
5. **Default trend following**: Above 200-SMA -> 60-70% equity, below -> defensive

## Parameters
- **Model**: RandomForestClassifier (100 estimators, max_depth=5)
- **Training**: Monthly, minimum 504 days (2 years)
- **Signal check**: Daily, 30 min after market open
- **Warmup**: 252 days
- **ML threshold**: Bullish probability > 0.6

## Backtest Results (11-year, 2008-2025)
See `research.ipynb` for detailed analysis.

## License
QuantConnect Community Strategy - open source
