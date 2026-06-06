# Trend Following Multi-Oracles (ID: 20216930)

Strategie trend following avec oracles multiples (MACD, RSI, Bollinger).

## Architecture (multi-fichiers)
- `main.py` - Algorithme principal, universe equity top 600
- `alpha.py` - Custom alpha avec 7+ indicateurs et scoring composite
- `trendCalculator.py` - Detection HH/HL/LL/LH (extrema locaux)
- `macd_oracle.py` - Oracle MACD (cross + seuils)
- `rsi_oracle.py` - Oracle RSI (convergence/divergence trend)
- `bollinger_oracle.py` - Oracle Bollinger (position relative)
- `research.ipynb` - Analyse SMA derivative et signaux

## Concepts enseignes
- Multi-oracle scoring
- Detection de tendance (Higher Highs, Lower Lows)
- ATR trailing stop-loss
- EMA 50/200 cross confirmation
- ADX strength filter
