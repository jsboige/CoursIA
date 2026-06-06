# Trend Following Multi-Oracles

**Asset class:** US Equities (top 600)
**Cloud project ID:** 28797562

## Description

Strategie trend following avec oracles multiples (MACD, RSI, Bollinger).

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Trend-Following"`

**QC Cloud:** Deployed as project 28797562.

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
