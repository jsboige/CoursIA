# Sector ML Classification

**Status**: 🔄 Research Phase - Based on HandsOnAITrading Book

## Description

Sector rotation strategy using Machine Learning (Random Forest) to classify US sectors into buy/hold/avoid categories.

### Strategy Overview

- **11 Sector ETFs**: XLK, XLF, XLV, XLE, XLY, XLP, XLI, XLB, XLU, XLRE, XLC
- **ML Classification**: Random Forest with 3 classes (BUY, HOLD, AVOID)
- **Monthly Rebalancing**: Top 3 sectors classified as "BUY" (equal-weight)
- **Features**: Technical indicators from QC-Py-18 (Feature Engineering)

### Key Features

- **Random Forest Classifier**: sklearn.ensemble.RandomForestClassifier
  - Handles non-linear relationships
  - Feature importance analysis
  - Robust to overfitting

- **Feature Engineering** (from QC-Py-18):
  - Momentum indicators (RSI, MACD)
  - Trend indicators (SMA, EMA)
  - Volatility measures (ATR, Bollinger Bands)

- **Universe**: 11 GICS Sector ETFs (SPDR sector spiders)

## Sector ETFs

| Ticker | Sector | Description |
|--------|--------|-------------|
| XLK | Technology | Tech giants (AAPL, MSFT, NVDA) |
| XLF | Financials | Banks, insurance |
| XLV | Healthcare | Pharma, medical devices |
| XLE | Energy | Oil, gas companies |
| XLY | Consumer Disc | Retail, autos, luxury |
| XLP | Consumer Staples | Essentials, food, beverages |
| XLI | Industrials | Manufacturing, aerospace |
| XLB | Materials | Chemicals, mining |
| XLU | Utilities | Power, water, gas |
| XLRE | Real Estate | REITs, property |
| XLC | Communication | Telecom, media, internet |

## Files

- `main.py`: QC algorithm with Random Forest classifier
- `research.ipynb`: Research notebook with feature engineering and model training
- `config.json`: Project configuration

## References

- **Book**: Hands-On AI Trading (ML Classification chapter)
- **Related Notebook**: QC-Py-19-ML-Supervised-Classification.ipynb
- **Concept**: Sector Rotation based on ML predictions

## Status

Research phase. Performance metrics and backtesting results to be determined.

---

**Note**: Sector rotation adds diversification beyond single-asset strategies.
