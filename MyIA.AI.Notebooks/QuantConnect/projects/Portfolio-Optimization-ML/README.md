# Portfolio Optimization with Machine Learning

**Status**: 🔄 Research Phase - Based on HandsOnAITrading Book

## Description

Modern Portfolio Theory (Markowitz, 1952) enhanced with Machine Learning for better covariance estimation and return prediction.

### Strategy Overview

- **Universe**: 15 Large-Cap US stocks (5 sectors, 3 stocks each)
- **Covariance Estimation**: Ledoit-Wolf shrinkage (regularized)
- **Return Prediction**: Technical features (momentum + mean reversion)
- **Risk Parity Weighting**: Target volatility constraints
- **Monthly Rebalancing**: Optimize portfolio weights

### Key Innovations

1. **Ledoit-Wolf Covariance**:
   - Shrinkage estimator for robust covariance matrix
   - Addresses overfitting in high-dimensional settings
   - Better than sample covariance for small samples

2. **ML-Predicted Returns**:
   - Momentum features (3, 6, 12 month returns)
   - Mean reversion features (RSI, Bollinger Bands)
   - Volatility features (ATR, historical vol)

3. **Risk Parity with Constraints**:
   - Equal risk contribution across assets
   - Target volatility constraint (e.g., 15%)
   - Long-only portfolio (no short selling)

## Universe (15 Large-Caps)

| Sector | Stocks |
|--------|--------|
| Technology | AAPL, MSFT, NVDA |
| Financials | JPM, BAC, WFC |
| Healthcare | JNJ, UNH, PFE |
| Consumer | AMZN, TSLA, MCD |
| Industrials | CAT, HON, UNP |

## Optimization Problem

```
Minimize: w^T Σ w
Subject to:
  - w^T μ = target_return
  - sum(w) = 1
  - w_i ≥ 0 (long-only)
```

Where:
- Σ = Ledoit-Wolf covariance matrix
- μ = ML-predicted returns
- w = portfolio weights

## Files

- `main.py`: QC algorithm with portfolio optimization
- `research.ipynb`: Research notebook with covariance analysis and optimization
- `config.json`: Project configuration

## References

- **Paper**: "Honey, I Shrunk the Sample Covariance Matrix" (Ledoit-Wolf, 2004)
- **Theory**: Markowitz Portfolio Theory (1952)
- **Book**: Hands-On AI Trading (Portfolio Optimization chapter)
- **Related Notebook**: QC-Py-21-Portfolio-Optimization-ML.ipynb

## Status

Research phase. Performance metrics and backtesting results to be determined.

---

**Note**: Portfolio optimization assumes returns are normally distributed. Real markets may have fat tails.
