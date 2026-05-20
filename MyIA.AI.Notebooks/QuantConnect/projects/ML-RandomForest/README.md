# ML-RandomForest

**Asset class:** US Equities (Large-cap)
**Cloud project ID:** 29434751

## Description

Random Forest (sklearn `RandomForestClassifier`) strategy on 10 large-cap US stocks.
Uses 12 technical features (RSI, Bollinger Bands, MACD, momentum, volatility, volume, price ratios) to predict 10-day forward returns.

Monthly model training with biweekly rebalance (every other Monday). Prediction threshold of 0.54 with max 5 concurrent positions at 18% weight each.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Open project 29434751 in the QuantConnect IDE and click "Backtest".

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.68 |
| CAGR | 20.1% |
| Max Drawdown | 36.4% |
| Rebalance | Biweekly |

## Files

- `main.py` - Strategy (v3, RandomForestClassifier)
- `research.ipynb` - Feature engineering and hyperparameter research

## References

- Breiman (2001), "Random Forests"
- Hands-On AI Trading, Section 06 Example
