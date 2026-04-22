# ML-SVM

**Asset class:** US Equities (Equity ETFs)
**Cloud project ID:** 29434752

## Description

SVM Classification (sklearn `SVC`, linear kernel, C=0.5) strategy on 8 equity ETFs (SPY, QQQ, IWM, DIA, XLK, XLF, XLV, XLY).
Uses 8 features (RSI, BB position, MACD histogram, momentum, volatility, price/SMAs) to classify positive 10-day forward returns.

Monthly training, biweekly rebalance. Threshold 0.55 with max 4 positions.

**Structural ceiling:** SVM for ETF direction prediction has limited signal-to-noise ratio. Sharpe 0.147 reflects this ceiling, not a code issue.

## How to Run

**Lean CLI:**
```bash
lean backtest --project .
```

**QC Cloud:** Open project 29434752 in the QuantConnect IDE and click "Backtest".

## Backtest Metrics (2015-2026)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.147 |
| Rebalance | Biweekly |
| Kernel | Linear |
| Universe | 8 equity ETFs |

## Files

- `main.py` - Strategy (v3, SVC linear)
- `quantbook.ipynb` - Research notebook

## References

- Vapnik (1995), Support-Vector Networks
- Hands-On AI Trading, Section 06
