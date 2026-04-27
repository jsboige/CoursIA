# ML-FX-SVM-Wavelet (HandsOn Ex05)

**Asset class:** Forex (4 pairs: EURUSD, AUDUSD, USDJPY, USDCAD)
**Cloud project ID:** None (local only)

## Description

SVR + Wavelet decomposition on G10 FX pairs. Uses pywt wavelet denoising on price series, then SVR to predict returns.

## How to Run

**Lean CLI:**

**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | SVR + Wavelet (pywt) |
| Universe | 4 G10 FX pairs |
| Rebalance | Monthly |

## Files

- main.py - Strategy (v1.0, SVR + wavelet)
- research.ipynb - Wavelet decomposition analysis
## References

- Hands-On AI Trading, Section 06, Example 05
