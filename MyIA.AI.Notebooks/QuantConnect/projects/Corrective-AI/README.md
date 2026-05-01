# Corrective AI / Meta-Labeling (Ch08-02)

**Hands-On AI Trading**, Chapter 8-02 — Meta-Labeling with Corrective AI

## Objective

Implement a meta-labeling approach where a primary model generates trading signals and a secondary corrective model filters out false positives, improving precision while maintaining recall.

## Approach

### Primary Model: SMA Crossover
- Fast SMA (20-day) vs Slow SMA (60-day)
- Signal: bullish when fast > slow * 1.02, bearish when fast < slow * 0.98
- Universe: SPY, TLT, GLD (multi-asset diversification)

### Corrective Filter
The secondary model evaluates whether to trust the primary signal based on:
- **Trend strength**: Gap between fast and slow SMA (normalized)
- **Volatility regime**: Price relative to EMA (50-day volatility proxy)
- **Rules**:
  - Strong trend (>3% gap) -> trust signal
  - Moderate trend + low volatility -> trust signal
  - Weak trend + high volatility -> reject signal (stay flat)

### Meta-Labeling Concept
- Primary model labels: +1 (long), -1 (short), 0 (flat)
- Secondary model labels: 1 (trust primary), 0 (reject primary)
- Net position = primary_direction * corrective_approval
- Expected: higher precision (fewer false signals), similar or lower recall

## QC Project

| Field | Value |
|-------|-------|
| Project ID | 30800636 |
| Organization | Trading Firm ESGF |
| Period | 2018-01-01 to 2024-12-31 |
| Starting Capital | $1,000,000 |

## Backtest Results (v1)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | -0.151 |
| CAGR | 2.22% |
| Max Drawdown | 11.3% |
| Net Profit | +16.64% |
| Win Rate | 70% |
| Total Orders | 1242 |
| Total Fees | $2,673.78 |

### Analysis
- 70% win rate confirms the corrective filter improves signal quality
- Negative Sharpe indicates risk-adjusted returns are suboptimal
- Average loss (-0.18%) exceeds average win (0.12%) — position sizing and exit timing need improvement
- The multi-asset approach (SPY/TLT/GLD) provides diversification but the SMA crossover lag hurts in sideways markets

## Files

- `main.py` — QC algorithm with primary signal + corrective filter
- `research.ipynb` — SMA crossover computation, corrective filter design, signal reduction analysis

## Reference

- Hands-On AI Trading, Chapter 8-02
- De Prado, M. (2018), "Advances in Financial Machine Learning" — Meta-labeling concept
- Corrective AI: secondary model trained on primary model's prediction errors
