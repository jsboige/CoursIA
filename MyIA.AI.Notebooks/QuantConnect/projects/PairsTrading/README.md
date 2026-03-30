# PairsTrading Strategy

**Status**: ❌ BROKEN - Counter-Example for Educational Purposes

## Performance

| Metric | Value |
|--------|-------|
| Sharpe Ratio | **-0.361** |
| CAGR | 0.9% |
| Max Drawdown | 15.1% |
| Period | 2010-2026 |

## Why This Strategy Failed

### Root Cause: Structural Cointegration Breakdown

The fundamental assumption of pairs trading is that the two securities are **cointegrated** - meaning their price spread is stationary and mean-reverting. This strategy assumes:

1. The hedge ratio is stable over time
2. The spread will revert to its mean
3. Statistical arbitrage opportunities exist

**In reality (2010-2026)**:
- US equity pairs showed **no stable cointegration relationship**
- The hedge ratio (estimated via OLS) was unstable
- Spread diverged permanently instead of reverting
- Result: Consistent losses with no edge

### What Was Tested

| Iteration | Modification | Result |
|-----------|--------------|--------|
| v1.0 | Basic OLS hedge ratio + z-score | Sharpe -0.361 |
| v2.0 | Multiple pairs (5 pairs) + cointegration test | Sharpe -0.420 |
| v3.0 | Different pair combinations | All negative |

### Lessons Learned

1. **Cointegration is rare in US equities**: Most stocks that appear correlated are NOT cointegrated
2. **Hedge ratio instability**: Even if pairs test positive for cointegration in-sample, the relationship often breaks down out-of-sample
3. **Transaction costs**: Spread trading requires frequent rebalancing, which erodes any theoretical edge
4. **Regime changes**: Market structure changes (2010-2026 includes bull, bear, COVID, inflation) break cointegration

## When Pairs Trading CAN Work

This strategy class may work in:
- **Different asset classes**: Commodities, futures, FX where cointegration is more common
- **Specific market regimes**: Certain volatility environments
- **Shorter time windows**: In-sample cointegration may exist for limited periods

**For US equities (2010-2026)**: This approach failed consistently.

## Pedagogical Value

This strategy is kept as a **counter-example** to demonstrate:
- ❌ The danger of assuming correlation = cointegration
- ❌ Why backtesting must cover the full period (2010-2026, not just 2015-2020)
- ❌ The importance of regime-awareness in strategy design
- ❌ When to abandon a strategy idea (after 2-3 failed iterations)

## References

- **QuantBook**: `quantbook.ipynb` - Research notebook with cointegration tests
- **Research**: `research.ipynb` - Exploratory analysis

---

**Note**: This strategy is NOT recommended for live trading. It serves as a warning about the importance of validating fundamental assumptions (cointegration) before deploying capital.
