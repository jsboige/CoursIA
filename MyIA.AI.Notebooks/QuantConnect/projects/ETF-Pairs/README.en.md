# ETF-Pairs Strategy

**Status**: ❌ BROKEN - Counter-Example for Educational Purposes

## Performance

| Metric | Value |
|--------|-------|
| Sharpe Ratio | **-0.706** |
| CAGR | -4.7% |
| Max Drawdown | 35.0% |
| Period | 2020-2026 |

## Why This Strategy Failed

### Root Cause: Same Fundamental Problem as PairsTrading

This strategy attempted pairs trading with **ETFs instead of individual stocks**, hypothesizing that:
- ETFs would be more stable than individual stocks
- Sector ETFs might show better cointegration
- Diversification within ETFs would reduce noise

**Result**: The same cointegration breakdown, but with WORSE performance:
- ETF pairs showed even LESS cointegration than stock pairs
- Higher volatility led to larger losses
- The hedge ratio was even more unstable

### What Makes This Worse Than PairsTrading

| Factor | PairsTrading | ETF-Pairs |
|--------|--------------|-----------|
| Sharpe | -0.361 | **-0.706** |
| CAGR | 0.9% | **-4.7%** (negative!) |
| Max DD | 15.1% | **35.0%** |

### Why ETFs Failed Here

1. **ETF composition changes**: ETFs rebalance their holdings, breaking any cointegration
2. **Sector correlation ≠ cointegration**: Sectors may move together but don't have mean-reverting spreads
3. **Lag effects**: ETF rebalancing creates artificial price disconnects
4. **Shorter history**: Most sector ETFs have less history for robust cointegration testing

### Lessons Learned

1. **ETF diversification ≠ cointegration stability**: Just because ETFs hold multiple stocks doesn't mean their price relationship is stable
2. **Don't double down on broken assumptions**: If stock pairs don't work, ETF pairs won't magically fix the fundamental issue
3. **Negative CAGR is a red flag**: Losing money consistently means the strategy has no edge whatsoever
4. **Stop after 2-3 iterations**: We tested multiple ETF pair combinations - all failed

## When Pairs Trading Might Work

See `PairsTrading/README.md` for context. For ETFs specifically:
- **Commodity ETFs** (GLD/GSLV, USO/UCO) where cointegration is structural
- **Leveraged ETF pairs** where the decay relationship is predictable
- **Fixed-income ETFs** where yield curve relationships create cointegration

**For equity sector ETFs (2020-2026)**: This approach failed catastrophically.

## Pedagogical Value

This strategy serves as a **double counter-example**:
- ❌ Same lesson as PairsTrading: correlation ≠ cointegration
- ❌ Additional lesson: ETF "stability" is a myth for cointegration
- ❌ When to pivot: If the core assumption fails, changing the instrument (stocks→ETFs) won't help

## References

- **PairsTrading**: See the stock-based version for comparison
- **QuantBook**: `quantbook.ipynb` - ETF cointegration analysis

---

**Note**: This strategy is NOT recommended for live trading. It demonstrates that instrument choice cannot fix a fundamentally flawed strategy assumption.
