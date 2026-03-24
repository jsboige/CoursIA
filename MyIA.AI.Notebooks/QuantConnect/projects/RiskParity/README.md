# RiskParity Strategy

**Status**: ⚠️ PLAFOND STRUCTUREL CONFIRMÉ - Counter-Example for Educational Purposes

## Performance

| Metric | Value |
|--------|-------|
| Sharpe Ratio | **0.399** |
| CAGR | 7.8% |
| Max Drawdown | 20.9% |
| Period | 2015-2026 |

## Why This Strategy Hit a Ceiling

### Root Cause: Anti-Pattern in Bull Markets

Risk parity allocates capital inversely proportional to volatility:
- **Hypothesis**: Equal risk contribution = better risk-adjusted returns
- **Reality (2015-2026)**: Underperforms simpler approaches

### What Was Tested (and Failed)

| Iteration | Modification | Result | Why It Failed |
|-----------|--------------|--------|---------------|
| H5 | Replace TLT with IEF | Sharpe 0.330 | TLT superior in bull bond market (2015-2020) |
| H6 | Vol targeting 10% | Negative | Cash drag in low-vol (anti-pattern in bull) |
| H7 | VIX filter >25 (exit to cash) | Negative | Too little time in stress (<15%) = cash drag |

### Why Risk Parity Underperforms (2015-2026)

**The bull market problem**:
1. **Vol targeting reduces exposure**: When vol is low, strategy reduces exposure (misses gains)
2. **Bonds underperformed post-2020**: IEF/TLT correlation with equities during rate hikes
3. **Equal risk ≠ equal return**: Low-vol assets (bonds) drag down returns in bull markets
4. **Complexity without benefit**: Simple equal-weight outperforms

### Comparison to Alternatives

| Strategy | Sharpe | CAGR | Complexity |
|----------|--------|------|------------|
| RiskParity | 0.399 | 7.8% | High (vol weighting, rebalancing) |
| Equal Weight (60/40) | ~0.45 | ~9% | Low |
| AdaptiveAssetAllocation | 0.518 | 8.0% | High (momentum + min-var) |

### The "Vol Targeting" Anti-Pattern

Risk parity often uses vol targeting (e.g., target 10% vol):
- **In low-vol periods**: Reduce exposure to maintain target → miss gains
- **In high-vol periods**: Increase exposure → buy high, sell low
- **Net result**: Negative alpha in trending markets

**2015-2026 was mostly a bull market**: Vol targeting consistently reduced exposure during the best periods.

### Lessons Learned

1. **Risk parity ≠ free lunch**: Equal risk contribution doesn't guarantee better returns
2. **Vol targeting is regime-dependent**: Works in choppy markets, fails in trending markets
3. **Complexity isn't always better**: Equal-weight 60/40 outperforms with less effort
4. **Bonds aren't always diversifiers**: Post-2020 rate hikes broke the bond/equity correlation
5. **Know when to stop**: After 3 failed iterations (H5-H7), the ceiling is confirmed

## When Risk Parity CAN Work

This approach may work in:
- **Sideways/choppy markets**: Where vol targeting adds value
- **High volatility environments**: Where risk equalization protects capital
- **Multi-asset futures**: Where cointegration creates more stable relationships
- **Regime-aware versions**: That adjust approach based on market state

**For 2015-2026 US equities**: Plafond structurel confirmé.

## Pedagogical Value

This strategy demonstrates:
- ⚠️ The **vol targeting anti-pattern** in bull markets
- ⚠️ **Complexity ≠ performance**: Simple equal-weight can beat sophisticated risk parity
- ⚠️ **Regime dependence**: Strategies optimized for one regime may fail in another
- ⚠️ **When to declare a ceiling**: After 3+ failed iterations with clear hypotheses

## Comparison to Better Alternatives

```python
# RiskParity (volatility-weighted)
weights = 1 / volatility
weights /= weights.sum()

# Equal weight (simpler, better 2015-2026)
weights = np.array([1/n] * n)

# Adaptive (momentum + min-var)
# See AdaptiveAssetAllocation project
```

## References

- **AdaptiveAssetAllocation**: Combines momentum + min-var (Sharpe 0.518)
- **AllWeather**: Simpler multi-asset portfolio (Sharpe 0.667)
- **OPTIMIZATION_BACKLOG.md**: Full iteration history (H5-H7)

---

**Note**: This strategy is kept as a counter-example. For production use, consider simpler approaches (equal weight) or momentum-based alternatives (AdaptiveAssetAllocation).
