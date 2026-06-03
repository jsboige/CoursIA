# MomentumRegime-AdaptiveWeights

**Asset class:** US Equities (SPY/QQQ/IEF/GLD)
**Cloud project ID:** 31524424
**Baseline:** Framework_Composite_MomentumRegime (Sharpe 0.185, CAGR 4.73%)

## Description

Adaptive-weight variant of Framework_Composite_MomentumRegime.
Shifts allocation toward SectorMomentum (85/15 vs baseline 60/40),
expands momentum universe to include QQQ, and favors shorter-term lookbacks.

## Backtest Results

| Metric | Baseline (T60/RS40) | This Variant (T85/RS15) | Delta |
|--------|---------------------|--------------------------|-------|
| Sharpe Ratio | 0.185 | **-0.74** | -0.925 |
| CAGR | 4.73% | 1.76% | -2.97pp |
| Max Drawdown | - | 4.4% | - |
| Net Profit | - | 21.1% | - |
| Beta (vs SPY) | - | 0.081 | - |
| Total Orders | - | 403 | - |
| Win Rate | - | 71% | - |

**Verdict: NO BEATS.** Negative Sharpe ratio. The 85/15 shift destroyed value.

## Analysis

The variant dramatically underperforms the baseline. Root causes:

1. **Over-concentration on SectorMomentum**: At 85% weight, SectorMomentum
   dominates allocations. When its monthly signal flips (common with short-term
   lookbacks 0.5/0.2/0.2/0.1), the portfolio churns between assets.

2. **QQQ addition dilutes signal quality**: Adding QQQ to SectorMomentum's
   universe creates a 4-way race where the best-scored asset rotates frequently,
   generating unnecessary turnover.

3. **Low beta (0.081)**: The strategy spends most time in defensive assets (IEF/GLD)
   despite bull market conditions, suggesting SectorMomentum's composite scoring
   with short-term bias overweights transient pullbacks.

4. **RegimeSwitching at 15%**: Too small to matter. The regime-switching safety net
   that protects in bear/sideways markets is effectively disabled.

## Files

- main.py - Strategy (T85/RS15 allocation)
- alpha_models.py - SectorMomentum + RegimeSwitching alpha models
- portfolio_construction.py - MultiStrategyPCM portfolio construction

## References

- Hands-On AI Trading, Section 06
- Baseline: Framework_Composite_MomentumRegime
