# DualMomentum Strategy

**Status**: ⚠️ REPLACED by DualMomentumNoTLT - Counter-Example for Educational Purposes

## Performance

| Metric | Value | Note |
|--------|-------|------|
| Sharpe Ratio | **0.350** | Weaker than replacement |
| CAGR | 9.2% | Similar to replacement |
| Max Drawdown | **33.6%** | Worse than replacement |
| Period | 2015-2026 | |

## Why This Strategy Was Replaced

### Root Cause: TLT (Long-Term Treasuries) Risk-Off Failure

This strategy uses **TLT** as the risk-off asset during bear markets:
- **Hypothesis**: TLT provides safe haven during equity declines
- **Reality (2022)**: TLT crashed -26% during rate hike cycle
- **Impact**: Max drawdown of 33.6% (mostly from COVID + 2022)

### The COVID Problem (March 2020)

| Event | SPY Drop | TLT Drop | Strategy Impact |
|-------|----------|----------|------------------|
| COVID crash (Mar 2020) | -34% | +2% | TLT worked as intended |
| Rate hike cycle (2022) | -25% | **-26%** | TLT FAILED as safe haven |

**The structural issue**: TLT is **duration risk**, not true diversification:
- In rate hike cycles, TLT correlates WITH equities (both down)
- 2022 broke the "bonds = safe haven" assumption
- Max DD of 33.6% is structural (cannot be fixed with parameter tuning)

### Replacement: DualMomentumNoTLT

| Strategy | Sharpe | CAGR | Max DD | Improvement |
|----------|--------|------|--------|-------------|
| DualMomentum (original) | 0.350 | 9.2% | 33.6% | Baseline |
| **DualMomentumNoTLT** | **0.469** | **11.0%** | **23.6%** | **+34% Sharpe, -10% Max DD** |

**What changed**:
- Removed TLT, replaced with **defensive assets** (XLP, IEF, GLD)
- Max DD reduced from 33.6% → 23.6%
- Sharpe improved from 0.350 → 0.469

### Lessons Learned

1. **TLT is not a safe haven in all regimes**: Duration risk creates correlation with equities during rate hikes
2. **Max DD is structural**: 33.6% drawdown is unacceptable for most investors
3. **Asset selection matters**: The choice of risk-off asset is as important as the signal
4. **Regime awareness**: Strategies must account for different market regimes (rate hikes vs. cuts)
5. **Don't overfit to one period**: TLT worked 2015-2020 but broke in 2022

## When DualMomentum (with TLT) CAN Work

This original approach may work in:
- **Falling rate environments**: TLT benefits from rate cuts
- **Deflationary periods**: Bonds provide true diversification
- **Shorter backtests**: 2015-2020 shows good results (but 2022 breaks it)

**For full-cycle (2015-2026)**: Use DualMomentumNoTLT instead.

## Pedagogical Value

This strategy serves as a counter-example for:
- ⚠️ **Asset selection risk**: The "safe haven" asset can become a source of risk
- ⚠️ **Regime dependence**: Strategies that work in one regime may fail in another
- ⚠️ **Max DD matters**: 33.6% drawdown is psychologically and financially damaging
- ⚠️ **The importance of full-period backtesting**: 2015-2020 looks good, 2022 breaks it

## Comparison to Replacement

```python
# Original (DualMomentum)
UNIVERSE = [SPY, QQQ, IEF, GLD, XLP, TLT]  # TLT included
RISK_OFF_ASSETS = [TLT, IEF, GLD, XLP]

# Replacement (DualMomentumNoTLT)
UNIVERSE = [SPY, QQQ, IEF, GLD, XLP]  # TLT removed
RISK_OFF_ASSETS = [IEF, GLD, XLP]  # Defensive, no duration risk
```

## References

- **DualMomentumNoTLT**: The improved version without TLT
- **SectorMomentum**: Similar dual-momentum approach with defensive assets
- **OPTIMIZATION_BACKLOG.md**: Full iteration history

---

**Note**: This strategy is kept as a counter-example. For production use, see **DualMomentumNoTLT** which removes TLT and achieves better risk-adjusted returns.
