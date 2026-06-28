# Framework Composite - MomentumSector + RegimeSwitching

## Description

Composite strategy combining two complementary approaches via QuantConnect Algorithm Framework:

1. **SectorMomentum (60% slice)**: Dual momentum among SPY/IEF/GLD
   - Multi-lookback composite score (1/3/6/12 months)
   - SMA200 filter for SPY
   - Monthly rebalancing

2. **RegimeSwitching (40% slice)**: Regime-dependent strategy
   - Bull markets: Risk-adjusted momentum on SPY/QQQ (70/30)
   - Bear/Sideways: Mean-reversion (RSI oversold) + defensive (GLD/IEF)
   - Regime detection via SMA50/SMA200 on SPY

## Files

- `main.py`: Algorithm setup with CompositeAlpha and MultiStrategyPCM
- `alpha_models.py`: SectorMomentumAlpha and RegimeSwitchingAlpha classes
- `portfolio_construction.py`: MultiStrategyPCM for capital allocation per strategy

## Backtest Results (T60/RS40)

| Metric | Value |
|--------|-------|
| Sharpe Ratio | 0.185 |
| CAGR | 4.728% |
| Net Profit | 66.272% |
| Max Drawdown | 11.500% |
| Total Orders | 520 |
| Win Rate | 73% |
| Alpha | -0.008 |
| Beta | 0.218 |
| Sortino | 0.196 |

**Verdict**: Underperforming. Sharpe 0.185 is well below SectorMomentum standalone (0.555).
The RegimeSwitching component dilutes returns in the 60/40 blend. Very low beta (0.218)
indicates the composite is too conservative.

**Next steps**: Try T80/RS20 or T90/RS10 to reduce RegimeSwitching drag, or replace
RegimeSwitching with a more aggressive bull-only variant.

## Cloud IDs

- Project ID: 31243821
- Organization: d600793ee4caecb03441a09fc2d00f7f

## Backtest Period

2015-01-01 to 2025-12-31
