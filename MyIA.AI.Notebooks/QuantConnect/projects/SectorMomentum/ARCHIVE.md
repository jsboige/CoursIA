# ARCHIVE - Dual Momentum (SPY/TLT/GLD)

**Status**: ARCHIVED
**Date**: 2026-04-21
**Sharpe ceiling**: ~0.56

## Strategy Summary

Dual momentum on 3 assets (SPY risk-on, TLT bonds, GLD gold) using multi-lookback
composite momentum (1/3/6/12 months, weights 0.4/0.2/0.2/0.2) with daily SMA200
exit protection and monthly entry rebalance.

## Iteration History

| Version | Sharpe | CAGR  | MaxDD  | Change                              | Verdict    |
|---------|--------|-------|--------|-------------------------------------|------------|
| v2      | 0.554  | 13.1% | 23.0%  | Multi-lookback composite            | Baseline   |
| v3.2    | 0.555  | 13.0% | 22.8%  | SMA200 daily exit protection        | BEST       |
| v4.0    | 0.307  | -     | -      | Expanded risk-on (SPY+QQQ+IWM)      | REJECTED   |
| v4.1    | 0.263  | -     | -      | Proportional portfolio allocation   | REJECTED   |
| v4.2    | 0.376  | -     | -      | Classic GEM + tactical hedge        | REJECTED   |

## Why Expansion Doesn't Improve

1. **3-asset constraint**: With only SPY/TLT/GLD, the strategy has limited choices.
   Adding QQQ and IWM (v4.0) diluted the signal — correlated equity assets
   reduce the momentum discrimination power.

2. **Lookback saturation**: The composite 4-window lookback already captures
   short, medium, and long-term momentum. Adding more windows or changing weights
   doesn't move the needle beyond noise.

3. **SMA200 already optimal**: Daily exit protection (v3.2) was the last meaningful
   improvement. Finer-grained intra-month signals don't add value for monthly entries.

4. **Defensive rotation**: TLT vs GLD rotation is effective at what it does, but
   both are lower-return assets by design. The Sharpe is limited by the
   risk-off periods themselves.

## Research Key Findings

- **GLD > TLT risk-off**: GLD-only defensive gives Sharpe 0.434 vs TLT-only 0.075
  in research. The current strategy already uses relative momentum to choose.
- **4th asset tested**: TIPS and BIL add complexity without meaningful improvement.
- **VIX filter**: No significant gain — adds complexity, triggers whipsaws.
- **Composite + best risk-off**: Sharpe 0.409 (research period, lower than backtest)

## Recommendation

**Abandon pure dual momentum on 3-5 assets.** The Sharpe ceiling of ~0.56 is
inherent to the approach. Antonacci's GEM framework works but has structural limits
with this asset universe. To exceed 0.6:

- Move to broader asset universe (REITs, international, commodities)
- Add carry or value signals alongside momentum
- Use ML to predict momentum regime transitions
- Consider risk parity with momentum overlay instead of binary risk-on/off

## References

- Antonacci (2014): Dual Momentum Investing
- Faber (2007): A Quantitative Approach to Tactical Asset Allocation
