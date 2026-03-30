# Framework Composite - MomentumSector + RegimeSwitching

## Description

Composite strategy combining two complementary approaches via QuantConnect Algorithm Framework:

1. **SectorMomentum (60% slice)**: Dual momentum among SPY/TLT/GLD
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

## Target Allocation

- Initial: **T60/RS40** (SectorMomentum 60%, RegimeSwitching 40%)
- Sweep range: T55/RS45 to T65/RS35 (5% steps)

## Expected Results

Based on component strategies:
- SectorMomentum standalone: Sharpe 0.62, CAGR 13.2%, MaxDD 22.8%
- RegimeSwitching standalone: Sharpe 0.55, CAGR 11.7%, MaxDD 33.0%

Hypothesis: Composite should achieve Sharpe > 0.65 with MaxDD < 25%.

## Backtest Period

2015-01-01 to 2026-03-10 (covers bull, bear, and sideways regimes)

## Deployment

1. Create project on QuantConnect Cloud (org: Jean-Sylvain Boige - Researcher)
2. Upload the 3 Python files
3. Compile and backtest
4. If Sharpe < 0.5, iterate allocation (T55/RS45, T65/RS35)
