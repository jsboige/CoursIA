# Framework Composite - FamaFrench + AllWeather

## Description

Composite strategy combining two complementary approaches via QuantConnect Algorithm Framework:

1. **FamaFrench (20% slice)**: Factor ETF rotation (VLUE, MTUM, SIZE, QUAL, USMV)
   - Risk-adjusted momentum (return/volatility over 3/6/12 months)
   - Skip-month (exclude last month to avoid short-term reversal)
   - Top-2 factors by risk-adjusted momentum
   - Quarterly rebalancing

2. **AllWeather (80% slice)**: Static multi-asset allocation (SPY 30%, IEF 30%, GLD 30%, XLP 10%)
   - Ray Dalio-inspired "All Weather" portfolio (simplified, no TLT)
   - Drift rebalancing (3% threshold)
   - Monthly rebalancing

## Key Design Principle

**NO overlap between universes**: Factor ETFs (equity factors) vs traditional assets (equities/bonds/gold). This creates true diversification:
- FamaFrench: Equity factor exposure (value, momentum, size, quality, low-vol)
- AllWeather: Macro allocation (stocks, bonds, gold, defensive)

**Important**: FamaFrench uses risk-adjusted momentum ONLY (no SMA200 filter). AllWeather handles defense through its static allocation.

## Files

- `main.py`: Algorithm setup with CompositeAlpha and MultiStrategyPCM
- `alpha_models.py`: FamaFrenchAlpha and AllWeatherAlpha classes
- `portfolio_construction.py`: MultiStrategyPCM for capital allocation per strategy
- `quantbook.ipynb`: Research notebook with backtest analysis

## Performance

| Metric | Value |
|--------|-------|
| Sharpe Ratio | **0.588** |
| CAGR | 9.9% |
| Max Drawdown | 17.1% |
| Period | 2010-2026 |

## Allocation Sweep Results

| Allocation | Sharpe | CAGR | Max DD |
|------------|--------|------|--------|
| FF20/AW80 | **0.588** | 9.9% | 17.1% |
| FF40/AW60 | 0.564 | 10.5% | 19.3% |
| FF50/AW50 | 0.539 | 10.8% | 21.7% |
| FF60/AW40 | 0.512 | 11.2% | 24.1% |

**Winner**: FF20/AW80 (best risk-adjusted returns)

## Component Strategies

| Strategy | Sharpe | CAGR | Max DD |
|----------|--------|------|--------|
| FamaFrench v3.0 | 0.540 | 12.1% | 24.2% |
| AllWeather | 0.667 | 9.3% | 16.4% |
| **Composite (FF20/AW80)** | **0.588** | **9.9%** | **17.1%** |

The composite achieves better risk-adjusted returns than FamaFrench alone with lower drawdown.

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ff_allocation` | 0.20 | FamaFrench slice (0.20 = 20%) |
| `aw_allocation` | 0.80 | AllWeather slice (0.80 = 80%) |

## Backtest Period

2010-01-01 to 2026-03-10 (covers bull, bear, and sideways regimes)

## Deployment

- **Project ID**: 28882145
- **Organization**: Jean-Sylvain Boige (Researcher PAID)
- **Status**: ✅ Deployed and backtested

## References

- **FamaFrench**: Factor ETF rotation with risk-adjusted momentum
- **AllWeather**: Multi-asset static allocation (no TLT)
- **SESSION5_PATTERNS.md**: AlphaModel Framework pedagogical guide
