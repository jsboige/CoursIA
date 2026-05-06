# ESGF Cours 5 Mai 2026 - Backtest Pack Results

**Period**: 2024-01-01 to 2026-05-01 | **Starting Capital**: $100,000 | **Date**: 2026-05-05

## Summary

| # | Strategy | Sharpe | CAGR | MaxDD | Win Rate | Net Profit | Alpha | Beta | Orders | Fees |
|---|----------|--------|------|-------|----------|------------|-------|------|--------|------|
| 1 | Trend-Following | **1.072** | 23.21% | **9.3%** | 83% | +62.7% | 0.068 | 0.395 | 120 | $159.75 |
| 2 | EMA-Cross-Alpha | 1.053 | **34.33%** | 23.3% | **96%** | +99.1% | 0.110 | 0.860 | - | $804.74 |
| 3 | SectorRotation-Momentum | 0.796 | 21.77% | 13.8% | 84% | +58.3% | 0.051 | 0.508 | 141 | $158.83 |
| 4 | Sector-ML-Classification | 0.209 | 10.47% | 17.3% | 62% | +26.1% | -0.038 | 0.628 | 266 | $512.20 |
| 5 | MeanReversion | 0.140 | 9.21% | 10.2% | 68% | +22.8% | -0.030 | 0.432 | 163 | $354.64 |

## Key Findings

**Best Risk-Adjusted**: Trend-Following (Sharpe 1.072, lowest MaxDD at 9.3%)
**Best Absolute Return**: EMA-Cross-Alpha (+99.1% net profit, 34.33% CAGR)
**Best Defensive**: Trend-Following (Beta 0.395, lowest market exposure)

### Strategy Details

#### 1. Trend-Following (Project 28797562)
- **Signal**: SMA200 + 6-month momentum hybrid
- **Universe**: SPY, EFA, EEM, TLT, GLD, DBC + BND safe haven
- **Rebalance**: Monthly, rank-based weighting
- **Bear filter**: SPY < SMA200 caps risky assets at 50%

#### 2. EMA-Cross-Alpha (Project 28885488)
- **Signal**: EMA(20) > EMA(50) crossover
- **Universe**: AAPL, MSFT, GOOGL, AMZN, NVDA
- **Rebalance**: Daily, equal weight portfolio
- **Note**: High Win Rate (96%) due to daily rebalance on trending tech stocks

#### 3. Cloud-SectorRotation-Momentum (Project 30821748)
- **Signal**: Price > SMA200 AND 6m momentum > 0
- **Universe**: QQQ, SPY, EFA, GLD, IWM + SHY defensive
- **Rebalance**: Monthly, momentum-weighted allocation

#### 4. Sector-ML-Classification (Project 29318875)
- **Signal**: RandomForest classifier (11 features, per-sector prediction)
- **Universe**: 8 sector ETFs (XLK, XLF, XLV, XLE, XLY, XLP, XLI, XLU)
- **Rebalance**: Monthly, SMA200 trend filter per sector
- **Note**: ML model underperforms simple momentum in this period

#### 5. MeanReversion (Project 30776121)
- **Signal**: RSI(14) oversold entries with relative strength filter
- **Universe**: 11 sector ETFs
- **Exit**: RSI > 65 or 15-day hold, 10% stop-loss
- **Note**: Lowest Sharpe (0.14), mean reversion struggled in trending 2024-2026 market
