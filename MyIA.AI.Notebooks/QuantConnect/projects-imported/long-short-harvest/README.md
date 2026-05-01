# Long-Short Volatility Harvest ML

## Source
- **QC Library**: VolatilityHarvestML Long-Short
- **Concept**: Long-short equity with ML regime detection, Hurst exponent scoring, and trailing stops
- **QC Cloud Project**: 29687399 (cloned 2026-04-28)

## Concept
A long-short equity strategy combining multiple signals: (1) ML regime detection via RandomForestClassifier on VIX/SPY features, (2) Hurst exponent scoring for mean-reversion vs trend detection, (3) ATR-based stop losses for the short book, and (4) a 3-stage trailing stop system for the long book. The long book holds top 4 market cap stocks; the short book targets overextended stocks with high Hurst scores.

## Universe
| Component | Selection | Count |
|-----------|-----------|-------|
| Long book | Top 4 by market cap (monthly) | 4 |
| Short book | Hurst > threshold + extension + momentum | 1-150 |
| Coarse filter | Dollar volume > $20M, price > $5, fundamentals | 2000 |
| Fine filter | Market cap > $1B, IPO > 365 days | 150 |
| Benchmark | SPY | 1 |
| Hedge | GLD | 1 |

## ML Features (11 inputs)
| # | Feature | Source |
|---|---------|--------|
| 1 | Current VIX | CBOE |
| 2 | VIX z-score (20-day) | CBOE |
| 3 | VIX percentile rank | CBOE |
| 4 | VIX / VIX SMA(20) | CBOE |
| 5 | VIX / VIX SMA(50) | CBOE |
| 6 | SPY 5-day return | SPY |
| 7 | SPY 10-day return | SPY |
| 8 | SPY 20-day return | SPY |
| 9 | SPY / SPY SMA(50) | SPY |
| 10 | SPY / SPY SMA(200) | SPY |
| 11 | SPY realized vol (ann.) | SPY |

## Parameters
- **Model**: RandomForestClassifier (100 trees, max_depth=5)
- **Training**: Monthly, 504-day minimum, 21-day forward label (>2% = bullish)
- **Long gross**: 0.9 (configurable)
- **Short gross**: 0.6 (configurable)
- **ML tilt**: 0.25 (overweight top cap when ML bullish)
- **Top weight cap**: 35% per stock
- **Hurst windows**: [10, 10, 40, 60, 90, 100]
- **Score threshold**: 0.85 (short entry)
- **Short stop**: 2.0x ATR(20)
- **Long trailing stops**: 9.5% / 7.0% / 4.85% (3 stages)
- **Warmup**: 252 days

## Backtest Results (12-year)
See `research.ipynb` for detailed analysis.

## License
QuantConnect Community Strategy - open source
