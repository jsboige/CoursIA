# Asset Class Momentum (Dual Momentum)

## Source
- **QC Library**: https://www.quantconnect.com/learning/articles/investment-strategy-library/asset-class-trend-following
- **Quantpedia**: Strategy #2 - Asset Class Momentum
- **QC Cloud Project**: 29687233 (cloned 2026-04-05)

## Concept
Select 3 ETFs with the strongest 12-month momentum from a diversified basket of 5 asset classes, weight equally, rebalance monthly.

## Universe
| Ticker | Asset Class |
|--------|-------------|
| SPY | US Equities |
| EFA | International Equities |
| BND | US Bonds |
| VNQ | Real Estate (REITs) |
| GSG | Commodities |

## Parameters
- **Lookback**: 252 trading days (12 months)
- **Selection**: Top 3 by momentum
- **Weighting**: Equal weight (1/3 each)
- **Rebalance**: Monthly

## Backtest Results (11-year, 2014-2025)
See `research.ipynb` for detailed analysis.

## License
QuantConnect Community Strategy - open source
