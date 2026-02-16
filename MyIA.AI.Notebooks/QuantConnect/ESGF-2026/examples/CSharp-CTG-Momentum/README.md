# CTG Momentum (C#) (ID: 19225388)

Strategie momentum avec indicateurs custom avances en C#.

## Fichiers
- `Main.cs` - StocksOnTheMoveAlgorithm, OEF ETF universe
- `CustomMomentumIndicator.cs` - Indicateur composite (slope + MA + gap + ATR)
- `AnnualizedExponentialSlopeIndicator.cs` - Regression exponentielle annualisee
- `GapIndicator.cs` - Detection de gaps
- `MarketRegimeFilter.cs` - Filtre regime SPY > SMA200
- `Research.ipynb` - Uncorrelated Assets analysis

## Concepts enseignes
- Custom indicators en C# (WindowIndicator, TradeBarIndicator)
- MathNet.Numerics (regression lineaire, R-squared)
- Market regime filtering
- ATR-based position sizing
