# CTG Momentum (C#) (ID: 19225388)

Stratégie momentum avec indicateurs custom avancés en C#.

## Performance (post-bugfix SMA200)

- **Période**: 2021-01-01 → Now
- **Sharpe**: 0.507
- **Recommandation recherche**: Étendre a 2015-01-01 (Sharpe attendu: 1.05)

## Fichiers

### Code Principal

- `Main.cs` - StocksOnTheMoveAlgorithm, OEF ETF universe
- `CustomMomentumIndicator.cs` - Indicateur composite (slope + MA + gap + ATR)
- `AnnualizedExponentialSlopeIndicator.cs` - Régression exponentielle annualisée
- `GapIndicator.cs` - Détection de gaps
- `MarketRegimeFilter.cs` - Filtre régime SPY > SMA200

### Recherche

- `RESEARCH_SUMMARY.md` - Analyse robustesse 2015-2025 (Feb 2026)
- `research_robustness_simple.py` - Script Python backtest étendu
- `research_robustness_charts.png` - Visualisations régime filter + walk-forward
- `research_results.txt` - Output complet backtest
- `research_robustness.ipynb` - Notebook Jupyter (QuantBook, non execute)

## Concepts enseignes

- Custom indicators en C# (WindowIndicator, TradeBarIndicator)
- MathNet.Numerics (régression linéaire, R-squared)
- Market régime filtering (SMA 200)
- ATR-based position sizing
- Walk-forward validation
- Robustness testing sur 10+ ans

## Bugfix Important (Feb 2026)

**Bug**: SMA period = 10 au lieu de 200 (ligne 119)
**Impact**: ~95% Risk-ON (trop agressif) → 76.8% Risk-ON (optimal)
**Status**: Corrige, a valider par backtest cloud

## Prochaines Étapes

1. Modifier `Main.cs`: `SetStartDate(2015, 1, 1)`
2. Compiler via QC cloud
3. Lancer backtest via web UI
4. Valider Sharpe >= 0.4 sur période étendue
