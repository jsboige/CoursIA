# ETF Basket Pairs Trading (ID: 19865767)

Strategie de pairs trading sur ETFs sectoriels avec test de co-integration Engle-Granger.

## Statut Actuel

**Performance (Meilleur Backtest)**: ❌ NEEDS_IMPROVEMENT
- **Sharpe Ratio**: -0.759 (Cible: > 0.5)
- **Net Profit**: -14.566% sur 4 ans (2020-2024)
- **Trades**: 304 (suffisant)
- **Max Drawdown**: 19.8% (acceptable)
- **Win Rate**: 50% (mais losses > wins)

**Diagnostic**: Stratégie fondamentalement négative malgré une architecture saine. Problèmes principaux:
1. Critères de sélection de paires trop restrictifs (`corr > 0.6`)
2. Lookback trop court (500h vs 1638h recommandé)
3. Beta EWMA instable
4. Stop-loss par leg individuel (casse la neutralité)

**Voir**: `ANALYSIS_REPORT.md` pour l'analyse complète et les propositions d'amélioration.

## Architecture (Alpha Framework complet)
- `main.py` - Orchestrateur principal
- `alpha.py` - FilteredPairsAlphaModel (z-score + cooldown)
- `portfolio.py` - CointegratedVectorPortfolioConstructionModel
- `risk.py` - TrailingStopRiskManagementModel (8%)
- `utils.py` - Warm-up et reset des indicateurs
- `universe.py` - SectorETFUniverseSelectionModel (IYM, top 10)
- `research.ipynb` - Analyse complete (correlation, rolling co-integration, mini-backtest)

## Concepts enseignes
- Co-integration Engle-Granger
- Z-score rolling pour signaux
- Architecture Alpha Framework QC (alpha, portfolio, risk, universe)
- Gestion des corporate actions (splits/dividendes)
- Diagnostic de stratégies défaillantes (Win Rate vs Sharpe)
