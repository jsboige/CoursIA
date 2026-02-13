# ETF Basket Pairs Trading (ID: 19865767)

Strategie de pairs trading sur ETFs sectoriels avec test de co-integration Engle-Granger.

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
