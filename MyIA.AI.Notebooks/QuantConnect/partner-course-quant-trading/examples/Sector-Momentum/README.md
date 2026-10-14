# Sector Dual Momentum Strategy (ID: 20216980)

Stratégie de momentum sectoriel sur les constituants du SPY.

## Architecture
- `main.py` - Algorithme principal avec universe ETF SPY top 200
- `DualMomentumAlphaModel.py` - Alpha model momentum sectoriel
- `MyPcm.py` - Risk Parity Portfolio Construction avec leverage
- `CustomImmediateExecutionModel.py` - Exécution avec leverage ajustable
- `FredRate.py` - Custom data: taux Fed Funds (FRED)
- `deep_research_optimization.ipynb` - Deep Research : balayage des quatre leveurs du Sharpe (lookback, seuil VIX, levier, nombre de secteurs) sur 9 ETF sectoriels, avec diagnostic vrai signal vs artefact d'optimisation
- `research_robustness.ipynb` - Robustesse : démontage du Sharpe 2.53 obtenu sur 7 mois de bull market 2024 (extension 2015-2025, régimes de marché, momentum hebdomadaire, sensibilité au levier)

## Concepts enseignés
- Dual momentum (sector + individual)
- Universe selection dynamique
- Custom data (FRED)
- Risk Parity
