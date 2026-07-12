# ML-Reversion-Trending (HandsOn Ex03)

**Classe d'actifs :** Actions/ETF US (5 actifs)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Mean-reversion-en-régime-tendance par `GradientBoostingClassifier`. Utilise la largeur des bandes de Bollinger, le RSI et les rendements décalés pour prédire la direction du lendemain.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Reversion-Trending"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques du backtest

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.375 |
| CAGR | 8.44% |
| Max Drawdown | 24.4% |
| Modèle | GradientBoostingClassifier |
| Rebalancement | Hebdomadaire |

## Fichiers

- main.py - Stratégie (v1.0, GBM reversion/tendance)
- research.ipynb - Détection de régime et comparaison de modèles

## Références

- Hands-On AI Trading, Section 06, Exemple 03
