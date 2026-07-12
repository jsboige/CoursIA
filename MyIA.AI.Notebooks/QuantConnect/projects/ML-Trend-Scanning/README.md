# ML-Trend-Scanning (HandsOn Ex01)

**Classe d'actifs :** Actions/ETF US (SPY, TLT, GLD)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Scanning de tendance par `RandomForestClassifier`. Prédit la direction du lendemain à partir de caractéristiques de rendements décalés (lagged returns), de volatilité et de volume, sur un univers de 3 actifs. Ré-équilibrage mensuel.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Trend-Scanning"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques du backtest

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.292 |
| Modèle | RandomForestClassifier |
| Univers | SPY, TLT, GLD |
| Rebalancement | Mensuel |

## Fichiers

- main.py - Stratégie (v1.0, scanning de tendance RandomForest)
- research.ipynb - Feature engineering et évaluation du modèle

## Références

- Hands-On AI Trading, Section 06, Exemple 01
