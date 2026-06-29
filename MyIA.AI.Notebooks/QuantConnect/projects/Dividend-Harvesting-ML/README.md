# Dividend-Harvesting-ML (HandsOn Ex06)

**Classe d'actifs :** Actions US (QQQ 100)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Prédiction de dividendes par `DecisionTreeRegressor`. Prédit le rendement des dividendes à partir de ratios fondamentaux. Achète trimestriellement les 10 actions à dividendes élevés les mieux prédites.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Dividend-Harvesting-ML"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques du backtest

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.468 |
| CAGR | 12.66% |
| Max Drawdown | 30.6% |
| Modèle | DecisionTreeRegressor |
| Rebalancement | Trimestriel |

## Fichiers

- main.py - Stratégie (v1.0, prédiction de rendement de dividendes)
- research.ipynb - Analyse des caractéristiques de dividendes

## Références

- Hands-On AI Trading, Section 06, Exemple 06
