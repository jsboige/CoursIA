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
| Sharpe Ratio | 0.495 |
| CAGR | 9.85% |
| Max Drawdown | 20.7% |
| Fenêtre backtest | 2018-2025 (run frais aligné #1630, voir `docs/qc/qc-strategies-status.md` l.234/l.762 ; run d'origine tr.7 2015-2024 : Sharpe 0.571) |
| Modèle | GradientBoostingClassifier |
| Rebalancement | Hebdomadaire |

Verdict de recherche (notebook) : walk-forward multi-seed **INCONCLUSIVE** (Sharpe moyen 0.301 ± 0.808, edge non significatif) ; PSR 4.6 % sur le run cloud — edge non validée à ce jour.

## Fichiers

- main.py - Stratégie (v1.0, GBM reversion/tendance)
- research.ipynb - Détection de régime et comparaison de modèles

## Références

- Hands-On AI Trading, Section 06, Exemple 03
