# ML-Chronos-Foundation (HandsOn Ex18)

**Classe d'actifs :** Actions US (top 10)
**Cloud project ID :** None (local only)

## Description

Modèle de fondation Chronos T5 d'Amazon pour le forecasting de séries temporelles. Rebalance bi-hebdomadaire basée sur la direction des prévisions.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Chronos-Foundation"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.277 |
| CAGR | 7.23% |
| Max Drawdown | 13.5% |
| Modèle | Chronos T5 (Amazon) |
| Rebalance | Biweekly |

## Fichiers

- main.py - Stratégie (v1.0, forecasting Chronos)
- research.ipynb - Évaluation du modèle de fondation

## Références

- Hands-On AI Trading, Section 06, Exemple 18
