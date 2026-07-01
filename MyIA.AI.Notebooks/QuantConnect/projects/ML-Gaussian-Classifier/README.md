# ML-Gaussian-Classifier (HandsOn Ex15)

**Classe d'actifs :** Actions US (top 10 tech)
**Cloud project ID :** None (local only)

## Description

Classifieur de direction GaussianNB sur les top-10 actions tech. Utilise les lagged returns, RSI et MACD comme features.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Gaussian-Classifier"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.361 |
| CAGR | 12.49% |
| Max Drawdown | 47.4% |
| Modèle | GaussianNB |
| Rebalance | Daily |

## Fichiers

- main.py - Stratégie (v1.0, classifieur Gaussian NB)
- research.ipynb - Sélection de features et évaluation du NB

## Références

- Hands-On AI Trading, Section 06, Exemple 15
