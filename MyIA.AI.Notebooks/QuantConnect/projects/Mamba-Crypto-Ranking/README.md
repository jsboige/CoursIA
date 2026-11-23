# Mamba-Crypto-Ranking

**Type :** Recherche (notebook de recherche only, pas d'algorithme déployable)

**Classe d'actifs :** Crypto (BTC-USD, ETH-USD)

**Cloud project ID :** N/A (recherche only, pas d'algorithme déployable)

## Description

Notebook de recherche évaluant Mamba (Selective State Space Model, Gu et Dao 2023) pour la prédiction de direction crypto (BTC-USD, ETH-USD). Compare Mamba (d_model=64, d_state=8, 1 couche, 80 epochs) aux baselines DLinear et TFT-Lite. Implémentation pure PyTorch avec validation walk-forward. Verdict (ré-exécution du 2026-11-21, #26319) : aucun modèle ne bat le Buy & Hold des mêmes fenêtres de test (Sharpe moyen 1,164). Mamba NO BEATS (Sharpe test 0,625, z −2,49), DLinear NO BEATS (0,375, z −2,03), TFT-Lite INCONCLUSIVE (0,864, z −1,24), ce dernier souvent figé sur une seule classe prédite.

## Comment exécuter

### Lean CLI
Non applicable (notebook de recherche only, pas de `main.py`).

### QC Cloud
Non applicable. Exécuter le notebook de recherche localement avec Python 3.10+ et PyTorch.

### Local
```bash
papermill research.ipynb output.ipynb
```

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Mamba SSM | N/A (recherche) | d_model=64, d_state=8, 1 couche, 80 epochs, walk-forward 5-fold x 4 seeds |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `research.ipynb` | Notebook de recherche avec implémentation du modèle Mamba, comparaison vs baselines DLinear/TFT-Lite |
| `_generate_research.py` | Script qui génère le notebook de recherche |

## Références

- Gu, A., Dao, T. (2023). *Mamba: Linear-Time Sequence Modeling with Selective State Spaces*. arXiv.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
