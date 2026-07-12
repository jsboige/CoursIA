# TFT-Crypto-Ranking

**Type :** Recherche (notebook de recherche only, pas d'algorithme déployable)

**Classe d'actifs :** Crypto (BTC-USD, ETH-USD)

**Cloud project ID :** N/A (recherche only, pas d'algorithme déployable)

## Description

Notebook de recherche appliquant le Temporal Fusion Transformer (TFT, Lim et al. 2021) au ranking crypto cross-sectional (prédiction de direction BTC vs ETH). Utilise 26 features (11 spécifiques BTC + 11 spécifiques ETH + 4 cross-asset). L'architecture inclut un Variable Selection Network (VSN), un Gated Residual Network (GRN), un encodeur LSTM et une multi-head attention. Validation walk-forward 5-fold sur 4 seeds avec coûts de transaction 10bps. La baseline DLinear atteint Sharpe 0.742. Verdict : INCONCLUSIVE (z=1.33, insuffisant pour le seuil BEATS).

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
| TFT ranking cross-sectional | N/A (recherche) | 26 features, VSN+GRN+LSTM+attention, walk-forward 5-fold x 4 seeds, T-cost 10bps |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `research.ipynb` | Notebook de recherche avec modèle TFT pour ranking crypto, feature engineering et validation walk-forward |
| `_generate_research.py` | Script qui génère le notebook de recherche |

## Références

- Lim, B. et al. (2021). *Temporal Fusion Transformers for Interpretable Multi-horizon Time Series Forecasting*. International Journal of Forecasting.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
