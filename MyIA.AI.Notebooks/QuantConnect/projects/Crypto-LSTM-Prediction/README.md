# Crypto LSTM Prediction

**Statut** : 🔄 Phase de recherche — basé sur le livre HandsOnAITrading.

## Description

Modèle de Deep Learning pour la prédiction de prix de cryptomonnaies utilisant des réseaux LSTM (Long Short-Term Memory) avec une architecture avancée.

### Caractéristiques principales

- **Architecture DLinear** (AAAI 2023) : décomposition ultra-simple + couches linéaires
  - Bloc SeriesDecomposition (séparation tendance/saisonnalité par moyenne mobile)
  - Pas de mécanisme d'attention (~10K paramètres)
  - Performance SOTA en prévision de séries temporelles

- **Implémentation PyTorch** : stack Deep Learning complète
  - Dataset et DataLoader personnalisés
  - Module SeriesDecomposition
  - Modèle DLinear (prévision tendance + saisonnière)

- **Cible** : prédiction du prix BTCUSDT

## Architecture

```
Input → SeriesDecomposition → [Trend, Seasonal] → DLinear → Prediction
         (Moving Avg)
```

### Composants du modèle DLinear

1. **SeriesDecomposition** : décompose la série temporelle en composantes tendance et saisonnières
2. **Couche linéaire de tendance** : projette les features de tendance
3. **Couche linéaire saisonnière** : projette les features saisonnières
4. **Reconstruction** : combine les prédictions tendance + saisonnière

## Fichiers

- `main.py` : algorithme QC avec intégration du modèle PyTorch
- `research.ipynb` : notebook de recherche avec entraînement et évaluation du modèle
- `config.json` : configuration du projet

## Référence

- **Paper** : « Are Transformers Effective for Time Series Forecasting? » (AAAI 2023)
- **Livre** : Hands-On AI Trading (chapitre Deep Learning)
- **Notebook associé** : QC-Py-22-Deep-Learning-LSTM.ipynb

## Statut

Projet de recherche/exploration. Les résultats de backtest et les métriques de performance restent à déterminer.

---

**Note** : les marchés crypto sont très volatils. Cette stratégie est à but éducatif.
