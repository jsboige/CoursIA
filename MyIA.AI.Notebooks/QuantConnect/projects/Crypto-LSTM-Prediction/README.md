# Crypto LSTM Prediction

**Statut** : 🔄 Phase de recherche — basé sur le livre HandsOnAITrading.

## Description

Sélection d'actifs crypto par **ranking cross-sectionnel** (Broad Ch8, *Hands-On AI Trading*) : prédire quel actif surperforme l'autre à J+1 (BTC vs ETH), et non un prix absolu. Deux modèles PyTorch sont comparés : DLinear et LSTM.

### Caractéristiques principales

- **Architecture DLinear** (AAAI 2023) : décomposition ultra-simple + couches linéaires, comparée à un LSTM de référence
  - Bloc SeriesDecomposition (séparation tendance/saisonnalité par moyenne mobile)
  - Pas de mécanisme d'attention — version shared-channel : 122 paramètres exactement (deux `nn.Linear(60, 1)`, calculable depuis la classe du notebook)
  - Performance SOTA en prévision de séries temporelles

- **Implémentation PyTorch** : stack Deep Learning complète
  - Dataset et DataLoader personnalisés
  - Module SeriesDecomposition
  - Modèle DLinear (prévision tendance + saisonnière)

- **Cible** : ranking cross-sectionnel BTC vs ETH (`y = 1` si BTC surperforme ETH à J+1, classification binaire)

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
- `_generate_research.py` : script qui régénère `research.ipynb` depuis `main.py`
- `config.json` : configuration du projet
- `README.en.md` : version anglaise du README

## Référence

- **Paper** : « Are Transformers Effective for Time Series Forecasting? » (AAAI 2023)
- **Livre** : Hands-On AI Trading (chapitre Deep Learning)
- **Notebook associé** : QC-Py-22-Deep-Learning-LSTM.ipynb

## Statut

Projet de recherche/exploration. Les résultats de backtest et les métriques de performance restent à déterminer.

---

**Note** : les marchés crypto sont très volatils. Cette stratégie est à but éducatif.
