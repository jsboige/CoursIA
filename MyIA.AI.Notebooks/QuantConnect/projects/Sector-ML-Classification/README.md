# Sector ML Classification

**Statut** : 🔄 Phase de recherche — basé sur le livre HandsOnAITrading.

## Description

Stratégie de rotation sectorielle utilisant le Machine Learning (Random Forest) pour classer les secteurs US en catégories buy/hold/avoid.

### Vue d'ensemble de la stratégie

- **11 ETF sectoriels** : XLK, XLF, XLV, XLE, XLY, XLP, XLI, XLB, XLU, XLRE, XLC
- **Classification ML** : Random Forest à 3 classes (BUY, HOLD, AVOID)
- **Rééquilibrage mensuel** : les 3 premiers secteurs classés « BUY » (équi-pondéré)
- **Features** : indicateurs techniques issus de QC-Py-18 (Feature Engineering)

### Caractéristiques principales

- **Classifieur Random Forest** : `sklearn.ensemble.RandomForestClassifier`
  - Gère les relations non-linéaires
  - Analyse de l'importance des features
  - Robuste au surajustement

- **Feature Engineering** (issu de QC-Py-18) :
  - Indicateurs de momentum (RSI, MACD)
  - Indicateurs de tendance (SMA, EMA)
  - Mesures de volatilité (ATR, bandes de Bollinger)

- **Univers** : 11 ETF sectoriels GICS (SPDR sector spiders)

## ETF sectoriels

| Ticker | Secteur | Description |
|--------|---------|-------------|
| XLK | Technologie | Géants tech (AAPL, MSFT, NVDA) |
| XLF | Finances | Banques, assurance |
| XLV | Santé | Pharma, dispositifs médicaux |
| XLE | Énergie | Pétrole, gaz |
| XLY | Discrétionnaire | Retail, autos, luxe |
| XLP | Produits de base | Essentiels, alimentation, boissons |
| XLI | Industriels | Manufacturing, aéronautique |
| XLB | Matériaux | Chimie, mines |
| XLU | Services publics | Électricité, eau, gaz |
| XLRE | Immobilier | REIT, propriété |
| XLC | Communication | Télécom, média, internet |

## Fichiers

- `main.py` : algorithme QC avec classifieur Random Forest
- `research.ipynb` : notebook de recherche avec feature engineering et entraînement du modèle
- `config.json` : configuration du projet

## Références

- **Livre** : Hands-On AI Trading (chapitre ML Classification)
- **Notebook associé** : QC-Py-19-ML-Supervised-Classification.ipynb
- **Concept** : rotation sectorielle basée sur des prédictions ML

## Statut

Phase de recherche. Les métriques de performance et les résultats de backtest restent à déterminer.

---

**Note** : la rotation sectorielle ajoute de la diversification au-delà des stratégies mono-actif.
