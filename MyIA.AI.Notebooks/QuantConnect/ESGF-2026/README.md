# ESGF 2026 - Trading Algorithmique avec QuantConnect

Workspace ESGF pour l'annee scolaire 2025-2026.
Sponsorise par Jared Broad (CEO QuantConnect) via le tier "Trading Firm".

**Organisation** : Trading Firm ESGF (`94aa4bcb...`)
**Professeur** : <email> (User ID: 46613)

---

## 🎓 Inscription Étudiants

### Processus d'inscription

Pour participer au cours ESGF 2026 et bénéficier du sponsoring QuantConnect (Trading Firm tier) :

1. **Créer un compte gratuit** sur [quantconnect.com](https://www.quantconnect.com) avec votre **email scolaire**
2. **Envoyer votre username** au professeur : `<email>`
3. **Attendre l'ajout** à l'organisation "Trading Firm ESGF" par le professeur
4. **Commencer les exercices** : notebooks QC-Py-01 à QC-Py-04, puis exercices ESGF

### Workflow Cloud-First

Tout le développement se fait sur **QuantConnect Cloud** (QC Lab), pas en local.

- **Avantages** : Pas d'installation locale, accès aux données historiques QC, compilation instantanée
- **Projets** : Créez vos projets directement dans QuantConnect Lab

---

## Templates Étudiants

Les templates dans `templates/` sont des points de départ pour vos projets. Chaque niveau correspond à une difficulté croissante.

### 🟢 Starter (Débutant)

**Fichier** : `templates/starter/main.py`

**Stratégie** : Croisement EMA sur BTCUSDT (Golden Cross / Death Cross)

**Prérequis** :
- Avoir suivi les notebooks QC-Py-01 à QC-Py-04
- Comprendre les bases : Initialize, OnData, indicateurs

**Concepts couverts** :
- `AddCrypto` : Ajouter un actif crypto avec marche et resolution
- `self.EMA(...)` : Créer un indicateur Moyenne Mobile Exponentielle
- `SetWarmUp` : Préchauffer les indicateurs avant de trader
- `SetHoldings` : Allouer un pourcentage du portefeuille
- `Liquidate` : Vendre toute la position
- `OnOrderEvent` : Recevoir les notifications d'execution

**Modifications suggérées** :
- Changer les périodes EMA : (5, 20), (20, 50) ou (50, 200)
- Ajouter un filtre RSI : ne pas acheter si RSI > 70
- Implémenter un stop-loss à -5%
- Tester sur d'autres cryptos : ETHUSDT, SOLUSDT

**Documentation complète** : [templates/starter/README.md](templates/starter/README.md)

---

### 🟡 Intermediate (Intermédiaire)

**Fichier** : `templates/intermediate/main.py`

**Stratégie** : Momentum ranking sur actions du S&P 500 avec Alpha Framework

**Prérequis** :
- Avoir suivi QC-Py-13 (Alpha Models)
- Comprendre l'Algorithm Framework QC

**Modules Alpha Framework** :
| Module | Role | Classe |
|--------|------|--------|
| **AlphaModel** | Générer des signaux (Insights) | `MomentumAlphaModel` |
| **PortfolioConstructionModel** | Convertir Insights en allocations | `EqualWeightingPortfolioConstructionModel` |
| **RiskManagementModel** | Ajuster selon le risque | `TrailingStopRiskManagementModel(0.05)` |
| **ExecutionModel** | Envoyer les ordres | `ImmediateExecutionModel` |

**Concepts couverts** :
- Universe Selection : filtrage dynamique via `universe.etf()`
- Alpha Framework : les 4 modules indépendants
- Insights : signaux avec direction, durée et confiance
- ScheduledEvent : déclenchement mensuel
- BrokerageModel : simulation Interactive Brokers

**Modifications suggérées** :
- Changer le lookback momentum : 60, 120 ou 252 jours
- Ajouter un filtre RSI pour éviter les surachats
- Filtrage sectoriel : concentrer sur certains secteurs
- Changer le modèle de construction : InsightWeighting, MeanVariance, RiskParity

**Documentation complète** : [templates/intermediate/README.md](templates/intermediate/README.md)

---

### 🔴 Advanced (Avancé)

**Fichier** : `templates/advanced/main.py`

**Stratégie** : Machine Learning (RandomForest) sur BTCUSDT

**Prérequis** :
- Avoir suivi QC-Py-18 (ML Features Engineering) et QC-Py-19 (ML Classification)
- Connaître sklearn : RandomForestClassifier, feature engineering

**Pipeline ML** :
```
Données (BTCUSDT Daily)
    → Feature Engineering (SMA, RSI, EMA ratios, returns)
    → Entraînement RandomForest (100 arbres, max_depth=5)
    → Prediction quotidienne (1 = long, 0 = cash)
    → Re-entraînement mensuel automatique
```

**Concepts couverts** :
- **Feature engineering** : Transformation d'indicateurs en features ML normalisées
- **sklearn dans QC** : RandomForestClassifier dans l'environnement QuantConnect
- **ObjectStore** : Persistance de modèles sérialisés (pickle)
- **Re-entraînement programme** : `Schedule.On` pour adaptation au régime de marché
- **Overfitting** : Risques d'un modèle trop complexe

**Modifications suggérées** :
- Ajouter des features : ADX, ATR, Bollinger Bands, volume
- Essayer d'autres modèles : XGBoost, SVC
- Ajouter des positions short (nécessite Margin account)
- Walk-forward optimization : entraîner sur N mois, tester sur mois suivant
- Gestion du risque : stop-loss, take-profit, position sizing

**Documentation complète** : [templates/advanced/README.md](templates/advanced/README.md)

---

## Exemples du Professeur

Le dossier `examples/` contient 11 projets de référence illustrant différents concepts de trading.

### Python - Stratégies Crypto

| Projet | Cloud ID | Description |
|--------|----------|-------------|
| **Crypto-MultiCanal** | 22298373 | Détecteur hiérarchique multi-canaux (ZigZag Macro/Meso/Micro) |
| **BTC-MachineLearning** | 21047688 | ML sur BTC (RandomForest/SVC/XGBoost) + ObjectStore |
| **Multi-Layer-EMA** | 20216947 | EMA crossover multi-crypto (BTC/ETH/LTC) + filtre RSI |

### Python - Stratégies Actions/ETF

| Projet | Cloud ID | Description |
|--------|----------|-------------|
| **ETF-Pairs-Trading** | 19865767 | Pairs trading avec co-intégration Engle-Granger + z-score |
| **Sector-Momentum** | 20216980 | Momentum dual SPY/TLT/GLD + Risk Parity PCM |
| **Trend-Following** | 20216930 | Multi-oracles (MACD/RSI/Bollinger) + ATR trailing stop |

### Python - Stratégies Options

| Projet | Cloud ID | Description |
|--------|----------|-------------|
| **Options-VGT** | 21113806 | Vente de PUTs OTM sur 5 valeurs tech (NVDA, ORCL, CSCO, AMD, QCOM) |
| **Option-Wheel-Strategy** | 20216898 | Wheel strategy SPY : PUT selling → assignment → covered CALL |

### C# - Stratégies

| Projet | Cloud ID | Description |
|--------|----------|-------------|
| **CSharp-BTC-MACD-ADX** | 19898232 | BTC MACD+ADX journalier sur Binance Cash |
| **CSharp-BTC-EMA-Cross** | 19050970 | EMA crossover classique BTC (18/23) |
| **CSharp-CTG-Momentum** | 19225388 | "Stocks on the Move" (Clenow) - Momentum ranking |

---

## Concepts Pédagogiques Couverts

Les exemples et templates couvrent **8 classes d'actifs** et **10+ concepts de trading** :

| Niveau | Concepts | Stratégies |
|--------|----------|------------|
| **1 - Fondations** | EMA Crossover, MACD+ADX, Options basiques, Anomalie calendaire | Multi-Layer-EMA, CSharp-BTC-EMA-Cross, Options-VGT, TurnOfMonth |
| **2 - Intermédiaire** | Alpha Framework, Multi-indicateurs, Wheel Strategy, ML basique | ETF-Pairs-Trading, Sector-Momentum, Option-Wheel, BTC-ML |
| **3 - Avancé** | Détecteur hiérarchique, Co-intégration, Volatilité, Forex, Futures | Crypto-MultiCanal, CSharp-CTG, ETF-Pairs, VIX-TermStructure, ForexCarry |

---

## Résultats de Backtest

### Exemples ESGF (org ESGF)

| # | Projet | Sharpe | CAGR | Max DD | Statut |
|---|--------|--------|------|--------|--------|
| 1 | **Option-Wheel-Strategy** | 0.524 | 12.7% | 26.4% | ✅ HEALTHY |
| 2 | **CSharp-BTC-EMA-Cross** | 1.094 | 36.2% | 40.7% | ✅ HEALTHY |
| 3 | **CSharp-BTC-MACD-ADX** | 1.224 | 38.1% | 48.8% | ✅ HEALTHY |
| 4 | **Multi-Layer-EMA** | 1.891 | 120.9% | 54.4% | ✅ HEALTHY |
| 5 | **Sector-Momentum** | 2.530 | 66.1% | 5.6% | ✅ HEALTHY |
| 6 | **Options-VGT** | 0.892 | 25.3% | 15.6% | ✅ HEALTHY |
| 7 | **Trend-Following** | 2.157 | 136.0% | 20.5% | ✅ HEALTHY |
| 8 | **CSharp-CTG-Momentum** | 0.507 | 17.7% | 36.1% | ✅ HEALTHY |
| 9 | **ETF-Pairs-Trading** | -0.759 | -3.7% | 19.8% | ❌ BROKEN |
| 10 | **Crypto-MultiCanal** | 0 | 0% | 0% | ❌ BROKEN |
| 11 | **BTC-MachineLearning** | — | — | — | ⏳ NO_DATA |

**Légende** :
- ✅ HEALTHY : Sharpe > 0.5 (stratégie robuste)
- ⚠️ NEEDS_IMPROVEMENT : Sharpe 0-0.5 (à améliorer)
- ❌ BROKEN : Sharpe < 0 ou 0 trades (problème majeur)

---

## Parcours Recommandé

### Pour les débutants

1. **Notebooks de fondations** : QC-Py-01 à QC-Py-04 (~4.5h)
2. **Template Starter** : Comprendre et modifier `templates/starter/main.py`
3. **Premier projet personnel** : Adapter le template avec vos idées
4. **Itération** : Backtester, analyser les résultats, améliorer

### Pour les intermédiaires

1. **Notebooks Alpha Framework** : QC-Py-13 à QC-Py-15 (~4h)
2. **Template Intermediate** : Étudier `templates/intermediate/main.py`
3. **Projets exemples** : Analyser `Sector-Momentum`, `ETF-Pairs-Trading`
3. **Projet personnel** : Créer votre propre stratégie avec Alpha Framework

### Pour les avancés

1. **Notebooks ML** : QC-Py-18 à QC-Py-21 (~4h)
2. **Template Advanced** : Étudier `templates/advanced/main.py`
3. **Projets ML** : Analyser `BTC-MachineLearning`, `Sector-ML-Classification`
4. **Recherche avancée** : Features engineering, hyperparameter tuning, walk-forward

---

## Notebooks d'Accompagnement

28 notebooks Python progressifs dans `../Python/` (QC-Py-01 à QC-Py-28) :

1. **Setup** : Compte, IDE, premier algorithme
2. **Fondations** : API, Resolution, Consolidators, QuantBook
3. **Indicateurs** : MACD, RSI, Bollinger, EMA
4. **Stratégies** : Mean Reversion, Momentum, Pairs Trading, Options
5. **Framework** : Alpha, Portfolio Construction, Risk, Execution
6. **ML/AI** : Features, modèles, ObjectStore, RL, NLP
7. **Production** : Paper trading, live, monitoring

---

## Documentation

- **[GETTING-STARTED.md](../GETTING-STARTED.md)** : Guide de démarrage détaillé
- **[ECE-QC-QUICKSTART.md](../ECE-QC-QUICKSTART.md)** : Guide pour étudiants ECE
- **[projects/README.md](../projects/README.md)** : Catalogue de 67 stratégies

---

## Ressources

- [Documentation QuantConnect](https://www.quantconnect.com/docs)
- [Hands-On AI Trading Book](https://www.hands-on-ai-trading.com)
- [GitHub du livre](https://github.com/QuantConnect/HandsOnAITradingBook)
