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

Le dossier `examples/` contient 8 projets validés avec backtests positifs.

### Python - Crypto

| Projet | Cloud ID | Description |
|--------|----------|-------------|
| **Multi-Layer-EMA** | 20216947 | EMA crossover multi-crypto (BTC/ETH/LTC) + filtre RSI |

### Python - Actions/ETF

| Projet | Cloud ID | Description |
|--------|----------|-------------|
| **Sector-Momentum** | 20216980 | Momentum dual SPY/TLT/GLD + Risk Parity PCM |
| **Trend-Following** | 20216930 | Multi-oracles (MACD/RSI/Bollinger) + ATR trailing stop |

### Python - Options

| Projet | Cloud ID | Description |
|--------|----------|-------------|
| **Options-VGT** | 21113806 | Vente de PUTs OTM sur 5 valeurs tech (NVDA, ORCL, CSCO, AMD, QCOM) |
| **Option-Wheel-Strategy** | 20216898 | Wheel strategy SPY : PUT selling → assignment → covered CALL |

### Python - ML

| Projet | Cloud ID | Description |
|--------|----------|-------------|
| **ESGF-ML-RandomForest** | 29686996 | RandomForest sur AAPL/MSFT/GOOGL/AMZN/NVDA, 6 features, re-entrainement mensuel |
| **ESGF-Framework-Composite** | 29687005 | Alpha Framework : EMAMomentum + SectorMomentum alphas, MaxDD 15% |

### C#

| Projet | Cloud ID | Description |
|--------|----------|-------------|
| **CSharp-BTC-MACD-ADX** | 19898232 | BTC MACD+ADX journalier sur Binance Cash |
| **CSharp-BTC-EMA-Cross** | 19050970 | EMA crossover classique BTC (18/23) |
| **CSharp-CTG-Momentum** | 19225388 | "Stocks on the Move" (Clenow) - Momentum ranking |

---

## Notebooks de Recherche (QuantBook)

Cinq projets Researcher avec notebooks QuantBook opérationnels pour explorer les données QC Cloud :

| Projet | Cloud ID | QuantBook | Contenu de recherche |
|--------|----------|-----------|----------------------|
| **Multi-Layer-EMA-Researcher** | 28433748 | research.ipynb | Grid search EMA/RSI/stop-loss sur BTC/ETH/LTC |
| **BTC-ML-Researcher** | 28433750 | research.ipynb | Feature importance, walk-forward, confidence grid |
| **MomentumStrategy-Researcher** | 28657837 | quantbook.ipynb | H1-H4 : top-N, lookback, vol window, regime filter |
| **AllWeather-Researcher** | 28657833 | quantbook.ipynb | Grid search allocations All-Weather (SPY/IEF/GLD/XLP) |
| **Sector-Momentum-Researcher** | 28433643 | quantbook.ipynb + research.ipynb | Dual Momentum SPY/TLT/GLD, redesign complet |

Ces notebooks illustrent le workflow QuantBook → QCAlgorithm : idée → recherche → backtest.

---

## Recherche ML 2026 — Modèles validés (Pipeline V2)

Notre pipeline de recherche ML 2026 (`ML-Training-Pipeline/`) suit un curriculum 7 stages
ancré sur *Hands-On AI Trading* (Broad/QuantConnect, 2025). Les modèles ci-dessous ont
passé le gate **S1 (vol-forecasting)** avec test de Diebold-Mariano significatif
(p < 0.05, ≥ 4 seeds, walk-forward 5-fold) — ils sont **KEEPERS** intégrés aux stratégies
de production ESGF.

### S1 KEEPERS — Prévision de volatilité crypto multi-coins (BEATS)

| Modèle | Tâche | Verdict | p-value DM | Architecture |
|--------|-------|---------|-----------|--------------|
| **M12 HAR-RV-J** | Forecast vol 5-jours | BEATS RW + GARCH | **0.0015** | Heterogeneous Autoregressive + Jump component (Corsi 2009) |
| **M15 LSTM h=32** | Forecast vol courte échelle | BEATS RW | **0.0107** | LSTM hidden=32, 53/84 combos BEAT cross-coin (BTC/XRP/DOT/ADA) |

Complémentarité observée : M12 capte mieux ETH/SOL, M15 capte mieux DOT — d'où le
choix d'un ensemble pondéré (cf. ESGF-VolEnsemble-Conservative).

### S1 long-horizon — Vol multi-horizons (8 BEATS sur 16 combos)

XRP h=66 13.5σ, ETH h=132 5σ, BTC h=22 et h=66 BEATS. Confirme que le signal de
volatilité existe aussi sur horizons longs (1 à 6 mois), avec poids per-coin × per-horizon
dans S2 (vol ensemble pondéré).

### S3 — HMM Regime daily (livré, alimente S5 sizing)

Hidden Markov Model 2-régimes (calm vs stress) sur returns daily SPY+VIX+BTC.
Sortie discrète utilisée comme switch dans les stratégies vol-target (réduire
exposition en régime stress).

### S4 v2 — Inverse-Vol Ridge + HMM Regime (BEATS EqW)

Allocation pondérée inverse-vol avec régression Ridge sur features
(momentum + vol forecast M12) et switch HMM. Delta Sharpe **+0.325 vs EqW**
(Equal Weight baseline) sur backtest QC Cloud.

### Stratégies QC live alimentées par ces modèles

| Projet QC Cloud | Cloud ID | Modèle source | Description |
|----------------|----------|---------------|-------------|
| **ESGF-HAR-RV-Kelly** | 31456164 | M12 HAR-RV-J | Vol forecast → Kelly 1/4 sizing sur SPY/EFA/EEM/TLT/GLD/DBC |
| **ESGF-GARCH-VolTarget** | 31456084 | GARCH(1,1) baseline | Vol-targeting 15% annualisé (référence pour M12) |
| **ESGF-VolEnsemble-Conservative** | 31456204 | Ensemble M12+M15 | Pondération inverse-vol + cap de levier |

Ces 3 projets seront utilisés en **TP S5 (sizing & exécution)** du curriculum
ESGF 2026. Leur code et research notebooks sont disponibles dans
`../projects/ESGF-*`.

---

## Concepts Pédagogiques Couverts

Les exemples et templates couvrent **4 classes d'actifs** et **8+ concepts de trading** :

| Niveau | Concepts | Stratégies |
|--------|----------|------------|
| **1 - Fondations** | EMA Crossover, MACD+ADX, Options basiques | Multi-Layer-EMA, CSharp-BTC-EMA-Cross, Options-VGT |
| **2 - Intermédiaire** | Alpha Framework, Multi-indicateurs, Wheel Strategy | Sector-Momentum, Option-Wheel-Strategy, Trend-Following |
| **3 - Avancé** | Momentum ranking, Risk Parity, ML | CSharp-CTG-Momentum, Sector-Momentum, ESGF-ML-RandomForest |

---

## Résultats de Backtest

### Exemples ESGF (org ESGF) - 8 projets validés

| # | Projet | Sharpe | CAGR | Max DD |
|---|--------|--------|------|--------|
| 1 | **Sector-Momentum** | 2.530 | 66.1% | 5.6% |
| 2 | **Trend-Following** | 2.157 | 136.0% | 20.5% |
| 3 | **Multi-Layer-EMA** | 1.891 | 120.9% | 54.4% |
| 4 | **CSharp-BTC-MACD-ADX** | 1.224 | 38.1% | 48.8% |
| 5 | **CSharp-BTC-EMA-Cross** | 1.094 | 36.2% | 40.7% |
| 6 | **Options-VGT** | 0.892 | 25.3% | 15.6% |
| 7 | **Option-Wheel-Strategy** | 0.524 | 12.7% | 26.4% |
| 8 | **CSharp-CTG-Momentum** | 0.507 | 17.7% | 36.1% |

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
3. **Projets exemples** : Analyser `Sector-Momentum`, `Trend-Following`
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
- **[projects/README.md](../projects/README.md)** : Catalogue de stratégies

---

## Ressources

- [Documentation QuantConnect](https://www.quantconnect.com/docs)
- [Hands-On AI Trading Book](https://www.hands-on-ai-trading.com)
- [GitHub du livre](https://github.com/QuantConnect/HandsOnAITradingBook)
