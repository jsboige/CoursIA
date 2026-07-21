<!-- CATALOG-STATUS
series: QuantConnect-partner-course-quant-trading
pedagogical_count: 7
note: count filesystem autoritatif (git ls-files) ; sous-série NON référencée dans le breakdown hub QuantConnect/README.md (Python/projects/ML-Training-Pipeline/kelly_lean = 4 entrées seulement, partner-course=7 et research=17 absents de l'agrégat)
-->

# Trading Quantitatif avec QuantConnect — Template de Cours Partenaire

Espace de travail pour les cours de trading quantitatif des écoles partenaires.
Sponsorisé par Jared Broad (CEO QuantConnect) via le tier « Trading Firm ».

---

## Inscription des Étudiants

### Procédure d'Inscription

Pour participer et bénéficier du sponsoring QuantConnect (tier Trading Firm) :

1. **Créer un compte gratuit** sur [quantconnect.com](https://www.quantconnect.com) avec votre **email d'école**
2. **Envoyer votre nom d'utilisateur** à l'instructeur
3. **Attendre d'être ajouté** à l'organisation Trading Firm
4. **Commencer les exercices** : notebooks QC-Py-01 à QC-Py-04, puis les exercices du cours

### Workflow Cloud-First

Tout le développement se fait sur **QuantConnect Cloud** (QC Lab), pas en local.

- **Avantages** : pas d'installation locale, accès aux données historiques QC, compilation instantanée
- **Projets** : créez vos projets directement dans QuantConnect Lab

---

## Templates Étudiants

Les templates dans `templates/` sont des points de départ pour vos projets. Chaque niveau correspond à une difficulté croissante.

### Starter (Débutant)

**Fichier** : `templates/starter/main.py`

**Stratégie** : crossover EMA sur BTCUSDT (Golden Cross / Death Cross)

**Prérequis** :
- Notebooks QC-Py-01 à QC-Py-04 terminés
- Comprendre les bases : `Initialize`, `OnData`, indicateurs

**Concepts couverts** :
- `AddCrypto` : ajouter un actif crypto avec marché et résolution
- `self.EMA(...)` : créer un indicateur Exponential Moving Average
- `SetWarmUp` : préchauffer les indicateurs avant de trader
- `SetHoldings` : allouer un pourcentage du portefeuille
- `Liquidate` : vendre toute la position
- `OnOrderEvent` : recevoir les notifications d'exécution

**Modifications suggérées** :
- Changer les périodes EMA : (5, 20), (20, 50) ou (50, 200)
- Ajouter un filtre RSI : ne pas acheter si RSI > 70
- Implémenter un stop-loss à -5 %
- Tester sur d'autres cryptos : ETHUSDT, SOLUSDT

**Documentation complète** : [templates/starter/README.md](templates/starter/README.md)

---

### Intermediate (Intermédiaire)

**Fichier** : `templates/intermediate/main.py`

**Stratégie** : classement momentum sur actions S&P 500 avec l'Alpha Framework

**Prérequis** :
- QC-Py-13 (Alpha Models) terminé
- Comprendre le QC Algorithm Framework

**Modules de l'Alpha Framework** :
| Module | Rôle | Classe |
|--------|------|--------|
| **AlphaModel** | Générer les signaux (Insights) | `MomentumAlphaModel` |
| **PortfolioConstructionModel** | Convertir les Insights en allocations | `EqualWeightingPortfolioConstructionModel` |
| **RiskManagementModel** | Ajuster pour le risque | `TrailingStopRiskManagementModel(0.05)` |
| **ExecutionModel** | Envoyer les ordres | `ImmediateExecutionModel` |

**Modifications suggérées** :
- Changer le lookback momentum : 60, 120 ou 252 jours
- Ajouter un filtre RSI pour éviter les actions surachetées
- Filtrage sectoriel : se concentrer sur des secteurs spécifiques
- Changer le modèle de construction : InsightWeighting, MeanVariance, RiskParity

**Documentation complète** : [templates/intermediate/README.md](templates/intermediate/README.md)

---

### Advanced (Avancé)

**Fichier** : `templates/advanced/main.py`

**Stratégie** : Machine Learning (RandomForest) sur BTCUSDT

**Prérequis** :
- QC-Py-18 (ML Features Engineering) et QC-Py-19 (ML Classification) terminés
- Familier avec sklearn : `RandomForestClassifier`, feature engineering

**Pipeline ML** :
```
Données (BTCUSDT Daily)
    -> Feature Engineering (SMA, RSI, ratios EMA, rendements)
    -> Entraînement RandomForest (100 arbres, max_depth=5)
    -> Prédiction quotidienne (1 = long, 0 = cash)
    -> Ré-entraînement mensuel automatique
```

**Modifications suggérées** :
- Ajouter des features : ADX, ATR, Bollinger Bands, volume
- Essayer d'autres modèles : XGBoost, SVC
- Ajouter des positions courtes (requiert un compte Margin)
- Walk-forward optimization : entraîner sur N mois, tester sur le mois suivant
- Gestion du risque : stop-loss, take-profit, position sizing

**Documentation complète** : [templates/advanced/README.md](templates/advanced/README.md)

---

## Exemples de l'Instructeur

Le répertoire `examples/` contient des projets validés avec des backtests positifs.

### Python - Crypto

| Projet | Cloud ID | Description |
|---------|----------|-------------|
| **Multi-Layer-EMA** | 20216947 | EMA crossover multi-crypto (BTC/ETH/LTC) + filtre RSI |

### Python - Actions/ETFs

| Projet | Cloud ID | Description |
|---------|----------|-------------|
| **Sector-Momentum** | 20216980 | Dual momentum SPY/TLT/GLD + PCM Risk Parity |
| **Trend-Following** | 20216930 | Multi-oracle (MACD/RSI/Bollinger) + ATR trailing stop |

### Python - Options

| Projet | Cloud ID | Description |
|---------|----------|-------------|
| **Options-VGT** | 21113806 | Vente de PUT OTM sur 5 actions tech (NVDA, ORCL, CSCO, AMD, QCOM) |
| **Option-Wheel-Strategy** | 20216898 | Stratégie Wheel SPY : vente PUT -> assignment -> CALL couvert |

### Python - ML

| Projet | Cloud ID | Description |
|---------|----------|-------------|
| **ML-RandomForest** | 29686996 | RandomForest sur large caps, 6 features, ré-entraînement mensuel |
| **Framework-Composite** | 29687005 | Alpha Framework : alphas EMAMomentum + SectorMomentum, MaxDD 15 % |

### C#

| Projet | Cloud ID | Description |
|---------|----------|-------------|
| **CSharp-BTC-MACD-ADX** | 19898232 | BTC MACD+ADX daily sur Binance Cash |
| **CSharp-BTC-EMA-Cross** | 19050970 | Crossover EMA BTC classique (18/23) |
| **CSharp-CTG-Momentum** | 19225388 | « Stocks on the Move » (Clenow) — Momentum ranking |

---

## Kit de Transition — Stratégies ML & Framework

Le répertoire [`kit-transitoire/`](kit-transitoire/README.md) regroupe **trois stratégies progressives de rotation sectorielle** (univers de 9 ETFs `XLK`..`XLRE`), chacune livrée avec un `main.py` déployable sur QC Cloud et un notebook de recherche QuantBook (`research.ipynb`) documentant les itérations et le calibrage. Backtests validés sur 2015-2024.

| # | Stratégie | Type | Sharpe | CAGR | Max DD |
|---|-----------|------|--------|------|--------|
| 01 | **ML RandomForest** | Classification (14 features, ré-entraînement mensuel) | 0.556 | 11.43 % | 17.2 % |
| 02 | **ML XGBoost** | Régression (20 features, ré-entraînement bi-hebdomadaire) | 0.521 | 12.81 % | 39.1 % |
| 03 | **Framework Composite** | Alpha Models (`SectorMomentum` + `Defensive`, `MultiStrategyPCM` 70/30, `MaxDrawdownCircuitBreaker` 15 %) | 0.376 | 7.60 % | 20.6 % |

Les trois stratégies partagent un filtre baissier (`SPY < SMA200` -> max 2 positions) et illustrent la progression pédagogique : ML supervisé -> ML avancé avec features riches -> architecture QC Framework propre (alpha models + PCM + risk). Documentation détaillée et comparaison complète : [`kit-transitoire/README.md`](kit-transitoire/README.md).

---

## Notebooks de Recherche (QuantBook)

Cinq projets Researcher avec des notebooks QuantBook opérationnels pour explorer les données QC Cloud :

| Projet | Cloud ID | QuantBook | Contenu de recherche |
|---------|----------|-----------|----------------------|
| **Multi-Layer-EMA-Researcher** | 28433748 | research.ipynb | Grid search EMA/RSI/stop-loss sur BTC/ETH/LTC |
| **BTC-ML-Researcher** | 28433750 | research.ipynb | Feature importance, walk-forward, confidence grid |
| **MomentumStrategy-Researcher** | 28657837 | quantbook.ipynb | H1-H4 : top-N, lookback, fenêtre de vol, filtre de régime |
| **AllWeather-Researcher** | 28657833 | quantbook.ipynb | Grid search allocations All-Weather (SPY/IEF/GLD/XLP) |
| **Sector-Momentum-Researcher** | 28433643 | quantbook.ipynb + research.ipynb | Dual Momentum SPY/TLT/GLD, refonte complète |

Ces notebooks illustrent le workflow QuantBook -> QCAlgorithm : idée -> recherche -> backtest.

---

## Recherche ML 2026 — Modèles Validés (Pipeline V2)

Le pipeline de recherche ML (`ML-Training-Pipeline/`) suit un curriculum en 7 étapes
basé sur *Hands-On AI Trading* (Broad/QuantConnect, 2025). Les modèles ci-dessous ont passé
le **gate S1 (vol-forecasting)** avec un test de Diebold-Mariano significatif
(p < 0,05, >= 4 seeds, walk-forward 5-fold).

### S1 KEEPERS — Prévision de volatilité multi-coin (BEATS)

| Modèle | Tâche | Verdict | DM p-value | Architecture |
|-------|------|---------|-----------|--------------|
| **M12 HAR-RV-J** | Prévision de vol à 5 jours | BEATS RW + GARCH | **0,0015** | Heterogeneous Autoregressive + composante de Jump (Corsi 2009) |
| **M15 LSTM h=32** | Prévision de vol court-terme | BEATS RW | **0,0107** | LSTM hidden=32, 53/84 combos BEAT cross-coin (BTC/XRP/DOT/ADA) |

Complémentarité observée : M12 capte mieux ETH/SOL, M15 capte mieux DOT.

### S3 — HMM Regime daily (livré, alimente le sizing S5)

Hidden Markov Model 2-régimes (calme vs stress) sur les rendements daily SPY+VIX+BTC.
La sortie discrète est utilisée comme switch dans les stratégies vol-target (réduction de l'exposition en régime stress).

### S4 v2 — Inverse-Vol Ridge + HMM Regime (BEATS EqW)

Allocation pondérée inverse-vol avec régression Ridge sur les features
(momentum + prévision de vol M12) et switch HMM. Delta Sharpe **+0,325 vs EqW**
(baseline Equal Weight) sur backtest QC Cloud.

### L4 Decision Transformer — Trading basé actions (BEATS)

Premier modèle à battre le buy-and-hold sur 24/26 symboles. L'approche basée actions (classification buy/hold/sell)
surpasse massivement les approches basées prévision (PatchTST). AUC médian 0,5582, 104 combos validés.

### Stratégies QC Cloud alimentées par ces modèles

| Projet QC Cloud | Cloud ID | Modèle source | Description |
|-----------------|----------|-------------|-------------|
| **HAR-RV-Kelly** | 31456164 | M12 HAR-RV-J | Prévision de vol -> sizing Kelly 1/4 sur SPY/EFA/EEM/TLT/GLD/DBC |
| **Vol-GARCH-Target** | 31456084 | GARCH(1,1) baseline | Vol-targeting 15 % annualisé (référence pour M12) |
| **Vol-Ensemble-Conservative** | 31456204 | Ensemble M12+M15 | Pondération inverse-vol + cap de levier |

Ces projets sont disponibles dans `../projects/`.

---

## Concepts Pédagogiques Couverts

Les exemples et templates couvrent **4 classes d'actifs** et **8+ concepts de trading** :

| Niveau | Concepts | Stratégies |
|-------|----------|------------|
| **1 - Fondations** | EMA Crossover, MACD+ADX, Options de base | Multi-Layer-EMA, CSharp-BTC-EMA-Cross, Options-VGT |
| **2 - Intermédiaire** | Alpha Framework, Multi-indicateurs, Wheel Strategy | Sector-Momentum, Option-Wheel-Strategy, Trend-Following |
| **3 - Avancé** | Momentum ranking, Risk Parity, ML | CSharp-CTG-Momentum, Sector-Momentum, ML-RandomForest |

---

## Résultats de Backtest

### Exemples de l'instructeur — 8 projets validés

| # | Projet | Sharpe | CAGR | Max DD |
|---|---------|--------|------|--------|
| 1 | **Sector-Momentum** | 2.530 | 66.1 % | 5.6 % |
| 2 | **Trend-Following** | 2.157 | 136.0 % | 20.5 % |
| 3 | **Multi-Layer-EMA** | 1.891 | 120.9 % | 54.4 % |
| 4 | **CSharp-BTC-MACD-ADX** | 1.224 | 38.1 % | 48.8 % |
| 5 | **CSharp-BTC-EMA-Cross** | 1.094 | 36.2 % | 40.7 % |
| 6 | **Options-VGT** | 0.892 | 25.3 % | 15.6 % |
| 7 | **Option-Wheel-Strategy** | 0.524 | 12.7 % | 26.4 % |
| 8 | **CSharp-CTG-Momentum** | 0.507 | 17.7 % | 36.1 % |

---

## Parcours d'Apprentissage Recommandé

### Pour les débutants

1. **Notebooks de fondation** : QC-Py-01 à QC-Py-04 (~4,5h)
2. **Template Starter** : comprendre et modifier `templates/starter/main.py`
3. **Premier projet personnel** : adapter le template avec vos idées
4. **Itération** : backtester, analyser les résultats, améliorer

### Pour les intermédiaires

1. **Notebooks Alpha Framework** : QC-Py-13 à QC-Py-15 (~4h)
2. **Template Intermediate** : étudier `templates/intermediate/main.py`
3. **Projets exemples** : analyser `Sector-Momentum`, `Trend-Following`
4. **Projet personnel** : créer votre propre stratégie avec l'Alpha Framework

### Pour les avancés

1. **Notebooks ML** : QC-Py-18 à QC-Py-21 (~4h)
2. **Template Advanced** : étudier `templates/advanced/main.py`
3. **Projets ML** : analyser `BTC-MachineLearning`, `Sector-ML-Classification`
4. **Recherche avancée** : features engineering, hyperparameter tuning, walk-forward

---

## Notebooks Compagnons

La série Python progressive dans [`../Python/`](../Python/README.md) (notebooks `QC-Py-*`) accompagne ce cours partenaire. Elle couvre l'écosystème QC de bout en bout, du premier algorithme au déploiement live :

1. **Setup** : compte, IDE, premier algorithme
2. **Fondations** : API, Resolution, Consolidators, QuantBook
3. **Indicateurs** : MACD, RSI, Bollinger, EMA
4. **Stratégies** : Mean Reversion, Momentum, Pairs Trading, Options
5. **Framework** : Alpha, Portfolio Construction, Risk, Execution
6. **ML/AI** : Features, modèles, ObjectStore, RL, NLP
7. **Production** : paper trading, live, monitoring

Le catalogue détaillé et les comptes à jour (les notebooks `QC-Py-*` continuent de croître) se trouvent dans le README canonique [`../Python/README.md`](../Python/README.md).

---

## Documentation

- **[GETTING-STARTED.md](../GETTING-STARTED.md)** : guide de démarrage détaillé
- **[projects/README.md](../projects/README.md)** : catalogue de stratégies

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Ce cours partenaire est une **plateforme de démarrage structurée** vers le trading algorithmique professionnel sur QuantConnect, pensée pour des étudiants partant de zéro jusqu'à un projet personnel ML. Il s'appuie sur deux piliers :

- **Le workflow Cloud-First** : tout le développement se fait sur QuantConnect Cloud (QC Lab), sans installation locale — accès direct aux données historiques QC, compilation instantanée, et sponsoring *Trading Firm* offert par Jared Broad / QuantConnect. On apprend que la plateforme gère l'infrastructure pour que l'étudiant se concentre sur la *stratégie*, pas sur le plumbing.
- **Les templates progressifs** : trois points de départ (`starter` → `intermediate` → `advanced`) calibrés par difficulté croissante. Le `starter` (EMA crossover sur BTCUSDT) enseigne le `QCAlgorithm` lifecycle ; l'`intermediate` introduit l'Algorithm Framework modulaire ; l'`advanced` ajoute le machine learning. On apprend qu'**un bon template est un échafaudage** : il code les bonnes pratiques (Initialize, Risk Management, execution) pour que l'étudiant itère sur l'alpha, pas sur la plomberie.
- **Les exemples de projets** (`Sector-Momentum`, `Trend-Following`, `BTC-MachineLearning`, `Sector-ML-Classification`) montrent des stratégies *achevées* à étudier puis adapter. On apprend que **lire du code qui marche** est aussi formateur que d'en écrire.

Le fil rouge : la **progression pédagogique** — les 28 notebooks compagnons (`../Python/`, QC-Py-01 à 28) fournissent la théorie, et ce cours fournit la *pratique guidée* via templates et exemples. Les deux sont conçus pour avancer ensemble.

### Prochaines étapes

1. **Créer votre compte** sur [quantconnect.com](https://www.quantconnect.com) avec votre email d'école, puis envoyer votre username à l'instructeur pour rejoindre l'organisation *Trading Firm*.
2. **Faire les fondations** : notebooks QC-Py-01 à 04 avant tout (compte, lifecycle, data, QuantBook).
3. **Démarrer avec le template `starter`** : copier `templates/starter/main.py` dans un projet QC Lab, le backtester, puis le modifier (changer la paire, la période EMA).
4. **Monter de niveau** : passer à `intermediate` (Algorithm Framework) puis `advanced` (ML) à mesure que vous maîtrisez le niveau précédent.
5. **Étudier puis adapter un exemple** : analyser `Sector-Momentum` ou `Trend-Following`, comprendre chaque module, puis créer votre propre variante comme projet personnel.
6. **Consulter le catalogue** : `../projects/README.md` recense les 50+ stratégies backtestées de la série complète pour inspiration et comparaison.

> **Rappel honnête** : un template qui backteste bien n'est pas une stratégie déployable. Le sponsoring vous donne l'infrastructure, pas l'edge. La même discipline que dans toute la série QuantConnect s'applique : walk-forward, out-of-sample, et Sharpe *net* après frais avant de croire à un résultat.

---

## Ressources

- [QuantConnect Documentation](https://www.quantconnect.com/docs)
- [Hands-On AI Trading Book](https://www.hands-on-ai-trading.com)
- [Book GitHub](https://github.com/QuantConnect/HandsOnAITradingBook)
- **Version anglaise (snapshot pré-bascule)** : [README.en.md](README.en.md)
