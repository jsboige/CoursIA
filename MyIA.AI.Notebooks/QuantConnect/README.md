# QuantConnect AI Trading - Série Éducative CoursIA

> **Trading algorithmique + Intelligence Artificielle**
> 28 notebooks Python | Cloud-first | Free Tier compatible

---

## Pour Commencer (4 étapes)

1. **Créer un compte gratuit** : [https://www.quantconnect.com/signup](https://www.quantconnect.com/signup)
2. **Créer un projet Python** dans QC Lab (File > New Project)
3. **Copier un `main.py`** depuis `projects/` (ex: `EMA-Cross-Stocks/`) dans votre projet
4. **Cliquer Backtest** pour exécuter

**Temps estimé** : 5-10 minutes

> **Note** : Les notebooks QC-Py-XX sont des supports de cours à lire sur GitHub, pas à uploader dans QC Lab.

---

## Vue d'Ensemble

Cette série est une formation complète sur le **trading algorithmique** avec la plateforme **QuantConnect LEAN**, inspirée du livre *"Hands-On AI Trading"* (2025).

### Objectifs

- **Pédagogique** : Progression de débutant à expert (30h de contenu)
- **IA-first** : Focus important sur ML/DL/RL/LLM pour stratégies de trading
- **Cloud-native** : Exécution principale sur QuantConnect cloud (free tier)
- **Production-ready** : De la recherche au déploiement live

### Contenu

- **28 notebooks Python** organisés en 8 phases
- **18 notebooks sur fondations** avant ML (Universe, Asset Classes, Risk, Framework)
- **9 notebooks ML/DL/AI** (Supervised Learning, Deep Learning, RL, LLM)
- **Free tier compatible** avec workarounds pour fonctionnalités payantes

---

## Structure de la Série

### Phase 1 : Fondations LEAN (4 notebooks, ~4.5h)

Maîtriser les bases de QuantConnect : architecture, lifecycle d'algorithme, gestion des données, workflow de recherche.

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 01 | [QC-Py-01-Setup](Python/QC-Py-01-Setup.ipynb) | 45 min | Compte QC, premier backtest cloud, architecture LEAN |
| 02 | [QC-Py-02-Platform-Fundamentals](Python/QC-Py-02-Platform-Fundamentals.ipynb) | 60 min | QCAlgorithm lifecycle, Initialize/OnData, Moving Average Crossover |
| 03 | [QC-Py-03-Data-Management](Python/QC-Py-03-Data-Management.ipynb) | 75 min | History API, data normalization, consolidators, multi-timeframe |
| 04 | [QC-Py-04-Research-Workflow](Python/QC-Py-04-Research-Workflow.ipynb) | 75 min | QuantBook, pandas integration, notebook→algorithm transition |

**Objectifs** : Créer compte gratuit, maîtriser cycle de vie algorithme, gestion des données.

---

### Phase 2 : Universe et Asset Classes (4 notebooks, ~5h)

Sélection dynamique d'univers, comprendre les particularités de chaque classe d'actifs (Equities, Options, Futures, Forex).

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 05 | [QC-Py-05-Universe-Selection](Python/QC-Py-05-Universe-Selection.ipynb) | 75 min | Manual universe, coarse/fine selection, dynamic rebalancing |
| 06 | [QC-Py-06-Options-Trading](Python/QC-Py-06-Options-Trading.ipynb) | 75 min | Options chains, Greeks, covered calls, protective puts |
| 07 | [QC-Py-07-Futures-Forex](Python/QC-Py-07-Futures-Forex.ipynb) | 75 min | Futures contracts, rollover, Forex pairs, leverage |
| 08 | [QC-Py-08-Multi-Asset-Strategies](Python/QC-Py-08-Multi-Asset-Strategies.ipynb) | 75 min | Portfolio Equity + Options + Futures, corrélations |

**Objectifs** : Maîtriser sélection dynamique d'univers, comprendre chaque classe d'actifs.

---

### Phase 3 : Trading Avancé et Risk Management (4 notebooks, ~5.5h)

Gestion du risque professionnelle, types d'ordres avancés, analyse approfondie de backtests.

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 09 | [QC-Py-09-Order-Types](Python/QC-Py-09-Order-Types.ipynb) | 75 min | Market, Limit, Stop, Stop-Limit, combo orders |
| 10 | [QC-Py-10-Risk-Portfolio-Management](Python/QC-Py-10-Risk-Portfolio-Management.ipynb) | 90 min | Position sizing (Kelly, fixed fractional), stop-loss, take-profit |
| 11 | [QC-Py-11-Technical-Indicators](Python/QC-Py-11-Technical-Indicators.ipynb) | 75 min | Indicateurs intégrés, custom indicators, signal generation |
| 12 | [QC-Py-12-Backtesting-Analysis](Python/QC-Py-12-Backtesting-Analysis.ipynb) | 75 min | Performance metrics (Sharpe, Sortino, max drawdown), equity curve |

**Objectifs** : Maîtriser gestion du risque, ordres avancés, analyse de backtests.

---

### Phase 4 : Algorithm Framework (3 notebooks, ~4h)

Architecture modulaire QuantConnect pour stratégies scalables (Alpha, Portfolio Construction, Execution, Risk).

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 13 | [QC-Py-13-Alpha-Models](Python/QC-Py-13-Alpha-Models.ipynb) | 75 min | Algorithm Framework intro, Alpha models, insights |
| 14 | [QC-Py-14-Portfolio-Construction-Execution](Python/QC-Py-14-Portfolio-Construction-Execution.ipynb) | 90 min | Portfolio construction models, execution models, risk models |
| 15 | [QC-Py-15-Parameter-Optimization](Python/QC-Py-15-Parameter-Optimization.ipynb) | 75 min | Parameter sets, optimization targets, overfitting prevention |

**Objectifs** : Maîtriser architecture modulaire, optimisation systématique.

---

### Phase 5 : Alternative Data et Préparation ML (3 notebooks, ~4h)

Intégrer données alternatives (news, sentiment, fundamentals), préparer datasets pour Machine Learning.

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 16 | [QC-Py-16-Alternative-Data](Python/QC-Py-16-Alternative-Data.ipynb) | 75 min | NewsAPI (gratuit), fundamentals, custom data sources |
| 17 | [QC-Py-17-Sentiment-Analysis](Python/QC-Py-17-Sentiment-Analysis.ipynb) | 75 min | Sentiment scoring (TextBlob, VADER), news aggregation |
| 18 | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) | 90 min | Feature extraction, labeling, train/test split, feature importance |

**Objectifs** : Intégrer données alternatives, préparer datasets pour ML.

---

### Phase 6 : Machine Learning Traditionnel (3 notebooks, ~4h)

Appliquer ML classique au trading : classification directionnelle, régression pour prédiction de prix.

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 19 | [QC-Py-19-ML-Supervised-Classification](Python/QC-Py-19-ML-Supervised-Classification.ipynb) | 75 min | Random Forest, XGBoost, direction prediction, walk-forward |
| 20 | [QC-Py-20-ML-Regression-Prediction](Python/QC-Py-20-ML-Regression-Prediction.ipynb) | 75 min | Linear regression, SVR, price target prediction |
| 21 | [QC-Py-21-Portfolio-Optimization-ML](Python/QC-Py-21-Portfolio-Optimization-ML.ipynb) | 90 min | ML-enhanced Markowitz, covariance estimation via ML |

**Objectifs** : Appliquer ML classique au trading, persistence modèles avec ObjectStore.

---

### Phase 7 : Deep Learning (3 notebooks, ~4.5h)

Deep Learning pour séries temporelles : LSTM, Transformers, Autoencoders.

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 22 | [QC-Py-22-Deep-Learning-LSTM](Python/QC-Py-22-Deep-Learning-LSTM.ipynb) | 90 min | LSTM time series, TensorFlow/Keras, CPU-first |
| 23 | [QC-Py-23-Attention-Transformers](Python/QC-Py-23-Attention-Transformers.ipynb) | 90 min | Transformer architecture, multi-head attention, temporal fusion |
| 24 | [QC-Py-24-Autoencoders-Anomaly](Python/QC-Py-24-Autoencoders-Anomaly.ipynb) | 75 min | Autoencoders pour détection anomalies, regime change |

**Objectifs** : Maîtriser deep learning pour séries temporelles, design CPU-optimized.

---

### Phase 8 : IA Avancée et Production (3 notebooks, ~4.5h)

État de l'art : Reinforcement Learning, LLM pour trading signals, déploiement production.

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 25 | [QC-Py-25-Reinforcement-Learning](Python/QC-Py-25-Reinforcement-Learning.ipynb) | 90 min | PPO/DQN agents, Stable-Baselines3, Gym environment custom |
| 26 | [QC-Py-26-LLM-Trading-Signals](Python/QC-Py-26-LLM-Trading-Signals.ipynb) | 90 min | OpenAI/Anthropic API, prompt engineering, LLM+indicators hybrid |
| 27 | [QC-Py-27-Production-Deployment](Python/QC-Py-27-Production-Deployment.ipynb) | 75 min | Paper trading, live trading setup, monitoring, deployment |
| 28 | [QC-Py-28-Market-Regime-Detection](Python/QC-Py-28-Market-Regime-Detection.ipynb) | 75 min | HMM, regime detection, allocation adaptative |

**Objectifs** : IA state-of-the-art pour trading, déploiement production.

---

## Résumé de la Progression

**Total** : **28 notebooks Python** (~32 heures de contenu)

**Répartition** :
- **18 notebooks non-ML** (Fondations, Universe, Trading Avancé, Framework, Alternative Data) : ~18h
- **9 notebooks ML/DL/AI** (Supervised Learning, Deep Learning, RL, LLM) : ~12h

**Progression pédagogique** : Maîtriser les fondations QuantConnect **avant** d'aborder le Machine Learning.

---

## Notebooks Progressifs

**Recommandé pour débuter** :

1. **Phase 1** : Fondations LEAN (4.5h)
2. **Phase 2** : Universe et Asset Classes (5h)
3. **Phase 3** : Trading Avancé et Risk (5.5h)
4. **Notebooks 13-15** : Algorithm Framework (4h)
5. Premier projet : Stratégie momentum avec risk management

**Intermédiaire** (40h) : Phases 4-6 complètes + ML traditionnel

**Expert** (60h) : Phases 6-8 complètes + Deep dive LSTMs, Transformers, RL + déploiement

---

## Projets de Stratégies

Le dossier [`projects/`](projects/) contient **67 stratégies de trading** prêtes à backtester.

### Comment utiliser les projets

1. Choisir une stratégie dans [`projects/README.md`](projects/README.md)
2. Copier le `main.py` dans votre projet QuantConnect Lab
3. Lancer le backtest
4. Analyser les résultats (Sharpe, Max Drawdown, CAGR)

### Exemples de stratégies populaires

| Stratégie | Description | Niveau |
|-----------|-------------|--------|
| [EMA-Cross-Stocks](projects/EMA-Cross-Stocks/) | EMA 20/50 multi-stock (AAPL/MSFT/GOOGL/AMZN/NVDA) | Débutant |
| [TrendStocksLite](projects/TrendStocksLite/) | EMA20/50 + SMA200 trend 15 large-caps | Intermédiaire |
| [SectorMomentum](projects/SectorMomentum/) | Dual Momentum SPY/TLT/GLD (Antonacci) | Intermédiaire |
| [ML-RandomForest](projects/ML-RandomForest/) | Random Forest classification multi-asset | Avancé |
| [Option-Wheel](projects/Option-Wheel/) | Wheel strategy SPY (sell puts/calls) | Avancé |

---

## ESGF-2026 - Exemples de Recherche

Le dossier **ESGF-2026/** contient des exemples de recherche avancée utilisés dans le cours ESGF 2026.

### Structure ESGF-2026

```
ESGF-2026/
├── examples/           # 11 projets d'exemples du professeur
├── templates/          # Templates pour projets étudiants
│   ├── starter/        # Niveau débutant
│   ├── intermediate/   # Niveau intermédiaire
│   └── advanced/       # Niveau avancé
└── archive-2025/       # Archives historiques
```

Voir [ESGF-2026/README.md](ESGF-2026/README.md) pour le détail des exemples et templates.

---

## Documentation Complémentaire

### Guides de démarrage

- **[GETTING-STARTED.md](GETTING-STARTED.md)** : Guide de démarrage détaillé
- **[ECE-QC-QUICKSTART.md](ECE-QC-QUICKSTART.md)** : Guide pour étudiants ECE
- **[HANDSON_AI_TRADING_MAPPING.md](docs/HANDSON_AI_TRADING_MAPPING.md)** : Mapping avec le livre "Hands-On AI Trading"

### Bibliothèques partagées

Le dossier [`shared/`](shared/) contient des modules Python réutilisables :

- **features.py** : Feature engineering ML
- **indicators.py** : Custom indicators QuantConnect
- **ml_utils.py** : ML training, persistence (ObjectStore)
- **plotting.py** : Visualisations standardisées
- **backtest_helpers.py** : Helpers configuration backtests

### Scripts de validation

| Script | Description |
|--------|-------------|
| `scripts/validate_qc_notebooks.py` | Validation structure notebooks |
| `scripts/test_algorithms.py` | Automated backtest runner |

---

## Ressources Externes

### Documentation QuantConnect

- [Documentation officielle](https://www.quantconnect.com/docs)
- [LEAN Engine GitHub](https://github.com/QuantConnect/Lean)
- [Algorithm Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework/overview)

### Livre de référence

**"Hands-On AI Trading with Python, QuantConnect, and AWS"** (Janvier 2025, Wiley)

- [Site officiel](https://www.hands-on-ai-trading.com)
- [GitHub du livre](https://github.com/QuantConnect/HandsOnAITradingBook)
- [Amazon (livre)](https://www.amazon.com/dp/1394268432)

### Communauté

- [QuantConnect Forum](https://www.quantconnect.com/forum)
- [LEAN Discussions](https://github.com/QuantConnect/Lean/discussions)
- [CoursIA Main README](../../README.md)

---

## Configuration

### Variables d'environnement (.env)

Copiez `.env.example` vers `.env` et configurez :

```bash
# Authentification QuantConnect Cloud
QC_API_USER_ID=your_user_id_here
QC_API_ACCESS_TOKEN=your_access_token_here

# APIs IA/ML (optionnel, pour notebooks 17, 26)
OPENAI_API_KEY=sk-...
ANTHROPIC_API_KEY=sk-ant-...
HUGGINGFACE_TOKEN=hf_...

# NewsAPI (gratuit, pour notebook 17)
NEWSAPI_KEY=your_newsapi_key_here
```

### Dépendances Python

```bash
# Créer environnement virtuel
python -m venv venv
venv\Scripts\activate  # Windows
source venv/bin/activate  # Linux/macOS

# Installer dépendances
pip install -r requirements.txt

# Installer kernel Jupyter
python -m ipykernel install --user --name=quantconnect --display-name "Python (QuantConnect)"
```

---

## Free Tier vs Paid

| Fonctionnalité | Free Tier | Paid (Team/Premium) |
|----------------|-----------|---------------------|
| **Backtesting** | ✅ Illimité (8h calcul/mois) | ✅ Illimité (plus d'heures) |
| **Paper trading** | ✅ | ✅ |
| **Données Equity/Crypto/Forex** | ✅ Depuis 2010 | ✅ Depuis 1998 |
| **Alternative data** | ❌ (workaround : NewsAPI gratuit) | ✅ TiingoNews, etc. |
| **GPU pour Deep Learning** | ❌ (CPU local) | ✅ GPU cloud |
| **Live trading** | ❌ | ✅ |

**Workarounds Free Tier** :
- **QC-17 Sentiment** : NewsAPI gratuit au lieu de TiingoNews payant
- **QC-22/23/24 Deep Learning** : CPU-optimized
- **QC-27 Production** : Paper trading (simulation gratuite)

---

## Résultats Attendus

Après completion de cette série, vous maîtriserez :

### Compétences Techniques

- ✅ **QuantConnect LEAN** : Architecture, lifecycle, Universe selection
- ✅ **Risk Management** : Position sizing, stop-loss, take-profit
- ✅ **Algorithm Framework** : Alpha, Portfolio Construction, Execution, Risk
- ✅ **Machine Learning** : Supervised (RF, XGBoost), Deep Learning (LSTM), RL (PPO)
- ✅ **LLM Integration** : Prompt engineering, LLM-augmented signals
- ✅ **Production Deployment** : Paper trading, live trading, monitoring

### Projets Réalisables

- 🎯 Stratégie momentum multi-actifs avec risk management
- 🤖 Bot ML directionnel avec Random Forest + XGBoost
- 🧠 Stratégie LSTM pour prédiction prix court-terme
- 💡 LLM-augmented strategy combinant GPT-4 + indicateurs
- 🏭 Déploiement production en paper trading

---

**Bon trading algorithmique avec QuantConnect + CoursIA !**

*Créé par CoursIA | Inspiré par "Hands-On AI Trading" (Jared Broad, 2025) | Cloud-first Architecture*
