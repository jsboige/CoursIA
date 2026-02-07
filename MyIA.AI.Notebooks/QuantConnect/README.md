# QuantConnect AI Trading - Série Éducative CoursIA

> **Trading algorithmique + Intelligence Artificielle**
> 54 notebooks progressifs | Python + C# | Cloud-first | Free Tier compatible

---

## Vue d'Ensemble

La série QuantConnect AI Trading est une formation complète sur le trading algorithmique avec la plateforme **QuantConnect LEAN**, inspirée du livre **"Hands-On AI Trading"** (2025) coécrit par Jared Broad (CEO QuantConnect).

### Objectifs

- **Pédagogique** : Progression structurée de débutant à expert (30h de contenu par langage)
- **IA-first** : Focus important sur ML/DL/RL/LLM pour stratégies de trading (9 notebooks dédiés)
- **Cloud-native** : Exécution principale sur QuantConnect cloud (free tier)
- **Dual-language** : Python ET C# en parallèle (27 notebooks × 2 langages)
- **Production-ready** : De la recherche au déploiement live

### Caractéristiques

- **27 notebooks Python** + **27 notebooks C#** = **54 notebooks au total**
- **18 notebooks sur fondations** (Universe, Asset Classes, Risk, Framework) avant ML
- **9 notebooks ML/DL/AI** (Supervised Learning, Deep Learning, RL, LLM)
- **Approche cloud-first** avec option locale Docker + LEAN CLI
- **Free tier compatible** avec workarounds pour fonctionnalités payantes
- **Intégration MCP** pour automatisation avec Claude Code

---

## Démarrage Rapide

**Pour commencer immédiatement**, consultez le guide : [**GETTING-STARTED.md**](GETTING-STARTED.md)

**Résumé en 3 étapes** :

1. Créer un compte gratuit : [https://www.quantconnect.com/signup](https://www.quantconnect.com/signup)
2. Uploader `QC-Py-01-Setup.ipynb` dans QuantConnect Lab
3. Exécuter toutes les cellules et suivre les instructions

**Temps estimé** : 5-10 minutes

---

## Structure de la Série

### Phase 1 : Fondations LEAN (4 notebooks, ~4.5h par langage)

Maîtriser les bases de QuantConnect : architecture, lifecycle d'algorithme, gestion des données, workflow de recherche.

| # | Python | C# | Durée | Contenu |
|---|--------|----|----|---------|
| 01 | [QC-Py-01-Setup](Python/QC-Py-01-Setup.ipynb) | [QC-CS-01-Setup](CSharp/QC-CS-01-Setup.ipynb) | 45 min | Compte QC, premier backtest cloud, option LEAN CLI local, architecture LEAN |
| 02 | [QC-Py-02-Platform-Fundamentals](Python/QC-Py-02-Platform-Fundamentals.ipynb) | [QC-CS-02-Platform-Fundamentals](CSharp/QC-CS-02-Platform-Fundamentals.ipynb) | 60 min | QCAlgorithm lifecycle, Initialize/OnData, securities, Moving Average Crossover |
| 03 | [QC-Py-03-Data-Management](Python/QC-Py-03-Data-Management.ipynb) | [QC-CS-03-Data-Management](CSharp/QC-CS-03-Data-Management.ipynb) | 75 min | History API, data normalization, consolidators, multi-timeframe analysis |
| 04 | [QC-Py-04-Research-Workflow](Python/QC-Py-04-Research-Workflow.ipynb) | [QC-CS-04-Research-Workflow](CSharp/QC-CS-04-Research-Workflow.ipynb) | 75 min | QuantBook, pandas/DataFrame integration, notebook→algorithm transition |

**Objectifs** : Créer compte gratuit, maîtriser cycle de vie algorithme, gestion des données, outils de recherche.

---

### Phase 2 : Universe et Asset Classes (4 notebooks, ~5h par langage)

Sélection dynamique d'univers, comprendre les particularités de chaque classe d'actifs (Equities, Options, Futures, Forex).

| # | Python | C# | Durée | Contenu |
|---|--------|----|----|---------|
| 05 | [QC-Py-05-Universe-Selection](Python/QC-Py-05-Universe-Selection.ipynb) | [QC-CS-05-Universe-Selection](CSharp/QC-CS-05-Universe-Selection.ipynb) | 75 min | Manual universe, coarse/fine selection, dynamic rebalancing, filters (dollar volume, fundamentals) |
| 06 | [QC-Py-06-Options-Trading](Python/QC-Py-06-Options-Trading.ipynb) | [QC-CS-06-Options-Trading](CSharp/QC-CS-06-Options-Trading.ipynb) | 75 min | Options chains, Greeks, covered calls, protective puts, iron condors |
| 07 | [QC-Py-07-Futures-Forex](Python/QC-Py-07-Futures-Forex.ipynb) | [QC-CS-07-Futures-Forex](CSharp/QC-CS-07-Futures-Forex.ipynb) | 75 min | Futures contracts, rollover, Forex pairs, leverage management |
| 08 | [QC-Py-08-Multi-Asset-Strategies](Python/QC-Py-08-Multi-Asset-Strategies.ipynb) | [QC-CS-08-Multi-Asset-Strategies](CSharp/QC-CS-08-Multi-Asset-Strategies.ipynb) | 75 min | Portfolio avec Equity + Options + Futures, corrélations, hedging |

**Objectifs** : Maîtriser sélection dynamique d'univers, comprendre les particularités de chaque classe d'actifs.

---

### Phase 3 : Trading Avancé et Risk Management (4 notebooks, ~5.5h par langage)

Gestion du risque professionnelle, types d'ordres avancés, analyse approfondie de backtests.

| # | Python | C# | Durée | Contenu |
|---|--------|----|----|---------|
| 09 | [QC-Py-09-Order-Types](Python/QC-Py-09-Order-Types.ipynb) | [QC-CS-09-Order-Types](CSharp/QC-CS-09-Order-Types.ipynb) | 75 min | Market, Limit, Stop, Stop-Limit, MOO/MOC, combo orders, order management |
| 10 | [QC-Py-10-Risk-Portfolio-Management](Python/QC-Py-10-Risk-Portfolio-Management.ipynb) | [QC-CS-10-Risk-Portfolio-Management](CSharp/QC-CS-10-Risk-Portfolio-Management.ipynb) | 90 min | Position sizing (Kelly, fixed fractional), stop-loss, take-profit, portfolio heat |
| 11 | [QC-Py-11-Technical-Indicators](Python/QC-Py-11-Technical-Indicators.ipynb) | [QC-CS-11-Technical-Indicators](CSharp/QC-CS-11-Technical-Indicators.ipynb) | 75 min | Indicateurs intégrés, custom indicators, rolling windows, signal generation |
| 12 | [QC-Py-12-Backtesting-Analysis](Python/QC-Py-12-Backtesting-Analysis.ipynb) | [QC-CS-12-Backtesting-Analysis](CSharp/QC-CS-12-Backtesting-Analysis.ipynb) | 75 min | Performance metrics (Sharpe, Sortino, max drawdown), equity curve analysis, insights |

**Objectifs** : Maîtriser gestion du risque, ordres avancés, analyse approfondie de backtests.

---

### Phase 4 : Algorithm Framework (3 notebooks, ~4h par langage)

Architecture modulaire QuantConnect pour stratégies scalables (Alpha, Portfolio Construction, Execution, Risk).

| # | Python | C# | Durée | Contenu |
|---|--------|----|----|---------|
| 13 | [QC-Py-13-Alpha-Models](Python/QC-Py-13-Alpha-Models.ipynb) | [QC-CS-13-Alpha-Models](CSharp/QC-CS-13-Alpha-Models.ipynb) | 75 min | Algorithm Framework intro, Alpha models (manual, technical, fundamental), insights |
| 14 | [QC-Py-14-Portfolio-Construction-Execution](Python/QC-Py-14-Portfolio-Construction-Execution.ipynb) | [QC-CS-14-Portfolio-Construction-Execution](CSharp/QC-CS-14-Portfolio-Construction-Execution.ipynb) | 90 min | Portfolio construction models (equal weighting, mean-variance), execution models, risk models |
| 15 | [QC-Py-15-Parameter-Optimization](Python/QC-Py-15-Parameter-Optimization.ipynb) | [QC-CS-15-Parameter-Optimization](CSharp/QC-CS-15-Parameter-Optimization.ipynb) | 75 min | Parameter sets, optimization targets (Sharpe, return), genetic algorithms, overfitting prevention |

**Alignement QuantConnect** : [Algorithm Framework Documentation](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework/overview)

**Objectifs** : Maîtriser architecture modulaire QuantConnect, optimisation systématique de paramètres.

---

### Phase 5 : Alternative Data et Préparation ML (3 notebooks, ~4h par langage)

Intégrer données alternatives (news, sentiment, fundamentals), préparer datasets pour Machine Learning.

| # | Python | C# | Durée | Contenu |
|---|--------|----|----|---------|
| 16 | [QC-Py-16-Alternative-Data](Python/QC-Py-16-Alternative-Data.ipynb) | [QC-CS-16-Alternative-Data](CSharp/QC-CS-16-Alternative-Data.ipynb) | 75 min | NewsAPI (gratuit), fundamentals (P/E, EPS), custom data sources, event-driven strategies |
| 17 | [QC-Py-17-Sentiment-Analysis](Python/QC-Py-17-Sentiment-Analysis.ipynb) | [QC-CS-17-Sentiment-Analysis](CSharp/QC-CS-17-Sentiment-Analysis.ipynb) | 75 min | Sentiment scoring (TextBlob, VADER), news aggregation, sentiment-driven signals |
| 18 | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) | [QC-CS-18-ML-Features-Engineering](CSharp/QC-CS-18-ML-Features-Engineering.ipynb) | 90 min | Feature extraction (technical, fundamental, sentiment), labeling, train/test split, feature importance |

**Alignement livre** : Chapitres 3-4 (Data Preparation, Feature Engineering), Chapitre 8 (Sentiment Analysis)

**Objectifs** : Intégrer données alternatives, préparer datasets pour ML avec features engineering.

---

### Phase 6 : Machine Learning Traditionnel (3 notebooks, ~4h par langage)

Appliquer ML classique au trading : classification directionnelle, régression pour prédiction de prix, optimisation de portfolio ML-enhanced.

| # | Python | C# | Durée | Contenu |
|---|--------|----|----|---------|
| 19 | [QC-Py-19-ML-Supervised-Classification](Python/QC-Py-19-ML-Supervised-Classification.ipynb) | [QC-CS-19-ML-Supervised-Classification](CSharp/QC-CS-19-ML-Supervised-Classification.ipynb) | 75 min | Random Forest, XGBoost, direction prediction (up/down), walk-forward validation, ObjectStore persistence |
| 20 | [QC-Py-20-ML-Regression-Prediction](Python/QC-Py-20-ML-Regression-Prediction.ipynb) | [QC-CS-20-ML-Regression-Prediction](CSharp/QC-CS-20-ML-Regression-Prediction.ipynb) | 75 min | Linear regression, SVR, price target prediction, backtesting ML signals |
| 21 | [QC-Py-21-Portfolio-Optimization-ML](Python/QC-Py-21-Portfolio-Optimization-ML.ipynb) | [QC-CS-21-Portfolio-Optimization-ML](CSharp/QC-CS-21-Portfolio-Optimization-ML.ipynb) | 90 min | ML-enhanced Markowitz, covariance estimation via ML, risk-adjusted allocation |

**Alignement livre** : Chapitres 5-7 (Supervised Learning, Random Forests, XGBoost), Chapitre 12 (Portfolio Optimization)

**Objectifs** : Appliquer ML classique au trading, persistence modèles avec ObjectStore, validation robuste.

---

### Phase 7 : Deep Learning (3 notebooks, ~4.5h par langage)

Deep Learning pour séries temporelles : LSTM, Transformers, Autoencoders. Design CPU-first avec GPU optionnel.

| # | Python | C# | Durée | Contenu |
|---|--------|----|----|---------|
| 22 | [QC-Py-22-Deep-Learning-LSTM](Python/QC-Py-22-Deep-Learning-LSTM.ipynb) | [QC-CS-22-Deep-Learning-LSTM](CSharp/QC-CS-22-Deep-Learning-LSTM.ipynb) | 90 min | LSTM time series, TensorFlow/Keras (Python), TensorFlow.NET (C#), CPU-first, sequence prediction |
| 23 | [QC-Py-23-Attention-Transformers](Python/QC-Py-23-Attention-Transformers.ipynb) | [QC-CS-23-Attention-Transformers](CSharp/QC-CS-23-Attention-Transformers.ipynb) | 90 min | Transformer architecture, multi-head attention, temporal fusion, GPU optionnel |
| 24 | [QC-Py-24-Autoencoders-Anomaly](Python/QC-Py-24-Autoencoders-Anomaly.ipynb) | [QC-CS-24-Autoencoders-Anomaly](CSharp/QC-CS-24-Autoencoders-Anomaly.ipynb) | 75 min | Autoencoders pour détection anomalies, regime change detection, unsupervised signals |

**Alignement livre** : Chapitres 9-10 (LSTMs, Attention Mechanisms)

**Objectifs** : Maîtriser deep learning pour séries temporelles, design CPU-optimized par défaut.

---

### Phase 8 : IA Avancée et Production (3 notebooks, ~4.5h par langage)

État de l'art : Reinforcement Learning, LLM pour trading signals, déploiement production.

| # | Python | C# | Durée | Contenu |
|---|--------|----|----|---------|
| 25 | [QC-Py-25-Reinforcement-Learning](Python/QC-Py-25-Reinforcement-Learning.ipynb) | [QC-CS-25-Reinforcement-Learning](CSharp/QC-CS-25-Reinforcement-Learning.ipynb) | 90 min | PPO/DQN agents, Stable-Baselines3, Gym environment custom, reward shaping, CPU-first |
| 26 | [QC-Py-26-LLM-Trading-Signals](Python/QC-Py-26-LLM-Trading-Signals.ipynb) | [QC-CS-26-LLM-Trading-Signals](CSharp/QC-CS-26-LLM-Trading-Signals.ipynb) | 90 min | OpenAI/Anthropic API, prompt engineering pour trading, LLM+indicators hybrid, cost management |
| 27 | [QC-Py-27-Production-Deployment](Python/QC-Py-27-Production-Deployment.ipynb) | [QC-CS-27-Production-Deployment](CSharp/QC-CS-27-Production-Deployment.ipynb) | 75 min | Paper trading, live trading setup, monitoring, multi-strategy orchestration, deployment checklist |

**Alignement livre** : Chapitres 11-13 (Deep RL, Portfolio RL, LLMs for Trading), Chapitre 19 (Scaling and Deployment)

**Objectifs** : IA state-of-the-art pour trading, déploiement production, monitoring.

---

## Résumé de la Progression

**Total** : **27 notebooks × 2 langages = 54 notebooks**, ~30 heures de contenu par langage (60h total Python+C#)

**Répartition** :
- **18 notebooks non-ML** (Fondations, Universe, Asset Classes, Trading Avancé, Risk, Framework, Alternative Data) : ~18h
- **9 notebooks ML/DL/AI** (Supervised Learning, Deep Learning, RL, LLM) : ~12h

**Progression pédagogique** : Maîtriser les fondations QuantConnect **avant** d'aborder le Machine Learning.

---

## Configuration

### Variables d'Environnement (`.env`)

Copiez `.env.example` vers `.env` et configurez :

```bash
# Authentification QuantConnect Cloud (pour MCP et déploiement)
QC_API_USER_ID=your_user_id_here
QC_API_ACCESS_TOKEN=your_access_token_here

# APIs IA/ML (pour notebooks 17, 26)
OPENAI_API_KEY=sk-...              # LLM trading signals
ANTHROPIC_API_KEY=sk-ant-...       # Alternative LLM
HUGGINGFACE_TOKEN=hf_...           # Téléchargement modèles

# NewsAPI (FREE, pour notebook 17 - Sentiment Analysis)
NEWSAPI_KEY=your_newsapi_key_here  # https://newsapi.org/

# Local LEAN CLI (optionnel)
LEAN_DATA_PATH=./data
LEAN_RESULTS_PATH=./results
```

**Modèle complet** : Voir [`.env.example`](.env.example)

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

**Dépendances principales** : QuantConnect LEAN, pandas, numpy, scikit-learn, TensorFlow, PyTorch (optionnel), Stable-Baselines3, OpenAI, LangChain

Voir [`requirements.txt`](requirements.txt) pour la liste complète.

---

## Free Tier vs Paid

| Fonctionnalité | Free Tier | Paid (Team/Premium) |
|----------------|-----------|---------------------|
| **Backtesting** | ✅ Illimité (8h calcul/mois) | ✅ Illimité (plus d'heures) |
| **Paper trading** | ✅ | ✅ |
| **Données Equity/Crypto/Forex** | ✅ Depuis 2010 | ✅ Depuis 1998 |
| **Alternative data (news, sentiment)** | ❌ (workaround : NewsAPI gratuit) | ✅ TiingoNews, etc. |
| **GPU pour Deep Learning** | ❌ (CPU local ou cloud trial) | ✅ GPU cloud |
| **Live trading** | ❌ | ✅ |
| **API Cloud access** | Limité | ✅ Full |

**Workarounds Free Tier** :
- **QC-17 Sentiment** : NewsAPI gratuit (100 req/jour) au lieu de TiingoNews payant
- **QC-22/23/24 Deep Learning** : CPU-optimized (ou GPU local via Docker)
- **QC-25 RL** : CPU-first avec Stable-Baselines3
- **QC-27 Production** : Paper trading (simulation gratuite)

**Sponsoring universitaire** : Le CEO Jared Broad a précédemment sponsorisé des programmes avec tier Team gratuit. Contact : [https://www.quantconnect.com/contact](https://www.quantconnect.com/contact)

---

## Alignement avec "Hands-On AI Trading"

Cette série s'inspire du livre **"Hands-On AI Trading with Python, QuantConnect, and AWS"** (Janvier 2025, Wiley).

**Auteurs** : Jiri Pik, Ernest Chan, **Jared Broad** (CEO QuantConnect), et al.

| Notebooks CoursIA | Chapitres Livre |
|-------------------|-----------------|
| QC-16 | Ch 3-4 : Data Preparation, Feature Engineering |
| QC-17 | Ch 8 : Sentiment Analysis with Transformers |
| QC-18 | Ch 4 : Feature Engineering for ML |
| QC-19 | Ch 5-7 : Supervised Learning, Random Forests, XGBoost |
| QC-20 | Ch 6 : Regression Models |
| QC-21 | Ch 12 : Portfolio Optimization (adapté avec ML) |
| QC-22 | Ch 9 : LSTMs for Time Series |
| QC-23 | Ch 10 : Attention Mechanisms and Transformers |
| QC-24 | Ch 9 : Autoencoders (adapté pour anomaly detection) |
| QC-25 | Ch 11-12 : Deep Reinforcement Learning, Portfolio RL |
| QC-26 | Ch 13 : LLMs for Trading Signals |
| QC-27 | Ch 19 : Scaling and Deployment |

**Lien livre** : [Amazon](https://www.amazon.com/dp/1394268432) | [Site officiel](https://www.hands-on-ai-trading.com) | [GitHub du livre](https://github.com/QuantConnect/HandsOnAITradingBook)

---

## Intégration MCP QuantConnect

QuantConnect a lancé un [serveur MCP officiel](https://github.com/QuantConnect/mcp-server) en 2026 avec **60+ API endpoints**.

### Capacités MCP

- **Gestion projets** : Créer, lire, modifier, supprimer projets
- **Backtesting** : Lancer backtests, analyser résultats, lire charts/orders/insights
- **Live trading** : Déployer, monitorer, liquider algorithmes
- **Compilation** : Compiler algorithmes en cloud

### Configuration Claude Code

Dans `~/.claude.json` :

```json
{
  "mcpServers": {
    "quantconnect": {
      "command": "docker",
      "args": ["run", "-i", "--rm",
               "-e", "QC_USER_ID=${QC_API_USER_ID}",
               "-e", "QC_API_TOKEN=${QC_API_ACCESS_TOKEN}",
               "quantconnect/mcp-server:latest"],
      "env": {
        "QC_API_USER_ID": "your_user_id",
        "QC_API_ACCESS_TOKEN": "your_token"
      }
    }
  }
}
```

**Prérequis** : Claude Pro ($20/mois) + Compte QuantConnect

**Cas d'usage** :
- Créer projets QuantConnect depuis Claude Code
- Lancer backtests et récupérer résultats via chat
- Déployer algorithmes en paper/live trading
- Analyser performance via conversation

### MCP Jupyter (Alternative)

Pour itération locale sur notebooks de recherche : `mcps\internal\servers\jupyter-papermill-mcp-server` (CoursIA)

---

## Bibliothèques Partagées

### Python (`shared/`)

- **`features.py`** : Feature engineering (returns multi-period, technical features, labeling, walk-forward split)
- **`indicators.py`** : Custom indicators QuantConnect
- **`ml_utils.py`** : ML training, persistence (ObjectStore), métriques
- **`plotting.py`** : Visualisations standardisées (backtest results, feature importance, confusion matrix)
- **`backtest_helpers.py`** : Helpers configuration backtests

**Usage** :
```python
from shared.features import calculate_returns, add_technical_features
from shared.ml_utils import train_classifier, save_to_objectstore
from shared.plotting import plot_backtest_results
```

### C# (`SharedLib/`)

- **`Features.cs`** : Feature engineering (Accord.NET DataFrame)
- **`CustomIndicators.cs`** : Indicateurs personnalisés
- **`MLHelpers.cs`** : ML training (Accord.NET), persistence
- **`BacktestHelpers.cs`** : Configuration backtests

**Usage** :
```csharp
using CoursIA.QuantConnect.SharedLib;
var returns = FeatureEngineering.CalculateReturns(prices, new[] {1, 5, 20});
var model = MLHelpers.TrainClassifier(X, y);
```

---

## Scripts et Validation

### Scripts Disponibles

| Script | Description |
|--------|-------------|
| `scripts/validate_qc_notebooks.py` | Validation structure notebooks (Python + C#) |
| `scripts/test_algorithms.py` | Automated backtest runner (via MCP ou LEAN CLI) |
| `scripts/sync_to_cloud.py` | Upload vers QuantConnect cloud |

**Validation structure** :
```bash
python scripts/validate_qc_notebooks.py MyIA.AI.Notebooks/QuantConnect/Python --quick
python scripts/validate_qc_notebooks.py MyIA.AI.Notebooks/QuantConnect --all --fix
```

**Test algorithmes** :
```bash
# Test single algorithm
python scripts/test_algorithms.py --algorithm MovingAverageCrossover.py \
  --start 2020-01-01 --end 2023-12-31 --language python

# Test all Python algorithms
python scripts/test_algorithms.py --language python --all --report output/report.html
```

---

## Troubleshooting

### Cloud QuantConnect

**Problème** : "Backtest timed out"
**Solution** : Réduire date range ou résolution (Daily au lieu de Minute)

**Problème** : "Data not available"
**Solution** : Vérifier que l'asset est dans free tier (Equity US, Crypto, Forex OK)

**Problème** : "Out of compute hours"
**Solution** : Free tier = 8h/mois. Attendre reset mensuel ou optimiser algorithme

### Local LEAN CLI

**Problème** : "Docker container won't start"
**Solution** : Vérifier Docker Desktop running, volumes avec paths absolus

**Problème** : "Market data not found"
**Solution** : Télécharger données avec `lean data download --dataset us-equity`

**Problème** : "GPU not detected"
**Solution** : Installer nvidia-docker, vérifier `--gpus all` dans docker-compose

Pour plus de détails : [TROUBLESHOOTING.md](TROUBLESHOOTING.md) (à venir)

---

## Parcours Pédagogiques Recommandés

### Débutant (20h)

1. **Phase 1** : Fondations LEAN (4.5h)
2. **Phase 2** : Universe et Asset Classes (5h)
3. **Phase 3** : Trading Avancé et Risk (5.5h)
4. **Notebooks 13-15** : Algorithm Framework (4h)
5. Premier projet : Stratégie momentum avec risk management

### Intermédiaire (40h)

1. Révision Débutant (optionnel, 4h)
2. **Phase 4-5** : Algorithm Framework + Alternative Data (8h)
3. **Phase 6** : Machine Learning Traditionnel (4h)
4. Notebooks 19-21 en profondeur
5. Projet : Stratégie ML multi-actifs avec optimisation

### Expert (60h)

1. Révision Intermédiaire (optionnel, 8h)
2. **Phases 6-8** complètes : ML + DL + IA Avancée (12h)
3. Deep dive LSTMs, Transformers, RL
4. Notebook 26 : LLM trading signals
5. Notebook 27 : Déploiement production
6. Projet final : Stratégie RL avec LLM-augmented signals, déploiement paper trading

---

## Ressources Complémentaires

### Documentation QuantConnect

- [Documentation officielle](https://www.quantconnect.com/docs)
- [LEAN Engine GitHub](https://github.com/QuantConnect/Lean)
- [LEAN CLI Documentation](https://www.quantconnect.com/docs/v2/lean-cli)
- [Algorithm Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework/overview)

### MCP & Intégrations

- [QuantConnect MCP Server](https://github.com/QuantConnect/mcp-server)
- [MCP Announcement](https://www.quantconnect.com/announcements/19439/quantconnect-mcp-server/)
- [PulseMCP - QuantConnect](https://www.pulsemcp.com/servers/quantconnect)

### Livre & Ressources IA Trading

- [Hands-On AI Trading Book](https://www.hands-on-ai-trading.com)
- [Book GitHub Repository](https://github.com/QuantConnect/HandsOnAITradingBook)
- [Amazon (livre)](https://www.amazon.com/dp/1394268432)

### Communauté

- [QuantConnect Forum](https://www.quantconnect.com/forum)
- [LEAN Discussions](https://github.com/QuantConnect/Lean/discussions)
- [CoursIA Main README](../../README.md)

---

## Note Pédagogique - Sponsoring Jared Broad

Le CEO de QuantConnect, **Jared Broad**, a précédemment sponsorisé cette formation avec :
- Masterclass en direct pour la promotion
- Tier Team gratuit (alternative data, live trading, GPU)
- Accès à la League universitaire QuantConnect

**Pour demander un sponsoring** : [https://www.quantconnect.com/contact](https://www.quantconnect.com/contact)

**Historique** : Programme sponsorisé en 2024-2025, participation League universitaire non complétée.

**Objectif 2026** : Relancer contact pour nouveau sponsoring + participation active League.

---

## Résultats Attendus

Après completion de cette série, vous maîtriserez :

### Compétences Techniques

- ✅ **QuantConnect LEAN** : Architecture, lifecycle, Universe selection, multi-asset trading
- ✅ **Risk Management** : Position sizing, stop-loss, take-profit, portfolio heat
- ✅ **Algorithm Framework** : Alpha, Portfolio Construction, Execution, Risk models
- ✅ **Alternative Data** : News, sentiment, fundamentals, custom data sources
- ✅ **Machine Learning** : Supervised (RF, XGBoost), Deep Learning (LSTM, Transformers), RL (PPO, DQN)
- ✅ **LLM Integration** : Prompt engineering, LLM-augmented signals, cost management
- ✅ **Production Deployment** : Paper trading, live trading, monitoring, orchestration

### Projets Réalisables

- 🎯 **Stratégie momentum multi-actifs** avec risk management professionnel
- 🤖 **Bot ML directionnel** avec Random Forest + XGBoost
- 🧠 **Stratégie LSTM** pour prédiction prix court-terme
- 🏆 **Agent RL adaptatif** avec environnement custom
- 💡 **LLM-augmented strategy** combinant GPT-4 + indicateurs techniques
- 🏭 **Déploiement production** en paper trading avec monitoring

---

## Prochaines Étapes

1. **Démarrage rapide** : [GETTING-STARTED.md](GETTING-STARTED.md)
2. **Configuration** : Copier `.env.example` vers `.env` et remplir vos API keys
3. **Premier notebook** : [QC-Py-01-Setup.ipynb](Python/QC-Py-01-Setup.ipynb) ou [QC-CS-01-Setup.ipynb](CSharp/QC-CS-01-Setup.ipynb)
4. **Suivre la progression** : Phases 1-8 dans l'ordre
5. **(Optionnel) Configurer MCP** pour automatisation avec Claude Code

---

**Bon trading algorithmique avec QuantConnect + CoursIA !**

*Créé par CoursIA | Inspiré par "Hands-On AI Trading" (Jared Broad, 2025) | Cloud-first Architecture*
