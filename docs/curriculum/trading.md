<!--
  FICHIER GENERE — ne pas editer a la main.
  Cette page de parcours est derivee du catalogue de notebooks par
  scripts/notebook_tools/generate_parcours.py, puis regeneree chaque jour
  sur `main` par .github/workflows/catalog-cron.yml. Toute edition manuelle
  sera silencieusement ecrasee au prochain passage du cron. Pour corriger
  une derive (comptes, enumerations), corriger la SOURCE (le catalogue /
  les metadonnees de notebook) ou le generateur — jamais cette page.
  Cf .claude/rules/catalog-pr-hygiene.md (les artefacts generes
  appartiennent a l'automatisation).
-->

# Trading Algorithmique

**QuantConnect, ML appliqué et probabilités**

Stratégies de trading algorithmique avec QuantConnect, pipeline ML (Transformer, DQN, LSTM), indicateurs techniques avancés, et modèles probabilistes. Du backtesting basique au reinforcement learning.

## Statistiques

| Métrique | Valeur |
|----------|--------|
| Notebooks | 234 |
| PRODUCTION | 0 |
| BETA | 216 |
| ALPHA | 18 |

## ML/DataScienceWithAgents (51 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | 1.2 - Manipulation de Données avec NumPy | BETA | Oui |
| 2 | 1.3 - Analyse de Données avec Pandas | BETA | Oui |
| 3 | 2.1 — Le workflow d'apprentissage automatique | BETA | Oui |
| 4 | 2.10 — Optimisation d'hyperparamètres : grille, hasard,… | BETA | Non |
| 5 | 2.11 — Régularisation sparse : LASSO (L1) vs Ridge… | BETA | Oui |
| 6 | 2.12 — Données déséquilibrées : la courbe PR, les… | BETA | Oui |
| 7 | 2.13 — Analyse d'erreurs : diagnostiquer un modèle… | BETA | Oui |
| 8 | 2.2 — La descente de gradient : comment un modèle… | BETA | Oui |
| 9 | 2.3 — Régression linéaire et régression logistique | BETA | Oui |
| 10 | Naive Bayes génératif vs régression logistique… | BETA | Oui |
| 11 | Régression en grande dimension — quand p >> n : ridge,… | BETA | Oui |
| 12 | Modèle gaussien, frontière LDA / QDA | BETA | Oui |
| 13 | 2.4 — Arbres de décision, forêts aléatoires et boosting | BETA | Oui |
| 14 | 2.5 — Biais, variance, validation croisée et courbe ROC | BETA | Oui |
| 15 | 2.5b — Calibration des probabilités : reliability… | BETA | Oui |
| 16 | 2.5c — Equite par sous-groupe : compromis… | BETA | Oui |
| 17 | 2.6 — Clustering (KMeans) et réduction de dimension… | BETA | Oui |
| 18 | 2.7 — Modèles non paramétriques : SVM et k plus proches… | BETA | Oui |
| 19 | 2.8 — Théorie de l'apprentissage : PAC et dimension de… | BETA | Oui |
| 20 | 2.8c — Borne + Témoin extrémal + Concentration : ce que… | BETA | Oui |
| 21 | Novikoff : la convergence du perceptron, démontrée et… | BETA | Oui |
| 22 | 2.9 — Grokking : la généralisation qui arrive en retard | BETA | Oui |
| 23 | 3.0 — Théorie de l'information : entropie, KL,… | BETA | Oui |
| 24 | 3.1 — La rétropropagation : la chaîne des gradients à… | BETA | Oui |
| 25 | 3.2 — Les optimisateurs : de SGD à Adam, ce qui change… | BETA | Oui |
| 26 | 3.3 — Régularisation : dropout, weight decay, early… | BETA | Oui |
| 27 | 3.4 — Attention et Transformer from scratch : jusqu'au… | BETA | Oui |
| 28 | 3.5 — Grokking et double descente : quand la… | BETA | Oui |
| 29 | 3.6 — Modèles génératifs : trois objectifs, trois… | BETA | Oui |
| 30 | 3.6b — Modèles génératifs en PyTorch : VAE, GAN et… | BETA | Oui |
| 31 | 3.7 — Distillation maître-élève : quand le savoir se… | BETA | Oui |
| 32 | Représentations contrastives modernes — du skip-gram… | BETA | Oui |
| 33 | 4.1 — Le neurone convolutif from scratch : kernel… | BETA | Oui |
| 34 | 4.2 — ConvNet profonde : pourquoi les résiduelles | BETA | Non |
| 35 | Lab 1 - Les Bases de la Data Science en Python | BETA | Oui |
| 36 | Lab 2 - Analyser un Appel d'Offre avec l'IA | BETA | Non |
| 37 | Lab 3 - Pré-qualifier des Candidats avec l'IA | BETA | Non |
| 38 | Lab 4 - Le Nettoyage de Données avec Pandas | BETA | Oui |
| 39 | Lab 5 - De la Visualisation au Machine Learning | BETA | Oui |
| 40 | Lab 6 - Anatomie de votre premier Agent d'IA | ALPHA | Non |
| 41 | Lab 7 - Votre premier Agent Analyste de Données | BETA | Non |
| 42 | Lab 8: Introduction au Framework ADK et Multi-Provider | BETA | Non |
| 43 | Lab 9: Premier Agent ADK pour Data Science | BETA | Oui |
| 44 | Lab 10: Data File Analyzer (DS-STAR Component) | BETA | Oui |
| 45 | Lab 11: Planner-Coder-Verifier Loop (DS-STAR Core) | ALPHA | Oui |
| 46 | Lab 12: DS-STAR Workshop - Analyse Multi-Fichiers | BETA | Non |
| 47 | Lab 13: Web Search pour Modèles SOTA (MLE-STAR… | BETA | Oui |
| 48 | Lab 14: Ablation et Raffinement Ciblé (MLE-STAR… | ALPHA | Oui |
| 49 | Lab 15: Kaggle Challenge avec MLE-STAR | BETA | Oui |
| 50 | Lab 16: Data Science Agent avec GCP BigQuery | ALPHA | Oui |
| 51 | Lab 17: Projet Final - Pipeline DS-STAR Complet | ALPHA | Oui |

## ML/ML.Net (21 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | ML-1 (Python) : Introduction au Machine Learning avec… | BETA | Oui |
| 2 | ML-1 : Introduction au Machine Learning avec ML.NET | BETA | Oui |
| 3 | ML-2 : Préparation des données et ingénierie des… | BETA | Oui |
| 4 | ML-2 : Préparation des données et ingénierie des… | BETA | Oui |
| 5 | ML-3 : Entraînement et AutoML | BETA | Oui |
| 6 | ML-3 (Python) : Entraînement et AutoML | BETA | Oui |
| 7 | ML-4 : Évaluation des modèles (Python / sklearn) | BETA | Oui |
| 8 | ML-4 : Evaluation des modèles | BETA | Oui |
| 9 | ML-4b : Validité statistique des comparaisons de… | BETA | Oui |
| 10 | ML-5 (Python) : Prévision de séries temporelles (STL +… | BETA | Oui |
| 11 | ML-5 : Time Series Forecasting avec ML.NET | BETA | Oui |
| 12 | ML-5b (Python) : Séries temporelles classiques —… | BETA | Oui |
| 13 | ML-6 (Python) : Intégration de modèles ONNX (skl2onnx +… | BETA | Oui |
| 14 | ML-6 : ONNX Model Integration avec ML.NET | BETA | Oui |
| 15 | ML-7 (Python) : Systèmes de recommandation par… | BETA | Oui |
| 16 | ML-7 : Systèmes de Recommandation avec ML.NET | BETA | Oui |
| 17 | ML-8 (Python) : Clustering non-supervisé avec K-Means | BETA | Oui |
| 18 | ML-8 : Clustering non-supervise avec K-Means | BETA | Oui |
| 19 | ML-9 (Python) : Détection d'anomalies par PCA (erreur… | BETA | Oui |
| 20 | ML-9 : Detection d'anomalies avec Randomized PCA | BETA | Oui |
| 21 | TP : Prevision des ventes d'assurance | BETA | Oui |

## Probas (2 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Infer-101 : Introduction a Infer.NET | BETA | Oui |
| 2 | Le Framework Rational Speech Act (RSA) | BETA | Oui |

## Probas/DecisionTheory (25 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Du graphe causal au do-calculus — le pont entre les… | BETA | Oui |
| 2 | DoWhy-1 — Exiger un estimand : l'identification causale… | BETA | Oui |
| 3 | Méthodes quasi-expérimentales — identifier l'effet… | BETA | Oui |
| 4 | DecInfer-01-Utility-Foundations : Axiomes et Fondements | BETA | Oui |
| 5 | DecInfer-02-Théorème de représentation de von… | BETA | Oui |
| 6 | DecInfer-03-Utility-Money : Utilite de l'Argent et… | BETA | Oui |
| 7 | DecInfer-04-Multi-Attribute : Utilite Multi-Attributs | BETA | Oui |
| 8 | DecInfer-05-Decision-Networks : Reseaux de Decision | BETA | Oui |
| 9 | DecInfer-06-Value-Information : Valeur de l'Information | BETA | Oui |
| 10 | DecInfer-07-Expert-Systems : Decisions Robustes et… | BETA | Oui |
| 11 | DecInfer-08-Sequential : MDPs, Bandits et POMDPs | BETA | Oui |
| 12 | DecInfer-09-Preuves formelles — Indice de Gittins | BETA | Oui |
| 13 | DecInfer-10-Thompson-Sampling : Bandits bayesiens par… | BETA | Oui |
| 14 | DecPyMC-1-Utility-Foundations : Axiomes et Fondements | BETA | Oui |
| 15 | DecPyMC-10 : Ruine et capital — le processus de… | BETA | Oui |
| 16 | DecPyMC-11 — Valeur de l'Information en Souscription | BETA | Oui |
| 17 | DecPyMC-12 — Fréquence × sévérité hiérarchique : le… | BETA | Oui |
| 18 | DecPyMC-2-Utility-Money : Utilite de l'Argent et… | BETA | Oui |
| 19 | DecPyMC-3-Multi-Attribute : Utilite Multi-Attributs | BETA | Oui |
| 20 | DecPyMC-4-Decision-Networks : Reseaux de Decision | BETA | Oui |
| 21 | DecPyMC-5-Valeur de l'Information | BETA | Oui |
| 22 | DecPyMC-6-Systèmes Experts et Decisions Robustes | BETA | Oui |
| 23 | DecPyMC-7-MDPs, Bandits et POMDPs | BETA | Oui |
| 24 | DecPyMC-8 — Crédibilité actuarielle de Bühlmann–Straub… | BETA | Oui |
| 25 | DecPyMC-9 : Du risque à la prime — prime pure,… | BETA | Oui |

## Probas/Infer (20 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Infer-1-Setup : Introduction et Installation | BETA | Oui |
| 2 | Infer-10-Model-Sélection : Sélection et Comparaison de… | BETA | Oui |
| 3 | Infer-11-Topic-Models : Latent Dirichlet Allocation… | BETA | Oui |
| 4 | 12. Modèles Hiérarchiques Bayésiens — Pooling Partiel… | BETA | Oui |
| 5 | Infer-13-Crowdsourcing : Agregation de Labels et… | BETA | Oui |
| 6 | Infer-14-Sequences : Hidden Markov Models et Series… | BETA | Oui |
| 7 | Infer-15-Recommenders : systèmes de Recommandation | BETA | Oui |
| 8 | Infer-16-Sparse-Gaussian-Process : Processus Gaussiens… | BETA | Oui |
| 9 | Infer-17 — Filtre de Kalman : systèmes dynamiques… | BETA | Oui |
| 10 | Infer-18 — Détection de Rupture (Change-Point) :… | BETA | Oui |
| 11 | Infer-19 — Analyse de survie / fiabilite bayesienne :… | BETA | Oui |
| 12 | Infer-2-Gaussian-Mixtures : Distributions Gaussiennes… | BETA | Oui |
| 13 | Infer-20 — Quotients, fibres et recollement : ce qui… | BETA | Oui |
| 14 | Infer-2b-Debugging-Bonnes-Pratiques : Troubleshooting… | BETA | Oui |
| 15 | Infer-3-Factor-Graphs : Graphes de Facteurs et… | BETA | Oui |
| 16 | Infer-4-Bayesian-Networks : Reseaux Bayesiens… | BETA | Oui |
| 17 | Infer-5-Causal-Inference : Inférence Causale et… | BETA | Oui |
| 18 | Infer-7-Skills-IRT : Evaluation de Competences et… | BETA | Oui |
| 19 | Infer-8-TrueSkill : Système de Classement et… | BETA | Oui |
| 20 | Infer-9-Classification : Classification Bayesienne | BETA | Oui |

## Probas/PyMC (19 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | PyMC-1 : Configuration et Premier Modèle | BETA | Oui |
| 2 | PyMC-2 : Distributions Gaussiennes et Mélanges | BETA | Oui |
| 3 | PyMC-3 : Graphes de Facteurs et Inference Discrete | BETA | Oui |
| 4 | PyMC-4 : Reseaux Bayesiens | BETA | Oui |
| 5 | PyMC-05-Causal-Inference : Inference Causale et… | BETA | Oui |
| 6 | PyMC-06-Debugging : Troubleshooting et Bonnes Pratiques | BETA | Oui |
| 7 | PyMC-7 : Modèles de Competences (IRT et DINA) | BETA | Oui |
| 8 | PyMC-8 : TrueSkill - Classement et Apprentissage en… | BETA | Oui |
| 9 | PyMC-9 : Classification Bayesienne et Tests A/B | BETA | Oui |
| 10 | PyMC-10 : Sélection de Modèles et Comparaison… | BETA | Oui |
| 11 | PyMC-11 : Modèles de Sujets (Topic Models) et LDA | BETA | Oui |
| 12 | 12. Modèles Hiérarchiques Bayesiens -- Pooling Partiel… | BETA | Oui |
| 13 | PyMC-13 : Crowdsourcing - Agregation de Labels et… | BETA | Oui |
| 14 | PyMC-14 — Modèles de Sequences et Chaînes de Markov… | BETA | Oui |
| 15 | PyMC-15-Recommenders : Systèmes de Recommandation… | BETA | Oui |
| 16 | PyMC-16 : Processus Gaussiens et frontières non… | BETA | Oui |
| 17 | 17. Filtre de Kalman : systèmes dynamiques lineaires… | BETA | Oui |
| 18 | 18. Detection de Rupture (Change-Point) : inferer le… | BETA | Oui |
| 19 | 19. Analyse de survie / fiabilite bayesienne : inferer… | BETA | Oui |

## QuantConnect/ML-Training-Pipeline (1 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | M3b - HAR Asymetrique : Decomposition Semivariance et… | BETA | Non |

## QuantConnect/Python (47 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | QC-Py-01 : Configuration et Premier Backtest… | BETA | Non |
| 2 | QC-Py-02 : QuantConnect Platform Fundamentals -… | BETA | Non |
| 3 | QC-Py-03 - Data Management in QuantConnect | BETA | Non |
| 4 | Objectifs d'Apprentissage | BETA | Non |
| 5 | Objectifs d'Apprentissage | BETA | Non |
| 6 | QC-Py-06 : Options Trading dans QuantConnect | BETA | Non |
| 7 | QC-Py-07 : Futures et Forex Trading dans QuantConnect | BETA | Non |
| 8 | QC-Py-08 - Multi-Asset Portfolio Stratégies | BETA | Non |
| 9 | QC-Py-09 : Types d'Ordres et Order Management dans… | BETA | Non |
| 10 | Objectifs d'Apprentissage | BETA | Non |
| 11 | QC-Py-11 - Indicateurs Techniques dans QuantConnect | BETA | Non |
| 12 | QC-Py-12 - Backtesting et Analyse de Performance | BETA | Non |
| 13 | QC-Py-12b - Validité du backtest et signification… | BETA | Non |
| 14 | QC-Py-13 - Alpha Models et Algorithm Framework | BETA | Non |
| 15 | QC-Py-14 - Portfolio Construction et Exécution Models | BETA | Non |
| 16 | Objectifs d'Apprentissage | BETA | Non |
| 17 | QC-Py-16 - Alternative Data dans QuantConnect | BETA | Non |
| 18 | Objectifs d'Apprentissage | BETA | Non |
| 19 | QC-Py-18 - Feature Engineering pour Machine Learning… | ALPHA | Non |
| 20 | Objectifs d'Apprentissage | BETA | Non |
| 21 | Objectifs d'Apprentissage | BETA | Non |
| 22 | QC-Py-21 - Portfolio Optimization avec Machine Learning | BETA | Non |
| 23 | Objectifs d'Apprentissage | BETA | Non |
| 24 | Objectifs d'Apprentissage | BETA | Non |
| 25 | QC-Py-23b - PatchTST et iTransformer pour Prevision… | BETA | Non |
| 26 | QC-Py-24 - Modèles Génératifs pour Anomaly Detection et… | BETA | Non |
| 27 | Objectifs d'Apprentissage | BETA | Non |
| 28 | Objectifs d'Apprentissage | BETA | Non |
| 29 | QC-Py-27 - Production Deployment | BETA | Non |
| 30 | QC-Py-28 - Market Regime Detection | BETA | Non |
| 31 | QC-Py-30 - LSTM Training Multi-Asset (GPU) | BETA | Non |
| 32 | QC-Py-31 - Transformer Encoder Multi-Asset (GPU) | ALPHA | Non |
| 33 | QC-Py-32 - Reinforcement Learning DQN pour le Trading | BETA | Non |
| 34 | QC-Py-33 - Reinforcement Learning PPO pour le Trading | BETA | Non |
| 35 | QC-Py-34 - SAC et A2C : Comparaison d'Agents RL pour le… | BETA | Non |
| 36 | QC-Py-35 - Reinforcement Learning pour la Construction… | ALPHA | Non |
| 37 | QC-Py-40 : Paper Trading Binance - Mean Reversion… | BETA | Non |
| 38 | QC-Py-41 : Paper Trading IBKR - SP500 Momentum | ALPHA | Non |
| 39 | QC-Py-Cloud-01 : Analyse de Sentiment FinBERT sur QC… | ALPHA | Non |
| 40 | QC-Py-Cloud-02 : Classification de Texte et Sentiment… | ALPHA | Non |
| 41 | QC-Py-Cloud-03 — Dual Momentum : Asset Sélection… | BETA | Non |
| 42 | QC-Py-Cloud-03 : Parite de Risque (Risk Parity) | BETA | Non |
| 43 | QC-Py-Cloud-05 : Prevision par Reseau de Neurones (MLP) | ALPHA | Non |
| 44 | Value Factor Z-Score — Sélection multi-facteurs… | BETA | Non |
| 45 | Option Wheel — Le paradoxe du win-rate eleve | BETA | Non |
| 46 | QC-Py-Cloud-10 : Reinforcement Learning - DQN Trading | ALPHA | Non |
| 47 | Workflow : Téléchargement et gestion des datasets | ALPHA | Non |

## QuantConnect/kelly_lean (2 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Le critere de Kelly — compagnon Python du lake… | BETA | Non |
| 2 | Kelly — compagnon natif (kernel Lean 4) | BETA | Non |

## QuantConnect/projects (46 notebooks)

| # | Notebook | Maturité | Exécutable |
|---|----------|----------|------------|
| 1 | Research QuantBook: Adaptive Asset Allocation | BETA | Non |
| 2 | Research QuantBook: All-Weather Portfolio | BETA | Non |
| 3 | Alpha Correlation Analysis | BETA | Non |
| 4 | Research QuantBook: BTC ML Enhanced | BETA | Non |
| 5 | Research QuantBook: Multi-Channel ZigZag Crypto | BETA | Non |
| 6 | Research QuantBook: Deep Learning LSTM pour SPY | BETA | Non |
| 7 | Research QuantBook: DualMomentum (Antonacci) | BETA | Non |
| 8 | Research QuantBook: Dual Momentum No TLT | BETA | Non |
| 9 | Research QuantBook: EMA-Cross Alpha Model | BETA | Non |
| 10 | Research QuantBook: EMA Cross Equity | BETA | Non |
| 11 | Research QuantBook: EMA Crossover SPY Index | BETA | Non |
| 12 | Research QuantBook: Multi-Stock EMA Crossover | BETA | Non |
| 13 | Research QuantBook: ETF Pairs Trading | BETA | Non |
| 14 | Research QuantBook: Fama-French Factor ETF Rotation | BETA | Non |
| 15 | Research QuantBook: ForexCarry (G10 FX Momentum) | BETA | Non |
| 16 | Research QuantBook: Framework Composite EMA-Trend | BETA | Non |
| 17 | Research QuantBook: Framework Composite FamaFrench +… | BETA | Non |
| 18 | Research QuantBook: Framework Composite Momentum +… | BETA | Non |
| 19 | Framework Composite TrendWeather - Research | BETA | Non |
| 20 | Research QuantBook: FuturesTrend (Donchian Breakout) | BETA | Non |
| 21 | Research QuantBook: ML Classification (RandomForest) | BETA | Non |
| 22 | ML Deep Learning - LSTM/GRU pour Trading | ALPHA | Non |
| 23 | Research QuantBook: ML-Enhanced Pairs Trading | BETA | Non |
| 24 | Research QuantBook: ML Ensemble | BETA | Non |
| 25 | Research QuantBook: ML Feature Engineering | BETA | Non |
| 26 | ML Random Forest - Classification pour Trading | ALPHA | Non |
| 27 | Research QuantBook: ML Regression | BETA | Non |
| 28 | ML SVM - Support Vector Machine pour Trading | ALPHA | Non |
| 29 | ML Text Classification for Trading | ALPHA | Non |
| 30 | ML XGBoost - Gradient Boosting pour Trading | BETA | Non |
| 31 | Research QuantBook: Mean Reversion (Sector ETFs) | BETA | Non |
| 32 | Research QuantBook: MomentumStrategy (Sector ETF… | BETA | Non |
| 33 | Research QuantBook: Equity Multi-Layer EMA + ML Filters | BETA | Non |
| 34 | Research QuantBook: Option Wheel Strategy | BETA | Non |
| 35 | Research QuantBook: Options Wheel Tech Stocks | BETA | Non |
| 36 | Research QuantBook: Covered Call Strategy | BETA | Non |
| 37 | Research QuantBook: PairsTrading (Statistical… | BETA | Non |
| 38 | Research QuantBook: RL Portfolio Allocation | BETA | Non |
| 39 | Research QuantBook: RegimeSwitching Alpha Model | BETA | Non |
| 40 | Research QuantBook: RiskParity (Inverse-Volatility… | BETA | Non |
| 41 | Research QuantBook: Sector-Momentum (Dual Momentum) | BETA | Non |
| 42 | Research QuantBook: Trend Following Competition | BETA | Non |
| 43 | Research QuantBook: TrendStocks Alpha Model | BETA | Non |
| 44 | Research QuantBook: TurnOfMonth (Calendar Anomaly) | BETA | Non |
| 45 | Research QuantBook: VIX-TermStructure (Short Volatility… | BETA | Non |
| 46 | Top-4 Sharpe > 0.5 Stratégies: OOS Deep-Dive (Issue… | BETA | Non |
