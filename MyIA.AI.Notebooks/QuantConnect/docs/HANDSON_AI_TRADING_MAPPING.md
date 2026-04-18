# Mapping: Hands-On AI Trading (2025) → CoursIA QuantConnect Series

**Livre** : "Hands-On AI Trading with Python, QuantConnect, and AWS" (2025) par Jared Broad (CEO QuantConnect)
**Repo GitHub** : https://github.com/QuantConnect/HandsOnAITradingBook
**Série** : CoursIA QuantConnect AI Trading (27 notebooks Python, C# planifié)
**Objectif** : Aider les étudiants à faire le lien entre le livre et nos notebooks

---

## Structure du livre (vraie structure)

Basé sur le contenu réel du repo GitHub `QuantConnect/HandsOnAITradingBook` :

| Section | Dossier Livre | Contenu | Notebooks CoursIA |
|---------|---------------|---------|-------------------|
| **Libraries** | 00 Libraries | backtestlib, tearsheet | QC-Py-12, QC-Py-14 |
| **Dataset Prep** | 04 Step 2 - Dataset Preparation | EDA, missing data, outliers, feature engineering, normalization (10 scripts) | QC-Py-03, QC-Py-18 |
| **Model Choice** | 05 Step 3 - Model Choice, Training, and Application | Linear/Polynomial/Lasso/Ridge Regression, Markov Switching, Decision Tree, SVM, Grid Search, Random Forest, Logistic Regression (10 scripts) | QC-Py-19, QC-Py-20 |
| **Applied ML** | 06 Applied Machine Learning | Trend scanning, regime detection, classification, HMM, SVM wavelet, dividend harvesting, stoploss, pairs selection, clustering, volatility rank, trading costs, PCA stat-arb, temporal CNN, Gaussian classifier, LLM, CNN patterns, Chronos, FinBERT (19+ exemples) | QC-Py-17, QC-Py-22, QC-Py-23, QC-Py-25, QC-Py-26 |
| **RL** | 07 Better Hedging with Reinforcement Learning | RL for hedging options | QC-Py-25 |
| **Risk Mgmt** | 08 AI for Risk Management and Optimization | Conditional portfolio optimization, corrective AI | QC-Py-10, QC-Py-21 |

---

## Mapping Détaillé

### 00 Libraries

| Concept Livre | Notebook CoursIA | Statut |
|----------------|------------------|--------|
| backtestlib (utilitaires backtest) | QC-Py-12-Backtesting-Analysis | ✅ |
| tearsheet (rapports performance) | QC-Py-14-Portfolio-Construction-Execution | ✅ |

### 04 Step 2 - Dataset Preparation

| Script Livre | Concept | Notebook CoursIA | Statut |
|--------------|---------|------------------|--------|
| 01 ExploratoryDataAnalysis.py | Analyse exploratoire | QC-Py-03-Data-Management | ✅ |
| 02-03 IdentifyingMissingData.py | Données manquantes | QC-Py-03-Data-Management | ✅ |
| 04-08 Outliers (BoxPlot, ZScore, IQR, Removing, Transforming, CappingFlooring) | Détection et traitement des outliers | QC-Py-18-ML-Features-Engineering | ✅ |
| 09 FeatureEngineering.py | Feature engineering | QC-Py-18-ML-Features-Engineering | ✅ |
| 10 Normalization.py | Normalisation | QC-Py-18-ML-Features-Engineering | ✅ |

### 05 Step 3 - Model Choice, Training, and Application

| Script Livre | Concept | Notebook CoursIA | Statut |
|--------------|---------|------------------|--------|
| 01-04 Linear/Polynomial/Lasso/Ridge Regression | Régression linéaire et régularisée | QC-Py-20-ML-Regression-Prediction | ✅ |
| 05 MarkovSwitchingDynamicRegression.py | Modèles de Markov | QC-Py-25-Reinforcement-Learning | ⚠️ Similaire |
| 06 DecisionTreeRegression.py | Arbres de décision | QC-Py-19-ML-Supervised-Classification | ✅ |
| 07-08 SupportVectorMachines + GridSearch | SVM et optimisation | QC-Py-19-ML-Supervised-Classification | ✅ |
| 09 MulticlassRandomForestModel.py | Random Forest multiclasse | QC-Py-19-ML-Supervised-Classification | ✅ |
| 10 LogisticRegression.py | Régression logistique | QC-Py-19-ML-Supervised-Classification | ✅ |

### 06 Applied Machine Learning (19+ exemples)

| Exemple Livre | Concept | Notebook CoursIA | Statut |
|---------------|---------|------------------|--------|
| 01 ML Trend Scanning with MLFinlab | Trend scanning ML | QC-Py-11-Technical-Indicators | ⚠️ Partiel |
| 02 Factor Preprocessing for Regime Detection | Régimes de marché | QC-Py-25-Reinforcement-Learning, ESGF-2026/examples/Markov-Regime-Detection | ✅ **NEW** |
| 03 Reversion vs Trending by Classification | Classification momentum/mean reversion | QC-Py-19-ML-Supervised-Classification | ✅ |
| 04 Alpha by Hidden Markov Models | HMM pour régimes | QC-Py-25-Reinforcement-Learning, ESGF-2026/examples/Markov-Regime-Detection | ✅ **NEW** |
| 05 FX SVM Wavelet Forecasting | SVM + Wavelet decomposition, QC-Py-22-Deep-Learning-LSTM, ⚠️ Approche différente |
| 06 Dividend Harvesting Selection | Sélection dividendes | QC-Py-08-Multi-Asset-Strategies, [Dividend-Harvesting-ML](../projects/Dividend-Harvesting-ML/) | ✅ **NEW** |
| 07 Effect of Positive-Negative Splits | Stock splits | QC-Py-05-Universe-Selection | ⚠️ Concept lié |
| 08 Stoploss based on Volatility/Drawdown | Stoploss dynamique | QC-Py-10-Risk-Portfolio-Management, [Stoploss-Volatility-ML](../projects/Stoploss-Volatility-ML/) | ✅ **NEW** |
| 09 ML Trading Pairs Selection | Pairs trading ML | QC-Py-13-Alpha-Models | ✅ |
| 10 Stock Selection by Clustering | Clustering fundamental data | QC-Py-19-ML-Supervised-Classification | ✅ |
| 11 Inverse Volatility Rank and Allocate | Volatilité inverse | QC-Py-10-Risk-Portfolio-Management | ✅ |
| 12 Trading Costs Optimization | Coûts de trading | QC-Py-14-Portfolio-Construction-Execution | ✅ |
| 13 PCA Statistical Arbitrage Mean Reversion | PCA stat-arb | QC-Py-13-Alpha-Models | ✅ |
| 14 Temporal CNN Prediction | CNN temporelle | QC-Py-22-Deep-Learning-LSTM | ⚠️ CNN vs LSTM |
| 15 Gaussian Classifier for Direction Prediction | Gaussian Naive Bayes | QC-Py-19-ML-Supervised-Classification, ESGF-2026/examples/Gaussian-Direction-Classifier | ✅ **NEW** |
| 16 LLM Summarization of Tiingo News | LLM pour sentiment news | QC-Py-26-LLM-Trading-Signals | ✅ |
| 17 Head Shoulders Pattern Matching with CNN | CNN pour patterns | QC-Py-22-Deep-Learning-LSTM | ⚠️ CNN vs LSTM |
| 18 Amazon Chronos Model | Chronos (prévision) | QC-Py-22-Deep-Learning-LSTM | ⚠️ Modèles différents |
| 19 FinBERT Model | FinBERT sentiment | QC-Py-26-LLM-Trading-Signals | ✅ |

### 07 Better Hedging with Reinforcement Learning

| Exemple Livre | Concept | Notebook CoursIA | Statut |
|---------------|---------|------------------|--------|
| 01 Reinforcement Learning of Hedging Options | RL pour hedging | QC-Py-25-Reinforcement-Learning | ✅ |

### 08 AI for Risk Management and Optimization

| Exemple Livre | Concept | Notebook CoursIA | Statut |
|---------------|---------|------------------|--------|
| 01 Conditional Portfolio Optimization Applied | Portfolio optimisation | QC-Py-21-Portfolio-Optimization-ML | ✅ |
| 02 Application of Corrective Artificial Intelligence | AI corrective | QC-Py-27-Production-Deployment | ⚠️ Concept lié |

---

## Mapping des Projets CoursIA

Le livre se concentre sur ML/AI appliqué au trading. Voici les projets CoursIA qui correspondent :

| Projet CoursIA | Concepts Livre | Statut |
|----------------|----------------|--------|
| [EMA-Cross-Alpha](../projects/EMA-Cross-Alpha/) | EMA crossover (base ML) | ✅ |
| [DualMomentum](../projects/DualMomentum/) | Momentum (trend scanning) | ✅ |
| [MeanReversion](../projects/MeanReversion/) | Mean reversion (classification) | ✅ |
| [AllWeather](../projects/AllWeather/) | Portfolio optimisation | ✅ |
| [ETF-Pairs-Trading](../ESGF-2026/examples/ETF-Pairs-Trading/) | Pairs trading (PCA stat-arb) | ✅ |
| [Sector-Momentum](../ESGF-2026/examples/Sector-Momentum/) | Momentum sectoriel | ✅ |
| [Markov-Regime-Detection](../ESGF-2026/examples/Markov-Regime-Detection/) | HMM pour régimes (Ex04) | ✅ **NEW** |
| [SVM-Wavelet-Forecasting](../ESGF-2026/examples/SVM-Wavelet-Forecasting/) | SVM + Wavelet decomposition (Ex05) | ✅ **NEW** |
| [Gaussian-Direction-Classifier](../ESGF-2026/examples/Gaussian-Direction-Classifier/) | Gaussian Naive Bayes (Ex15) | ✅ **NEW** |
| [Temporal-CNN-Prediction](../projects/Temporal-CNN-Prediction/) | Temporal CNN (Ex14) | ✅ **NEW** |
| [LSTM-Forecasting](../projects/LSTM-Forecasting/) | LSTM Forecasting (Ex07) | ✅ **NEW** |
| [Reinforcement-Learning-Trading](../projects/Reinforcement-Learning-Trading/) | DQN Trading (Ex08) | ✅ **NEW** |
| [Chronos-Foundation-Forecasting](../projects/Chronos-Foundation-Forecasting/) | Chronos Foundation Model (Ex18) | ✅ **NEW** |
| [Stoploss-Volatility-ML](../projects/Stoploss-Volatility-ML/) | Lasso stop-loss with SPY vol proxy (Ex08) | ✅ **NEW** |
| [Dividend-Harvesting-ML](../projects/Dividend-Harvesting-ML/) | DecisionTree dividend yield prediction (Ex06) | ✅ **NEW** |

---

## Note aux Étudiants

**Comment utiliser ce mapping** :

1. **Lisez d'abord le chapitre/exemple du livre** pour comprendre les concepts théoriques
2. **Exécutez le notebook CoursIA correspondant** pour voir la pratique en Python
3. **Adaptez l'exemple** dans vos propres projets sur QuantConnect Cloud

**Conventions CoursIA** vs Livre :

| Concept | Livre | CoursIA |
|---------|-------|---------|
| Langage principal | Python | Python (C# planifié) |
| Exécution | QC Cloud + LEAN CLI | QC Cloud + QuantBook local |
| Approche | ML/AI focus | Trading complet (fondations → AI) |
| Données | Dataset QC (spécifiques) | Données standards QC |

---

## Différences Clés

Le livre "Hands-On AI Trading" se concentre sur **l'application de ML/AI au trading** avec des exemples avancés (CNN, LLM, RL). La série CoursIA couvre **tout le spectrum du trading algorithmique** :

- **Notebooks 01-15** : Fondations QC, indicateurs, backtesting, Alpha Framework (non couverts par le livre)
- **Notebooks 16-27** : ML/AI appliqué (correspond aux sections 04-08 du livre)

Les étudiants ESGF doivent d'abord maîtriser les fondations (01-15) avant de passer aux exemples ML/AI du livre.

---

## Ressources

- **Livre** : [Hands-On AI Trading with Python, QuantConnect, and AWS](https://qnt.co/book-amazon)
- **Repo GitHub** : https://github.com/QuantConnect/HandsOnAITradingBook
- **Documentation QC** : https://www.quantconnect.com/docs

---

**Version** : 2.0 (basé sur la vraie structure du repo)
**Auteur** : CoursIA - po-2026
**Date** : 2026-03-23
**Issue** : #107
