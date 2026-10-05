# Hands-On AI Trading — inventaire des exemples du livre

Ce fichier est **l'inventaire de référence** : il rattache chaque exemple du livre *Hands-On AI Trading with Python, QuantConnect, and AWS* (Jared Broad, 2025) aux notebooks et aux projets de ce dépôt. [docs/HANDSON_AI_TRADING_MAPPING.md](docs/HANDSON_AI_TRADING_MAPPING.md) renvoie ici.

**Référence** : dépôt [QuantConnect/HandsOnAITradingBook](https://github.com/QuantConnect/HandsOnAITradingBook), commit `e025f21` (2025-12-20), dossiers `00` et `04` à `08`. Le chapitre 06 et les suivants contiennent des algorithmes LEAN complets ; les chapitres 04 et 05 contiennent des scripts autonomes sur données synthétiques.

## Comment lire les tableaux

| Statut | Sens |
|--------|------|
| `COVERED` | une ressource du dépôt implémente en code la technique de l'exemple (cellule de notebook ou `main.py`) |
| `PARTIAL` | la technique est présente, mais sur un autre problème, ou seulement pour une partie de l'exemple |
| `STUB` | un projet porte le nom de l'exemple mais ne contient pas encore de code (README seul) |
| `GAP` | aucune ressource du dépôt ne couvre l'exemple |

**Méthode (2026-10-03).** Les appels caractéristiques de chaque exemple (`Lasso(`, `GaussianHMM`, `LGBMRanker`, `MarkovRegression`…) ont été recherchés dans les cellules de code des notebooks `Python/` et dans les fichiers `.py` et `.ipynb` de `projects/` et `research/`. Le README de chaque projet a ensuite été lu pour confirmer l'exemple visé. Le statut dit si la technique est présente. Il ne dit pas si la reproduction est fidèle au livre (même univers, mêmes résultats) : cette comparaison est l'objet de [#18900](https://github.com/jsboige/CoursIA/issues/18900).

**Colonne « Statut QC ».** Elle reprend le statut du projet tel qu'il figure le 2026-10-03 dans [qc-strategies-status.md](../../docs/qc/qc-strategies-status.md). Ce fichier fait foi pour les backtests QC Cloud (Sharpe, CAGR, pire baisse, période).

Chaque ressource est un lien relatif vers un chemin qui existe sur `main`. Ce fichier est dans le périmètre de `scripts/check_docs_links.py` : un lien cassé y est détecté par la CI.

---

## 00 — Bibliothèques du livre

Outils internes du livre, sans exemple de stratégie à reproduire.

| Module | Rôle | Équivalent dans le dépôt |
|--------|------|--------------------------|
| `backtestlib` | `rough_daily_backtest()`, courbe de capital approchée | [QC-Py-12-Backtesting-Analysis](Python/QC-Py-12-Backtesting-Analysis.ipynb) (courbe de capital, pire baisse) |
| `tearsheet` | graphiques de performance | [QC-Py-12-Backtesting-Analysis](Python/QC-Py-12-Backtesting-Analysis.ipynb), [QC-Py-14-Portfolio-Construction-Execution](Python/QC-Py-14-Portfolio-Construction-Execution.ipynb) |

---

## 04 — Préparation des données (`04 Step 2 - Dataset Preparation`)

| # | Script du livre | Technique | Ressource du dépôt | Statut |
|---|-----------------|-----------|--------------------|--------|
| 01 | ExploratoryDataAnalysis | analyse exploratoire (Sweetviz) | [QC-Py-04-Research-Workflow](Python/QC-Py-04-Research-Workflow.ipynb), [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) (`describe()`, pas de Sweetviz) | PARTIAL |
| 02 | IdentifyingMissingData | détection des valeurs manquantes | [QC-Py-31-Transformer-Training](Python/QC-Py-31-Transformer-Training.ipynb) (`isna().sum()` par colonne) | COVERED |
| 03 | UsingBoxPlotToIdentifyOutliers | boîte à moustaches | [Ensemble-DLinear-TFT](projects/Ensemble-DLinear-TFT/) (compare des Sharpe, ne repère pas de valeurs aberrantes) | PARTIAL |
| 04 | UsingZScoreToIdentifyOutliers | score z | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) | COVERED |
| 05 | UsingIQRToIdentifyOutliers | écart interquartile | — | GAP |
| 06 | RemovingOutliers | filtrage des valeurs aberrantes | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) | PARTIAL |
| 07 | TransformingOutliers | transformation logarithmique | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) (logarithme de la capitalisation, sans lien explicite avec les valeurs aberrantes) | PARTIAL |
| 08 | CappingFlooringOutliers | écrêtage (winsorisation) | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) (`clip`) | COVERED |
| 09 | FeatureEngineering | moyennes mobiles, RSI, bandes de Bollinger, rendements décalés | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) | COVERED |
| 10 | Normalization | `MinMaxScaler` | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) | COVERED |
| 11 | Standardization | `StandardScaler` | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) | COVERED |
| 12 | TransformingTimeSeriesFeaturesToStationary | différenciation | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) | COVERED |
| 13 | ADFTest | test ADF, différenciation fractionnaire | [ML-EnhancedPairs](projects/ML-EnhancedPairs/) (`adfuller`, sans différenciation fractionnaire) | PARTIAL |
| 14 | Engle-GrangerTest | cointégration | [ETF-Pairs](projects/ETF-Pairs/), [ML-EnhancedPairs](projects/ML-EnhancedPairs/) (`coint`) | COVERED |
| 15 | HurstCoefficient | exposant de Hurst | [ML-Reversion-Trending](projects/ML-Reversion-Trending/) | COVERED |
| 16 | CorrelationAnalysis | corrélation de Pearson, carte de chaleur | [QC-Py-03-Data-Management](Python/QC-Py-03-Data-Management.ipynb), [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb) | COVERED |
| 17 | FeatureImportanceAnalysis | importance des variables (forêt aléatoire) | [QC-Py-18-ML-Features-Engineering](Python/QC-Py-18-ML-Features-Engineering.ipynb), [QC-Py-19-ML-Supervised-Classification](Python/QC-Py-19-ML-Supervised-Classification.ipynb) | COVERED |
| 18 | AutoIdentificationOfFeatures | élimination récursive des variables (RFE) | — | GAP |
| 19 | PCA | analyse en composantes principales | [PCA-StatArbitrage](projects/PCA-StatArbitrage/), [QC-Py-Cloud-06-PCA-StatArb](Python/QC-Py-Cloud-06-PCA-StatArb.ipynb) | COVERED |
| 20 | DataSplit | séparation apprentissage / test | [QC-Py-21-Portfolio-Optimization-ML](Python/QC-Py-21-Portfolio-Optimization-ML.ipynb) (`train_test_split`) | COVERED |
| 21 | KFoldCrossValidation | validation croisée | [QC-Py-19-ML-Supervised-Classification](Python/QC-Py-19-ML-Supervised-Classification.ipynb), [QC-Py-20-ML-Regression-Prediction](Python/QC-Py-20-ML-Regression-Prediction.ipynb) (`TimeSeriesSplit`, variante temporelle) | PARTIAL |

---

## 05 — Choix, entraînement et application du modèle (`05 Step 3 - Model Choice, Training, and Application`)

| # | Script du livre | Modèle | Ressource du dépôt | Statut |
|---|-----------------|--------|--------------------|--------|
| 01 | LinearRegression | régression linéaire | [QC-Py-20-ML-Regression-Prediction](Python/QC-Py-20-ML-Regression-Prediction.ipynb) | COVERED |
| 02 | PolynomialRegression | régression polynomiale | — | GAP |
| 03 | LassoRegression | régularisation L1 | [QC-Py-20-ML-Regression-Prediction](Python/QC-Py-20-ML-Regression-Prediction.ipynb), [Stoploss-Volatility-ML](projects/Stoploss-Volatility-ML/) | COVERED |
| 04 | RidgeRegression | régularisation L2 | [QC-Py-20-ML-Regression-Prediction](Python/QC-Py-20-ML-Regression-Prediction.ipynb), [ML-Regression](projects/ML-Regression/) | COVERED |
| 05 | MarkovSwitchingDynamicRegression | régression à changement de régime (statsmodels) | [Markov-Regime-Detection](projects/Markov-Regime-Detection/) (`MarkovRegression`) | COVERED |
| 06 | DecisionTreeRegression | arbre de régression | [Dividend-Harvesting-ML](projects/Dividend-Harvesting-ML/), [TradingCosts-Optimization](projects/TradingCosts-Optimization/) | COVERED |
| 07 | SupportVectorMachinesRegressionWithWaveletForecasting | SVR et ondelettes | [ML-FX-SVM-Wavelet](projects/ML-FX-SVM-Wavelet/), [SVM-Wavelet-Forecasting](projects/SVM-Wavelet-Forecasting/) | COVERED |
| 08 | SVRGridSearch | SVR et recherche en grille | [QC-Py-20-ML-Regression-Prediction](Python/QC-Py-20-ML-Regression-Prediction.ipynb) (`SVR`, `GridSearchCV`) | COVERED |
| 09 | MulticlassRandomForestModel | forêt aléatoire multiclasse | [QC-Py-19-ML-Supervised-Classification](Python/QC-Py-19-ML-Supervised-Classification.ipynb), [ML-RandomForest](projects/ML-RandomForest/) | COVERED |
| 10 | LogisticRegression | régression logistique | [ML-TextClassification](projects/ML-TextClassification/) (sur des titres de presse simulés, pas sur des prix) | PARTIAL |
| 11 | HiddenMarkovModels | `GaussianHMM` (hmmlearn) | [Markov-Regime-Detection](projects/Markov-Regime-Detection/), [HMM-KMeans-Voting](projects/HMM-KMeans-Voting/), [QC-Py-24-Autoencoders-Anomaly](Python/QC-Py-24-Autoencoders-Anomaly.ipynb) | COVERED |
| 12 | GaussianNaiveBayes | classifieur bayésien naïf gaussien | [ML-Gaussian-Classifier](projects/ML-Gaussian-Classifier/), [Gaussian-Direction-Classifier](projects/Gaussian-Direction-Classifier/) | COVERED |
| 13 | ConvolutionalNeuralNetworks | réseau convolutif | [ML-Temporal-CNN](projects/ML-Temporal-CNN/), [ML-HeadShoulders-CNN](projects/ML-HeadShoulders-CNN/) | COVERED |
| 14 | LGBRankerRanking | apprentissage du classement (`LGBMRanker`) | [Clustering-Fundamentals-ML](projects/Clustering-Fundamentals-ML/) | COVERED |
| 15 | OPTICSClustering | partitionnement par densité (OPTICS) | — | GAP |
| 16 | OpenAILanguageModel | modèle de langage OpenAI | [QC-Py-26-LLM-Trading-Signals](Python/QC-Py-26-LLM-Trading-Signals.ipynb), [ML-LLM-Summarization](projects/ML-LLM-Summarization/) | COVERED |
| 17 | AmazonChronosModel | Chronos (prévision de séries) | [ML-Chronos-Foundation](projects/ML-Chronos-Foundation/), [Chronos-Foundation-Forecasting](projects/Chronos-Foundation-Forecasting/) | COVERED |
| 18 | FinBERTModel | FinBERT (sentiment financier) | [QC-Py-Cloud-01-FinBERT-Sentiment](Python/QC-Py-Cloud-01-FinBERT-Sentiment.ipynb), [ML-FinBERT-Sentiment](projects/ML-FinBERT-Sentiment/) | COVERED |

---

## 06 — Apprentissage automatique appliqué (`06 Applied Machine Learning`)

Algorithmes LEAN complets sur données de marché. Les exemples 04, 08, 18 et 19 du livre ont plusieurs variantes, inventoriées séparément.

| # | Exemple du livre | Projet(s) du dépôt | Statut | Statut QC | Remarque |
|---|------------------|--------------------|--------|-----------|----------|
| 01 | ML Trend Scanning with MLFinlab | [ML-Trend-Scanning](projects/ML-Trend-Scanning/) | COVERED | Needs-improvement | étiquetage par balayage de tendance réécrit sans MLFinLab (licence payante) |
| 02 | Factor Preprocessing Techniques for Regime Detection | — | GAP | — | notebook de recherche dans le livre ; aucune reproduction |
| 03 | Reversion vs Trending - Strategy Selection by Classification | [ML-Reversion-Trending](projects/ML-Reversion-Trending/) | COVERED | Needs-improvement | classifieur `GradientBoostingClassifier` et exposant de Hurst |
| 04/01 | Alpha by Hidden Markov Models — Equities | [Markov-Regime-Detection](projects/Markov-Regime-Detection/) | COVERED | Needs-improvement | |
| 04/02 | Alpha by Hidden Markov Models — Equity Options | [Markov-Regime-Detection-Equity-Options](projects/Markov-Regime-Detection-Equity-Options/) | COVERED | Vivant (NO BEATS) | straddles SPY par régime de volatilité ; Sharpe -2,188 sur la fenêtre du livre, contre +106 % pour SPY détenu |
| 04/03 | Alpha by Hidden Markov Models — Index Options | [Markov-Regime-Detection-Index-Options](projects/Markov-Regime-Detection-Index-Options/) | COVERED | Vivant (NO BEATS) | straddles SPX par régime de volatilité ; Sharpe -1,832 sur la fenêtre du livre, contre +92 % pour SPX détenu |
| 05 | FX SVM Wavelet Forecasting | [ML-FX-SVM-Wavelet](projects/ML-FX-SVM-Wavelet/), [SVM-Wavelet-Forecasting](projects/SVM-Wavelet-Forecasting/) | COVERED | Needs-improvement / near-BROKEN (ML-FX-SVM-Wavelet) ; Vivant (SVM-Wavelet-Forecasting) | deux reproductions du même exemple |
| 06 | Dividend Harvesting Selection of High-Yield Assets | [Dividend-Harvesting-ML](projects/Dividend-Harvesting-ML/) | COVERED | Needs-improvement | |
| 07 | Effect of Positive-Negative Splits | [Positive-Negative-Splits-ML](projects/Positive-Negative-Splits-ML/) | COVERED | Edge (tranche 17) | |
| 08/01 | Stoploss — Benchmark Fixed Percentage Stop Loss | — | GAP | — | variante de référence, sans apprentissage |
| 08/02 | Stoploss — ML Placed Stop Loss | [Stoploss-Volatility-ML](projects/Stoploss-Volatility-ML/) | COVERED | Needs-improvement (tranche 17) | stop placé par régression Lasso |
| 08/03 | Stoploss — ML Put Option Hedge | [Stoploss-Put-Hedge](projects/Stoploss-Put-Hedge/) | COVERED | Vivant | couverture par put hebdomadaire, strike sous le plus bas prédit — #18960 |
| 09 | ML Trading Pairs Selection | [ML-EnhancedPairs](projects/ML-EnhancedPairs/), [ETF-Pairs](projects/ETF-Pairs/) | COVERED | Vivant (ML-EnhancedPairs) | PCA(3) + OPTICS mensuels pour grouper l'univers avant cointégration, derrière le paramètre `useClusterPairs` (mode défaut inchangé) — #18961 |
| 10 | Stock Selection through Clustering Fundamental Data | [Clustering-Fundamentals-ML](projects/Clustering-Fundamentals-ML/) | PARTIAL | Needs-improvement | la version actuelle (v4) classe les actions par z-scores de 8 facteurs fondamentaux, sans PCA ni `LGBMRanker` |
| 11 | Inverse Volatility Rank and Allocate to Future Contracts | [InverseVolatility-Rank](projects/InverseVolatility-Rank/) | COVERED | Needs-improvement / near-BROKEN | |
| 12 | Trading Costs Optimization | [TradingCosts-Optimization](projects/TradingCosts-Optimization/) | COVERED | Démo | |
| 13 | PCA Statistical Arbitrage Mean Reversion | [PCA-StatArbitrage](projects/PCA-StatArbitrage/), [QC-Py-Cloud-06-PCA-StatArb](Python/QC-Py-Cloud-06-PCA-StatArb.ipynb) | COVERED | Needs-improvement (tranche 15) | |
| 14 | Temporal CNN Prediction | [ML-Temporal-CNN](projects/ML-Temporal-CNN/), [Temporal-CNN-Prediction](projects/Temporal-CNN-Prediction/), [QC-Py-Cloud-07-TemporalCNN](Python/QC-Py-Cloud-07-TemporalCNN.ipynb) | COVERED | Needs-improvement (ML-Temporal-CNN) ; Needs-improvement, meilleur de sa cohorte (Temporal-CNN-Prediction) | `Temporal-CNN-Prediction` utilise un `MLPClassifier`, sans convolution |
| 15 | Gaussian Classifier for Direction Prediction | [ML-Gaussian-Classifier](projects/ML-Gaussian-Classifier/), [Gaussian-Direction-Classifier](projects/Gaussian-Direction-Classifier/) | COVERED | Needs-improvement (les deux) | |
| 16 | LLM Summarization of Tiingo News Articles | [ML-LLM-Summarization](projects/ML-LLM-Summarization/), [QC-Py-26-LLM-Trading-Signals](Python/QC-Py-26-LLM-Trading-Signals.ipynb) | PARTIAL | Needs-improvement (tranche 12) | sans clé d'API en paramètre du projet, `ML-LLM-Summarization` classe les articles par mots-clés, sans LLM, et l'actif est SPY, pas TSLA ; le notebook enseigne l'analyse de sentiment par LLM (réponses simulées dans ses sorties), sans résumé d'articles |
| 17 | Head Shoulders Pattern Matching with CNN | [ML-HeadShoulders-CNN](projects/ML-HeadShoulders-CNN/) | COVERED | Vivant | |
| 18/01 | Amazon Chronos Model — Base Model | [ML-Chronos-Foundation](projects/ML-Chronos-Foundation/), [Chronos-Foundation-Forecasting](projects/Chronos-Foundation-Forecasting/) | COVERED | Needs-improvement (les deux, tranche 14) | |
| 18/02 | Amazon Chronos Model — Fine-Tuned Model | — | GAP | — | aucun ré-entraînement de Chronos dans le dépôt |
| 19/01 | FinBERT Model — Base Model | [ML-FinBERT-Sentiment](projects/ML-FinBERT-Sentiment/), [QC-Py-Cloud-01-FinBERT-Sentiment](Python/QC-Py-Cloud-01-FinBERT-Sentiment.ipynb) | COVERED | Needs-improvement (tranche 12) | le portage ne produit pas de transaction sur QC Cloud : [#18903](https://github.com/jsboige/CoursIA/issues/18903) |
| 19/02 | FinBERT Model — Fine-Tuned Model | — | GAP | — | aucun ré-entraînement de FinBERT dans le dépôt |

---

## 07 — Couverture par apprentissage par renforcement (`07 Better Hedging with Reinforcement Learning`)

| # | Exemple du livre | Projet(s) du dépôt | Statut | Statut QC | Remarque |
|---|------------------|--------------------|--------|-----------|----------|
| 01 | Reinforcement Learning of Hedging Options | [RL-Options-Hedging](projects/RL-Options-Hedging/) | STUB | BROKEN (backtest QC sans code dans le dépôt) | portage suivi par [#18902](https://github.com/jsboige/CoursIA/issues/18902) |

Les projets [RL-DQN-Trading](projects/RL-DQN-Trading/) et [Reinforcement-Learning-Trading](projects/Reinforcement-Learning-Trading/), ainsi que les notebooks [QC-Py-25-Reinforcement-Learning](Python/QC-Py-25-Reinforcement-Learning.ipynb) et [QC-Py-32-RL-DQN-Trading](Python/QC-Py-32-RL-DQN-Trading.ipynb), appliquent l'apprentissage par renforcement au trading d'actions, pas à la couverture d'options. Leurs README les rattachent au chapitre 07, mais ils ne reproduisent pas cet exemple.

---

## 08 — IA pour la gestion du risque et l'optimisation (`08 AI for Risk Management and Optimization`)

| # | Exemple du livre | Projet(s) du dépôt | Statut | Statut QC | Remarque |
|---|------------------|--------------------|--------|-----------|----------|
| 01 | Conditional Portfolio Optimization Applied | [Portfolio-Optimization-ML](projects/Portfolio-Optimization-ML/), [QC-Py-21-Portfolio-Optimization-ML](Python/QC-Py-21-Portfolio-Optimization-ML.ipynb) | PARTIAL | Recherche-phase | optimisation de portefeuille sans le service PredictNow.ai du livre (API payante) |
| 02 | Application of Corrective Artificial Intelligence Applied | [Corrective-AI](projects/Corrective-AI/) | COVERED | Backteste | portage [#18901](https://github.com/jsboige/CoursIA/issues/18901) : primaire Breedon-Ranaldo + méta-étiquetage sans predictnow.ai (payant) |

---

## Résultats du livre face à nos reproductions

Cette section compare, exemple par exemple, le chiffre annoncé par le livre et celui de notre reproduction ([#18900](https://github.com/jsboige/CoursIA/issues/18900), une tranche de chapitre à la fois). Les chiffres du livre viennent de son texte et des fichiers `footnotes.txt` de son dépôt (commit `e025f21`). Les nôtres viennent de [qc-strategies-status.md](../../docs/qc/qc-strategies-status.md) et des README des projets. Tous sont des Sharpe calculés par QuantConnect, sauf mention contraire.

**Règle de verdict.** Elle a été écrite et publiée sur [#18900](https://github.com/jsboige/CoursIA/issues/18900) avant tout rejeu ([règle de base](https://github.com/jsboige/CoursIA/issues/18900#issuecomment-5968388318), [complément pour le chapitre 06](https://github.com/jsboige/CoursIA/issues/18900#issuecomment-5968451024), [complément pour la tranche 2](https://github.com/jsboige/CoursIA/issues/18900#issuecomment-5972434603), [complément pour la tranche 3](https://github.com/jsboige/CoursIA/issues/18900#issuecomment-5975932871), [complément pour la tranche 4](https://github.com/jsboige/CoursIA/issues/18900#issuecomment-5979125159)) :

- `REPRODUIT` : notre Sharpe s'écarte du Sharpe du livre d'au plus 0,25, avec le même signe. Quand le livre donne un intervalle, issu d'un balayage de paramètres, l'écart est nul à l'intérieur ; à l'extérieur, il vaut la distance à la borne la plus proche. CAGR et pire baisse ne sont jugés que si le livre les donne.
- `ÉCART` : l'écart dépasse la tolérance. Une issue fille en cherche la cause, et un écart n'est dit « expliqué » que si sa cause est mesurée.
- `NON COMPARABLE` : le texte du livre n'annonce aucun chiffre de backtest pour l'exemple.
- Si nos conditions diffèrent de celles du livre, aucun verdict n'est rendu avant un **rejeu dans les conditions du livre**. Le rejeu reprend la fenêtre et le capital du livre, son modèle de courtage par défaut (la ligne `set_brokerage_model` de notre projet est retirée) et ses paramètres publiés ; notre code reste inchangé par ailleurs. Le diff exact de chaque rejeu est donné sur l'issue.
- Borne à zéro : quand le livre ne publie qu'un signe (tous les Sharpe du balayage positifs, ou toutes les combinaisons profitables), une tolérance de 0,25 contredirait la condition « même signe ». Le test porte alors sur le signe seul : Sharpe > 0, ou `Net Profit` de QuantConnect > 0. C'est un test faible : il dit que notre reproduction ne contredit pas le livre, pas qu'elle en reproduit un chiffre.

### 06 — exemples 01 à 07 (tranche 1)

| # | Chiffre du livre | Conditions du livre | Notre chiffre | Nos conditions | Verdict |
|---|------------------|---------------------|---------------|----------------|---------|
| 01 | précision de classification 51,2 % | notebook de recherche, BTC quotidien, 2016-2024 | Sharpe 0,328, CAGR 7,1 %, pire baisse 29,4 % | algorithme LEAN, SPY, TLT et GLD, 2015-2024, `RandomForestClassifier` | `NON COMPARABLE` : une précision n'est pas un backtest |
| 02 | précisions 0,6101 / 0,5849 / 0,5882 / 0,5962 (quatre prétraitements des facteurs) | notebook de recherche, SPY quotidien, 2000-2024 | — | aucune reproduction (`GAP`) | sans objet |
| 03 | précision 0,5548 dans l'échantillon, 0,5277 hors échantillon | notebook de recherche, SPY, TLT et VIX quotidiens, 1990-2024 | Sharpe 0,571, CAGR 10,51 %, pire baisse 19,6 % (2015-2024) ; 0,495, 9,85 %, 20,7 % (2018-2025) | algorithme LEAN, cinq ETF (SPY, TLT, GLD, IWM, EFA), `GradientBoostingClassifier` et exposant de Hurst | `NON COMPARABLE` : une précision n'est pas un backtest, et notre projet ne mesure pas de précision |
| 04/01 | aucun chiffre dans le texte ; le tearsheet ne montre que des courbes (capital final d'environ 1,4 fois le départ et pire baisse proche de 35 %, lus à l'œil) | 2019-01-01 → 2024-01-01, capital 1 M, SPY et TLT en données minute, bascule complète SPY ↔ TLT à chaque changement de régime, 3 ans d'historique | Sharpe 0,375, CAGR 8,44 %, pire baisse 24,4 % | 2015 → 2026, capital 100 k, SPY, TLT et GLD en données quotidiennes, pondérations partielles revues en début de mois | `NON COMPARABLE` |
| 04/02 | — | 2019-01-01 → 2024-01-01, capital 100 k, SPY et options sur action, Interactive Brokers sur marge | Sharpe -2,188, CAGR -6,81 %, pire baisse 33,10 %, 430 ordres | rejeu du portage dans les conditions du livre (projet 37338046) | `NON COMPARABLE` : le livre ne publie pas de chiffres ; contre SPY détenu (+106 %), verdict NO BEATS |
| 04/03 | — | 2019-01-01 → 2024-01-01, capital 1 M, SPX et options d'indice, Interactive Brokers sur marge | Sharpe -1,832, CAGR -3,57 %, pire baisse 20,70 %, 470 ordres | rejeu du portage dans les conditions du livre (projet 37338052) | `NON COMPARABLE` : le livre ne publie pas de chiffres ; contre SPX détenu (+92 %), verdict NO BEATS |
| 05 | aucun chiffre dans le texte ; les tearsheets ne montrent que des courbes | 2019-01-01 → 2024-04-01, capital 1 M, EURJPY, GBPUSD, AUDCAD, NZDCHF | ML-FX-SVM-Wavelet : Sharpe 0,153, CAGR 4,29 %, pire baisse 21,2 % ; SVM-Wavelet-Forecasting : pas de mesure | ML-FX-SVM-Wavelet : 2015-2024, mêmes paires, courtage OANDA | `NON COMPARABLE` |
| 06 | Sharpe de 0,476 à 0,617 sur tout le balayage, toujours positif ; paramètres publiés : univers de 100, 5 ans d'historique | 2019-01-01 → 2024-04-01, capital 1 M, courtage par défaut | Sharpe 0,468, CAGR 12,66 %, pire baisse 30,6 % (2015-2026). **Rejeu dans les conditions du livre : Sharpe 0,638, CAGR 17,87 %, pire baisse 31,5 %, 1301 ordres** | notre mesure : 2015-01-01 → 2026-03-01, modèle de frais de nos campagnes comparatives ; rejeu : conditions du livre, paramètres publiés | `REPRODUIT` : 0,638 dépasse de 0,021 la borne haute du balayage (0,617), dans la tolérance de 0,25 |
| 07 | tous les Sharpe ≥ 0,7 sur le balayage, le meilleur à 3 jours de détention | 2019-01-01 → 2024-04-01, capital 100 k, courtage par défaut ; paramètres publiés : 4 positions au plus, 4 ans d'apprentissage | Sharpe 1,066, CAGR 41,11 %, pire baisse 34,10 % (2015-01 → 2024-04) ; 1,511, 75,72 %, 37,60 % (2018-2024). **Rejeu dans les conditions du livre : Sharpe 1,343, CAGR 65,87 %, pire baisse 37,6 %, 235 ordres** | nos deux mesures : modèle de frais de nos campagnes comparatives ; rejeu : conditions du livre, 3 jours de détention | `REPRODUIT` : 1,343 est dans l'intervalle annoncé (≥ 0,7) |

**Rejeux** (projets QuantConnect séparés, une exécution chacun) :

- 07 : projet 37295024, backtest `a7dd583491a45d77ab4a74a365573460` ; PSR 62,0 %.
- 06 : projet 37295108, backtest `009ff61bd41bc25832870bd613cbc65f` ; PSR 13,0 %. Comparé au code du livre au niveau de l'arbre syntaxique, notre `main.py` n'en diffère que par une garde (`if prediction_sum <= 0: return`, qui évite une division par zéro) et par des renommages ; le modèle est le même `DecisionTreeRegressor(random_state=0)`.

**Ce que le verdict `REPRODUIT` de l'exemple 06 dit, et ce qu'il ne dit pas.** Le rejeu tombe juste au-dessus du balayage du livre, aux paramètres que le livre publie : l'ordre de grandeur est reproduit, la position exacte dans le balayage ne l'est pas. Notre propre mesure (0,468 sur 2015-2026, avec le modèle de frais de nos campagnes) est plus basse, sans que ce rejeu permette de dire si l'écart vient de la fenêtre ou des frais : il change les deux à la fois.

**Ce que le verdict `REPRODUIT` de l'exemple 07 dit, et ce qu'il ne dit pas.** Le livre ne publie qu'un plancher : le rejeu le confirme, il ne reproduit pas un chiffre précis. Notre propre mesure sur 2015-2024 (Sharpe 1,066, PSR 34,9 %) reste plus basse que sur la fenêtre du livre : l'effet est concentré sur 2018-2024, comme l'écrit déjà le [README du projet](projects/Positive-Negative-Splits-ML/).

**Écarts internes au livre.** Le texte et le code de son dépôt ne disent pas toujours la même chose :

- 01 : le texte nomme `BTCUSD` ; le notebook charge `BTCUSDT` sur Binance.
- 03 : le texte cite 0,5548 et 0,5277 et la matrice de confusion `[592 1559]` ; le notebook du dépôt rend 0,5561 et 0,5309, et `[609 1542]`.
- 07 : le texte retient 3 jours de détention ; `footnotes.txt` publie 2 jours dans ses paramètres de backtest, tout en notant que 3 jours donnent le meilleur Sharpe. Le rejeu suit le texte. Les deux valeurs sont dans le balayage dont tous les Sharpe sont ≥ 0,7.

### 06 — exemples 08 à 13 (tranche 2)

Pour 08/02, 11 et 13, le livre ne publie qu'un signe : la règle de la borne à zéro s'applique. Les paramètres publiés de ces trois exemples sont tous dans le balayage auquel la borne se rapporte.

| # | Chiffre du livre | Conditions du livre | Notre chiffre | Nos conditions | Verdict |
|---|------------------|---------------------|---------------|----------------|---------|
| 08/01 | 17 des 20 seuils de stop battent le buy-and-hold de KO (Sharpe 0,263) ; paramètre publié : 0,95 | 2018-12-31 → 2024-04-01, capital 100 k, KO, stop fixe en pourcentage | — | aucune reproduction (`GAP`) | sans objet |
| 08/02 | les 30 combinaisons du balayage ont un Sharpe positif, 28 dépassent 0,263 ; paramètres publiés : 3 mois d'historique, écart de stop 0,01, `alpha_exponent` 4 | 2018-12-31 → 2024-04-01, capital 100 k, KO, VIX comme facteur de volatilité | Sharpe 0,291, CAGR 7,83 %, pire baisse 20,0 %. **Rejeu dans les conditions du livre : Sharpe 0,24, CAGR 6,87 %, pire baisse 20,5 %, profit net 41,8 %, 746 ordres** | code du projet : 2015-01-01 → 2026-03-01, 1 mois d'historique, modèle de frais de nos campagnes comparatives ; volatilité réalisée de SPY à la place du VIX (absent de QC Cloud) ; rejeu : conditions du livre, paramètres publiés | `REPRODUIT` (borne à zéro) : 0,24 > 0 |
| 08/03 | aucun chiffre | 2018-12-31 → 2024-04-01, capital 100 k, KO et ses puts hebdomadaires | Sharpe 0,033, CAGR 2,52 %, pire baisse 23,5 %, profit net 14,0 %, 1091 ordres, frais 8 208 $ | [Stoploss-Put-Hedge](projects/Stoploss-Put-Hedge/) : volatilité réalisée de SPY à la place du VIX (absent de QC Cloud), frais IBKR par le modèle de brokerage (le livre pose un security initializer), facteurs en listes (le livre utilise un `DataFrame`), semaine sans put admissible tenue nue et journalisée (le livre planterait sur `sorted()[-1]`) | `NON COMPARABLE` : le livre ne publie aucun chiffre pour cette variante |
| 09 | 1357 paires testées, 30 retenues ; aucun backtest | notebook de recherche | — | [ML-EnhancedPairs](projects/ML-EnhancedPairs/) : cointégration, et depuis #18961 sélection des paires par PCA(3) et OPTICS derrière le paramètre `useClusterPairs` (`COVERED`) | `NON COMPARABLE` : un décompte de paires n'est pas un backtest |
| 10 | tous les Sharpe du balayage sont ≥ 0 ; paramètres publiés : univers liquide de 100, univers final de 10, 365 jours d'historique, 5 composantes | 2018-12-31 → 2024-04-01, capital 100 k, PCA puis `LGBMRanker` | Sharpe 0,142, CAGR 3,37 %, pire baisse 65,3 % (2015-2026, mesure de la version v3, PCA et `GradientBoostingRegressor`) | la version actuelle (v4) classe par z-scores de 8 facteurs fondamentaux, sans PCA ni `LGBMRanker` | sans objet, pas de rejeu : notre projet ne met pas en œuvre le modèle du livre (ligne passée en `PARTIAL`) |
| 11 | toutes les combinaisons du balayage sont profitables ; paramètres publiés : 3 mois pour l'écart-type, 3 mois pour l'ATR, 365 jours d'apprentissage | 2018-12-31 → 2024-04-01, capital 100 M, contrats à terme de front month, `Ridge` | Sharpe 0,124, CAGR 4,13 %, pire baisse 41,0 %. **Rejeu dans les conditions du livre : Sharpe 0,124, CAGR 4,13 %, pire baisse 41,0 %, profit net 23,7 %, 532 ordres** | code du dépôt : 2015-01-01 → 2024-04-01, capital 100 M, modèle de frais de nos campagnes comparatives, trois surcouches de risque propres au projet (`weight_multiplier`, `max_position_pct`, `stop_loss_pct`) ; notre chiffre vient du projet QuantConnect 29463533, dont le code est déjà dans les conditions du livre ; rejeu : copie de ce code à l'octet près, surcouches gardées | `REPRODUIT` (borne à zéro) : profit net de 23,7 % > 0 |
| 12 | 774 ordres moins chers (42,36 %), 28 inchangés, 13 plus chers ; aucune statistique de backtest | 2023-01-01 → 2024-01-01, cryptomonnaies, démonstration d'un modèle de coûts | — | [TradingCosts-Optimization](projects/TradingCosts-Optimization/), démonstration | `NON COMPARABLE` |
| 13 | toutes les combinaisons du balayage sont profitables, Sharpe maximal à 3 composantes et 126 jours ; paramètres publiés : 3 composantes, 63 jours, seuil de z-score 1,5, univers de 100 | 2019-01-01 → 2024-04-01, capital 1 M | Sharpe 0,165, CAGR 5,34 %, pire baisse 35,9 %. **Rejeu dans les conditions du livre : Sharpe 0,211, CAGR 6,34 %, pire baisse 34,7 %, profit net 38,1 %, 1658 ordres** | code du projet : 2015-01-01 → 2024-01-01, capital 1 M, 60 jours d'historique, modèle de frais de nos campagnes comparatives ; `LinearRegression` à la place de `sm.OLS` avec constante (mêmes résidus) ; rejeu : conditions du livre, paramètres publiés | `REPRODUIT` (borne à zéro) : profit net de 38,1 % > 0 |

Nos chiffres hors rejeu viennent de [qc-strategies-status.md](../../docs/qc/qc-strategies-status.md). Pour l'exemple 13, cette page date sa mesure de 2015-2026, alors que le code du projet s'arrête au 2024-01-01. Pour l'exemple 11, notre chiffre a été mesuré sur le projet QuantConnect 29463533, dont le `main.py` diffère de celui du dépôt par deux lignes : début au 2018-12-31 au lieu du 2015-01-01, et pas de ligne `set_brokerage_model`. Ce code est celui du rejeu, à l'octet près : le rejeu redonne le même Sharpe, le même CAGR et la même pire baisse ; seul le PSR change (1,9 % sur la page de statut, 0,8 % au rejeu).

**Rejeux** (projets QuantConnect séparés, une exécution chacun) :

- 08/02 : projet 37309010, backtest `3e0d8c17982c9acc9d544fccf9260a09` ; PSR 1,7 %.
- 08/03 : projet 37363274, backtest `8a888b7e86262a8b763a07162c89f978` ; PSR 0,4 %.
- 13 : projet 37309113, backtest `a0205f4b3e052a526d3fc25de8acdc70` ; PSR 1,4 %.
- 11 : projet 37309271, backtest `a30271d032a6f4e54c2f2ed3bbb90381` ; PSR 0,8 %.

**Ce que les verdicts de la tranche 2 disent, et ce qu'ils ne disent pas.** Le livre ne publie, pour ces exemples, qu'un signe sur tout un balayage. Le rejeu confirme ce signe aux paramètres publiés ; il ne dit rien de la place du rejeu dans le balayage, ni de la qualité de la stratégie. Les PSR des rejeux (1,7 % pour 08/02, 1,4 % pour 13, 0,8 % pour 11) le rappellent : un Sharpe positif sur cinq ans n'est pas un avantage établi.

**Écarts internes au livre** (tranche 2) :

- 08/01 : le texte et `footnotes.txt` publient un stop à 0,95 ; la valeur par défaut du code est 0,99, dans la zone où le livre dit que le Sharpe s'effondre (≥ 0,985).
- 08/02 : le texte et `footnotes.txt` publient 3 mois d'historique ; la valeur par défaut du code est 1. Le rejeu suit le texte.
- 13 : le texte et `footnotes.txt` publient 63 jours ; la valeur par défaut du code est 60, hors du balayage, dont le pas est de 21 jours. Le rejeu suit le texte.

### 06 — exemples 14 à 19 (tranche 3)

Pour 14 et 15, le texte ne donne pas de Sharpe, mais le balayage de paramètres de `tearsheet2.png` porte une échelle de couleur. Elle est lue comme l'intervalle des Sharpe du balayage (normalisation par défaut de matplotlib : ses bornes sont le minimum et le maximum observés), à 0,03 près. Un rejeu à moins de 0,05 d'une borne de tolérance est dit fragile. Pour 17, le livre ne publie qu'un signe : la règle de la borne à zéro s'applique, sur le profit net (voir « Écarts internes »). Deux projets du dépôt se rattachent à 14, et deux à 15 : le rejeu porte sur celui dont le code suit celui du livre à l'arbre syntaxique (`ML-Temporal-CNN` et `ML-Gaussian-Classifier`).

| # | Chiffre du livre | Conditions du livre | Notre chiffre | Nos conditions | Verdict |
|---|------------------|---------------------|---------------|----------------|---------|
| 14 | « la plupart des combinaisons ne sont pas profitables » ; échelle du balayage : Sharpe de −0,55 à 0,20 ; paramètres publiés : 500 échantillons d'apprentissage, univers de 3 | 2018-12-31 → 2024-04-01, capital 100 k, constituants de QQQ, CNN temporel | [ML-Temporal-CNN](projects/ML-Temporal-CNN/) : Sharpe 0,161, CAGR 4,81 %, pire baisse 31,7 %. **Rejeu dans les conditions du livre : Sharpe 0,202, CAGR 6,11 %, pire baisse 44,7 %, profit net 36,6 %, 624 ordres** | code du projet : 2015-01-01 → 2024-01-01, modèle de frais de nos campagnes comparatives ; rejeu : conditions du livre, paramètres publiés | `REPRODUIT` : 0,202 est à la borne haute de l'échelle du balayage (0,20, lue à 0,03 près) et dans la tolérance [−0,80 ; 0,45] |
| 15 | « toutes les combinaisons sont profitables » ; échelle du balayage : Sharpe de 0,42 à 1,02 ; paramètres publiés : 4 jours par échantillon, 100 échantillons, univers de 10 | 2019-01-01 → 2024-04-01, capital 1 M, plus grandes capitalisations technologiques, `GaussianNB` | [ML-Gaussian-Classifier](projects/ML-Gaussian-Classifier/) : Sharpe 0,361, CAGR 12,49 %, pire baisse 47,4 %. **Rejeu dans les conditions du livre : Sharpe 0,582, CAGR 18,69 %, pire baisse 41,8 %, profit net 146,0 %, 1813 ordres** | code du projet : 2015-01-01 → 2026-01-01, capital 100 k, modèle de frais de nos campagnes comparatives ; liquidation complète quand aucune action n'est prédite en hausse ; rejeu : conditions du livre, paramètres publiés | `REPRODUIT` : 0,582 est dans l'intervalle du balayage (0,42 à 1,02) |
| 16 | Sharpe 1,695 | 2023-11-01 → 2024-03-01, capital 100 k, TSLA, résumés d'articles Tiingo par un LLM | Sharpe 0,686, CAGR 15,45 %, pire baisse 22,7 % | SPY, 2015-01-01 → 2026-01-01 ; sans clé d'API en paramètre du projet, classement des articles par mots-clés, sans LLM | sans objet, pas de rejeu : notre projet ne joue pas le modèle du livre par défaut (ligne passée en `PARTIAL`) |
| 17 | « toutes les combinaisons sont profitables » ; paramètres publiés : `max_size` 100, `step_size` 10, seuil de confiance 0,5, détention 10 jours | 2019-01-01 → 2024-04-01, capital 100 k, USDCAD, CNN chargé depuis l'Object Store | [ML-HeadShoulders-CNN](projects/ML-HeadShoulders-CNN/) : aucune mesure publiée. **Rejeu dans les conditions du livre : profit net −0,062 %, Sharpe −24,1, CAGR −0,012 %, pire baisse 0,2 %, 8 ordres** | code du projet : 2015-01-01 → 2024-01-01, courtage OANDA ; rejeu : conditions du livre, paramètres publiés ; le modèle étant absent de notre Object Store, un CNN entraîné sur des motifs synthétiques (journal : `Object Store model missing, training synthetic CNN`) | `ÉCART` : profit net négatif. L'écart porte sur le modèle de substitution, pas encore sur la stratégie : #19053 |
| 18/01 | aucun chiffre dans le texte ; courbes de prévision et table de rendements mensuels | 2019-01-01 → 2024-04-01, capital 100 k, 5 actions les plus liquides, Chronos pré-entraîné | Sharpe 0,277, CAGR 7,23 %, pire baisse 13,5 % | [ML-Chronos-Foundation](projects/ML-Chronos-Foundation/), 2015-01-01 → 2026-01-01 | `NON COMPARABLE` |
| 18/02 | — | Chronos ré-entraîné | — | aucune reproduction (`GAP`) | sans objet |
| 19/01 | idem 18/01 | 2022-01-01 → 2023-01-01, capital 100 k, 10 actions les plus liquides, FinBERT pré-entraîné | Sharpe 0,584, CAGR 22,10 %, pire baisse 43,0 % | [ML-FinBERT-Sentiment](projects/ML-FinBERT-Sentiment/), 2015-01-01 → 2026-01-01 | `NON COMPARABLE` |
| 19/02 | — | FinBERT ré-entraîné | — | aucune reproduction (`GAP`) | sans objet |

**Rejeux** (projets QuantConnect séparés, une exécution chacun) :

- 15 : projet 37323229, backtest `8df461e5fffd0f0df859d0bd41296130` ; PSR 10,1 %.
- 17 : projet 37323273, backtest `87648032844af2f195239271140bcb1f` ; PSR 0 %. Quatre figures détectées (2020-07-27, 2020-07-28, 2022-03-24, 2022-08-18), confiances de 50 à 58 %.
- 14 : projet 37323339, backtest `672faa80ccb73bdaa629b4137f388590` ; PSR 1,3 %.

**Ce que les verdicts de la tranche 3 disent, et ce qu'ils ne disent pas.** L'échelle de couleur d'un balayage est une source plus faible qu'un chiffre du texte : elle borne la stratégie sur tout le balayage, pas le paramètre publié. Pour 15, le rejeu tombe dans cette fourchette ; sa PSR (10,1 %) rappelle qu'un Sharpe de 0,58 sur cinq ans n'est pas un avantage établi. Pour 14, le rejeu tombe à la borne haute de l'échelle, avec un profit net positif, alors que le livre dit que la plupart des combinaisons ne sont pas profitables ; l'univers publié (3) n'étant pas dans le balayage, les deux ne se contredisent pas, et la PSR du rejeu (1,3 %) ne dit pas plus. Pour 17, l'`ÉCART` porte sur le modèle : le rejeu a joué le CNN de repli, entraîné sur des motifs synthétiques, et non le modèle entraîné du livre, absent de notre Object Store. Il dit que le projet, tel qu'il tourne aujourd'hui sur QC Cloud, ne retrouve pas le signe annoncé ; il ne dit encore rien de la stratégie du livre (#19053).

**Écarts internes au livre** (tranche 3) :

- 14 : l'univers publié (3) n'est pas dans le balayage, dont les valeurs sont 2, 4, …, 10. L'intervalle du balayage sert donc de fourchette pour la stratégie, pas de chiffre pour le paramètre publié.
- 17 : le texte et `footnotes.txt` disent « toutes les combinaisons sont profitables », mais l'échelle du balayage va d'environ −135 à −20 en Sharpe. Les deux ne se contredisent pas forcément : le Sharpe de QuantConnect retranche le taux sans risque, et une stratégie presque toujours hors du marché a une volatilité proche de zéro, ce qui rend son Sharpe très négatif même avec de petits gains. C'est pourquoi la borne de 17 porte sur le profit net et non sur le Sharpe.

### 07 et 08 — tous les exemples (tranche 4)

Le chapitre 07 et l'exemple 01 du chapitre 08 ne publient aucune statistique de backtest. Pour 08/02, les chiffres du livre ne viennent pas d'un backtest QuantConnect : ils sont calculés sur des données EBS que le livre ne partage pas, sans frais de transaction. Notre reproduction de 08/02 est celle de [#19052](https://github.com/jsboige/CoursIA/pull/19052), encore ouverte : les rejeux portent sur son `main.py`, figé à sa tête `1940f6c6d4`.

| # | Chiffre du livre | Conditions du livre | Notre chiffre | Nos conditions | Verdict |
|---|------------------|---------------------|---------------|----------------|---------|
| 07/01 | aucun chiffre : courbes de prix, de convergence des pertes, de décision face au delta et de richesse des portefeuilles de couverture (figures 7.3 à 7.8) | 2018-01-01 → 2024-01-01, capital 1 M, options sur TSLA, couverture en delta par un réseau ré-entraîné chaque mois | — | aucune reproduction ([RL-Options-Hedging](projects/RL-Options-Hedging/) est un `STUB`, portage suivi par [#18902](https://github.com/jsboige/CoursIA/issues/18902)) | `NON COMPARABLE` |
| 08/01 | aucune statistique de backtest ; les tables 8.4 à 8.9 portent sur d'autres portefeuilles, et leurs chiffres viennent du service PredictNow | 2020-02-01 → 2024-04-01, capital 100 k, 16 ETF, poids mensuels lus dans l'Object Store après un appel au service | aucune mesure publiée | [Portfolio-Optimization-ML](projects/Portfolio-Optimization-ML/) : 15 titres, covariance de Ledoit-Wolf, maximum de Sharpe, sans le service | `NON COMPARABLE` |
| 08/02, stratégie primaire | Sharpe 0,88, rendement annuel moyen 3,5 %, pire baisse −3,5 % | hors échantillon du 2021-10-01 au 2023-01-15, EUR/USD, données EBS, sans frais de transaction ; règle de saisonnalité intrajournalière de Breedon et Ranaldo | **R1 : Sharpe −0,976, CAGR −6,20 %, pire baisse 10,6 %, profit net −7,94 %, 1336 ordres.** **R2 : Sharpe −0,143, CAGR 0,77 %, pire baisse 5,7 %, profit net 1,00 %, 1336 ordres** | code de #19052 ([Corrective-AI](projects/Corrective-AI/)), stratégie primaire seule (`use_meta=false`), convention par défaut, EUR/USD OANDA à la minute, capital 100 k, frais du moteur nuls, fenêtre du livre ; R1 tel quel, R2 avec les ordres remplis au milieu de la fourchette | `ÉCART` : ni R1 ni R2 ne sont dans la tolérance (Sharpe de signe opposé ; CAGR de R2 à 2,7 points du livre, au-delà de 2 ; seule la pire baisse de R2 est dans la tolérance). L'écart achat-vente en explique une part mesurée, pas la totalité. Diagnostic : [#18901](https://github.com/jsboige/CoursIA/issues/18901) |
| 08/02, après Corrective AI | Sharpe 1,29, rendement annuel moyen 4,1 %, pire baisse −1,9 % | idem, après le modèle correctif du service PredictNow | — | #19052 remplace le modèle correctif du service par un méta-étiquetage | `NON COMPARABLE` : le modèle correctif n'est pas celui du livre |

**Rejeux** (un projet QuantConnect séparé, une exécution chacun, l'un après l'autre) :

- 08/02 R1 : projet 37336051, backtest `38c7614524d8fa7d3bfeeabfbe968dca` ; PSR 0,3 %. Le journal compte 668 fenêtres, toutes jouées.
- 08/02 R2 : même projet, backtest `935c5f7588034b0054cb9457fc8565b1` ; PSR 5,9 %. Le journal montre le remplissage au milieu de la fourchette : le 2021-10-01 à 03:00, cours acheteur 1,15872, cours vendeur 1,15887, ordre rempli à 1,158795.

**Ce que le verdict de 08/02 dit, et ce qu'il ne dit pas.** La règle de verdict compare des Sharpe calculés par QuantConnect, qui retranchent le taux sans risque ; celui du livre ne vient pas de QuantConnect. Le CAGR ne dépend pas du taux sans risque, et il est lui aussi hors tolérance : l'`ÉCART` ne tient donc pas à la convention de Sharpe. Retirer l'écart achat-vente remonte le CAGR de 7,0 points (de −6,20 % à 0,77 %) et le Sharpe de 0,83 : c'est le coût principal de la stratégie telle qu'elle est codée, mais il ne suffit pas à retrouver le livre. Deux causes candidates restent ouvertes sur #18901 : la source de données (EBS ou OANDA) et l'horodatage exact des fenêtres. Le sens des fenêtres n'en est probablement pas une. Au milieu de la fourchette, inverser les sens rend opposé le résultat de chaque fenêtre, et donnerait donc un CAGR proche de −0,8 % (déduction, non mesurée).

**Écarts internes au livre** (tranche 4) :

- 08/01 : la table 8.9 publie aussi des allocations conventionnelles (poids égaux, parité de risque, Markowitz, variance minimale), sur un portefeuille de 5 ETF de 2019 à 2022 rééquilibré toutes les deux semaines. Elles se rejoueraient sans le service. Ce rejeu sort du périmètre de cette comparaison, qui confronte le livre à nos reproductions.
- 08/02 : le livre publie un « rendement annuel moyen », pas un CAGR. À ces niveaux de rendement, l'écart entre les deux est faible devant la tolérance de 2 points.

---

## Ressources du dépôt mal rattachées au livre

Ces README citent le livre, mais l'exemple qu'ils nomment ne correspond pas à leur contenu. Les corriger relève d'une PR sur chaque projet.

| Ressource | Ce que dit son README | Ce qu'elle contient |
|-----------|----------------------|---------------------|
| [LSTM-Forecasting](projects/LSTM-Forecasting/) | « Ch06/Ex07 » | prévision par LSTM ; l'exemple 07 du ch. 06 porte sur les splits d'actions |
| [RL-DQN-Trading](projects/RL-DQN-Trading/), [Reinforcement-Learning-Trading](projects/Reinforcement-Learning-Trading/) | chapitre 07 | DQN sur actions, sans couverture d'options |
| [ML-DeepLearning](projects/ML-DeepLearning/) | « chapitre 13.6 » | le livre n'a pas de chapitre 13 dans son dépôt de code |

---

## Projets apparentés hors exemples du livre

Ces projets n'ont pas d'exemple correspondant dans le livre, mais illustrent des notions qu'il utilise.

| Projet | Notion |
|--------|--------|
| [EMA-Cross-Alpha](projects/EMA-Cross-Alpha/) | croisement de moyennes mobiles, première brique avant l'apprentissage |
| [DualMomentum](projects/DualMomentum/) | momentum (repérage de tendance) |
| [MeanReversion](projects/MeanReversion/) | retour à la moyenne |
| [AllWeather](projects/AllWeather/) | allocation de portefeuille |
| [ETF-Pairs](projects/ETF-Pairs/) | trading de paires |
| [Sector-Momentum](partner-course-quant-trading/examples/Sector-Momentum/) | momentum sectoriel |
| [Crypto-LSTM-Prediction](projects/Crypto-LSTM-Prediction/), [Sector-ML-Classification](projects/Sector-ML-Classification/) | apprentissage profond et classification, en phase de recherche |

---

## Exemples sans reproduction

| Exemple | Suite |
|---------|-------|
| 04/05, 04/18, 05/02, 05/15 | [#18957](https://github.com/jsboige/CoursIA/issues/18957) : écart interquartile, élimination récursive des variables, régression polynomiale, OPTICS (scripts courts sur données synthétiques, à porter dans QC-Py-18 à 20) |
| 06/02 | [#18958](https://github.com/jsboige/CoursIA/issues/18958) : régimes par prétraitement de facteurs |
| 06/08/01, 06/08/03 | [#18960](https://github.com/jsboige/CoursIA/issues/18960) : stop fixe de référence et couverture par put, dans [Stoploss-Volatility-ML](projects/Stoploss-Volatility-ML/) |
| 06/18/02, 06/19/02 | [#18962](https://github.com/jsboige/CoursIA/issues/18962) : ré-entraînement de Chronos et de FinBERT (calcul GPU) |
| 07/01 | [#18902](https://github.com/jsboige/CoursIA/issues/18902) |
| 08/01 | exclusion : le livre appelle l'API payante PredictNow.ai ; le dépôt garde une optimisation sans service externe |
| 08/02 | [#18901](https://github.com/jsboige/CoursIA/issues/18901) (méta-étiquetage sans l'API PredictNow.ai) |

---

## Utiliser cet inventaire

1. Lire d'abord l'exemple dans le livre, pour la théorie.
2. Ouvrir la ressource du dépôt correspondante : un notebook `Python/QC-Py-*` pour la pratique pas à pas, un projet `projects/*` pour l'algorithme complet.
3. Adapter l'exemple dans ses propres projets sur QuantConnect Cloud.

| Aspect | Livre | Dépôt CoursIA |
|--------|-------|---------------|
| Langage | Python | Python (C# pour une partie des projets) |
| Exécution | QC Cloud et LEAN CLI | QC Cloud et QuantBook |
| Approche | apprentissage automatique appliqué au trading | trading algorithmique complet, des fondations à l'IA |
| Données | jeux de données QC propres à chaque exemple | données standard de QC |

Le livre se concentre sur l'apprentissage automatique appliqué. La série `Python/` couvre aussi les fondations, qu'il vaut mieux maîtriser avant les exemples du livre : plateforme et données (QC-Py-01 à 04), univers, ordres et risque (05 à 10), indicateurs, backtest et Algorithm Framework (11 à 15). Les notebooks 16 et suivants correspondent aux chapitres 04 à 08 du livre.

## Liens

- Livre : [Hands-On AI Trading with Python, QuantConnect, and AWS](https://www.hands-on-ai-trading.com/)
- Code du livre : https://github.com/QuantConnect/HandsOnAITradingBook
- Statut des stratégies du dépôt : [docs/qc/qc-strategies-status.md](../../docs/qc/qc-strategies-status.md)
- Documentation QuantConnect : https://www.quantconnect.com/docs
