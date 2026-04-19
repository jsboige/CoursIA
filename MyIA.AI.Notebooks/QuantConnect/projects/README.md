# QuantConnect Algorithmic Trading Projects

Dernière mise à jour : 2026-04-19

Bibliothèque pédagogique de **78 stratégies** de trading algorithmique sur QuantConnect Cloud
+ **8 clones QC Strategy Library** + **6 composants Framework** + **3 research/tools** = **95 projets**.
Chaque stratégie illustre un concept ou une famille de stratégies ; les performances varient
volontairement pour montrer que toutes les idées académiques ne survivent pas au backtest réaliste.

## Classification

Les strategies sont classees en 3 categories pedagogiques :

| Label | Signification | Action |
|-------|---------------|--------|
| **Robuste** | Sharpe > 0.5, stable sur longue periode, signal propre | Conserver, iterer si besoin |
| **Historique** | Prime connue mais regime-dependante ou affaiblie | Conserver comme contre-exemple, documenter les regimes favorables |
| **Exploratoire** | Implementation naive ou signal insuffisant | Conserver si pedagogique, sinon retravailler |

Voir [OPTIMIZATION_BACKLOG.md](OPTIMIZATION_BACKLOG.md) pour les plafonds structurels et hypotheses testees.

## Performance Summary

### Robuste (Sharpe > 0.5)

| Projet | Description | Sharpe | CAGR | Max DD | Periode | Lang | Niveau | Research | Note |
|--------|-------------|--------|------|--------|---------|------|--------|----------|------|
| [BTC-MACD-ADX](BTC-MACD-ADX/) | MACD + ADX filter BTC daily | **1.647** | 38.1% | 48.8% | 2020-2026 | C# | Intermediaire | — | |
| [Framework_Composite_TrendWeather](Framework_Composite_TrendWeather/) | TrendStocksLite + AllWeather via Algorithm Framework (T75/AW25, Mom3m) | **1.155** | 27.4% | 27.7% | 2015-2026 | Py | Avance | QuantBook | |
| [CSharp-BTC-EMA-Cross](CSharp-BTC-EMA-Cross/) | EMA crossover BTC (C#) | **1.094** | 36.2% | 40.7% | 2017-2026 | C# | Debutant | — | |
| [BlackLitterman-Momentum](BlackLitterman-Momentum/) | Black-Litterman + multi-window momentum views (ECE Item 5, 15 large-caps) | **0.779** | 16.75% | 22.1% | 2015-2026 | Py | Avance | — | He & Litterman Omega calibration, Ledoit-Wolf shrinkage, Net Profit 449.7% |
| [Option-Wheel](Option-Wheel/) | Wheel strategy SPY (sell puts/calls) | **0.524** | 12.69% | 26.40% | 2015-2026 | Py | Avance | QuantBook | ✅ Validé 2015-2026 (Sharpe 0.524) |
| [EMA-Cross-Stocks](EMA-Cross-Stocks/) | EMA 20/50 multi-stock (AAPL/MSFT/GOOGL/AMZN/NVDA) | **0.872** | 25.7% | 35.7% | 2015-2026 | Py | Debutant | — | |
| [TrendStocksLite](TrendStocksLite/) | EMA20/50 + SMA200 trend 15 large-caps diversifies | **0.719** | 18.2% | 33.7% | 2015-2026 | Py | Intermediaire | — | |
| [AllWeather](AllWeather/) | Portfolio multi-asset (SPY/IEF/GLD/XLP, no TLT) | **0.667** | 9.3% | 16.4% | 2010-2026 | Py | Debutant | yfinance | |
| [SectorMomentum](SectorMomentum/) | Dual Momentum SPY/TLT/GLD (Antonacci) | **0.621** | 13.2% | 22.8% | 2010-2026 | Py | Intermediaire | yfinance | |
| [MomentumStrategy](MomentumStrategy/) | Rotation momentum 11 ETFs + stop-loss | **0.565** | 11.8% | 25.8% | 2010-2026 | Py | Intermediaire | yfinance | |
| [RegimeSwitching](RegimeSwitching/) | Regime detection + asset rotation | **0.553** | 11.7% | 33.0% | 2008-2026 | Py | Avance | — | |
| [FamaFrench](FamaFrench/) | Factor ETF rotation (VLUE/MTUM/SIZE/QUAL/USMV) | **0.540** | 12.1% | 24.2% | 2015-2026 | Py | Intermediaire | yfinance | |
| [AdaptiveAssetAllocation](AdaptiveAssetAllocation/) | Momentum + min-variance multi-asset | **0.518** | 8.0% | 18.8% | 2008-2026 | Py | Avance | — | |
| [Options-VGT](Options-VGT/) | Options income VGT (wheel NVDA/ORCL/CSCO/AMD/QCOM) | **0.507** | 14.2% | 16.2% | 2020-2026 | Py | Avance | — | |
| [CSharp-CTG-Momentum](CSharp-CTG-Momentum/) | CTG momentum strategy (C#) | **0.507** | 17.7% | 36.1% | 2015-2026 | C# | Intermediaire | — | |

### Historique / Regime-dependante (Sharpe 0-0.5, prime connue mais affaiblie)

| Projet | Description | Sharpe | CAGR | Max DD | Periode | Lang | Niveau | Research | Note |
|--------|-------------|--------|------|--------|---------|------|--------|----------|------|
| [Multi-Layer-EMA](Multi-Layer-EMA/) | Multi-layer EMA + vol filter BTCUSDT | **0.928** | 120.9% | 54.4% | 2020-2026 | Py | Intermediaire | QuantBook | NON ROBUSTE: Sharpe chute a 0.38 hors bulle 2017, MaxDD 67.7% |
| [Crypto-MultiCanal](Crypto-MultiCanal/) | ZigZag multi-channel (macro/meso/micro) BTCUSDT | **0.486** | 7.6% | 16.8% | 2017-2026 | Py | Avance | QuantBook | ❌ Runtime Error: cannot import 'find_envelope_line' |
| [EMA-Cross-Index](EMA-Cross-Index/) | EMA 20/60 + cooldown 3d SPY | **0.470** | 9.4% | 17.5% | 2015-2026 | Py | Debutant | yfinance | 25 combos testees |
| [DualMomentumNoTLT](DualMomentumNoTLT/) | Momentum rotation SPY/QQQ/IEF/GLD/XLP (no TLT) | **0.469** | 11.0% | 23.6% | 2015-2026 | Py | Intermediaire | — | Variante sans TLT |
| [CausalEventAlpha](CausalEventAlpha/) | CATE sector rotation via DML proxy (rolling OLS) + GradientBoosting (ECE Item 3) | **0.423** | 11.15% | 38.7% | 2015-2026 | Py | Avance | — | Win Rate 85%, 8 sector ETFs, regime bear/bull SMA200 |
| [RiskParity](RiskParity/) | Risk parity multi-asset portfolio | **0.399** | 7.8% | 20.9% | 2015-2026 | Py | Intermediaire | — | Plafond (3 hyp. rejetees) |
| [DualMomentum](DualMomentum/) | Absolute + relative momentum ETFs | **0.350** | 9.2% | 33.6% | 2015-2026 | Py | Intermediaire | yfinance | MaxDD COVID structurel |
| [FuturesTrend](FuturesTrend/) | Donchian breakout ETFs (trend following) | **0.136** | 4.896% | 18.70% | 2015-2026 | Py | Intermediaire | yfinance | ✅ Validé 2015-2026 (Sharpe 0.136) |
| [MeanReversion](MeanReversion/) | RSI multi-asset mean reversion | **0.294** | 7.5% | 16.5% | 2015-2026 | Py | Intermediaire | yfinance | SMA filter rejete |
| [BTC-ML](BTC-ML/) | Machine learning BTC prediction | **0.282** | 8.3% | 13.7% | 2023-2026 | Py | Avance | QuantBook | Periode courte, potentiel features |
| [EMA-Cross-Crypto](EMA-Cross-Crypto/) | EMA 20/50 + SMA200 + trailing stop BTCUSDT | **0.244** | 3.804% | 37.2% | 2017-2026 | Py | Debutant | yfinance | Sharpe < 0.5, classe Historique |
| [OptionsIncome](OptionsIncome/) | Covered Call SPY + VIX filter | **0.207** | 5.435% | 17.50% | 2015-2026 | Py | Avance | — | ✅ Validé 2015-2026 (Sharpe 0.207) |
| [Trend-Following](Trend-Following/) | Multi-oracle trend following (MACD/RSI/Bollinger) | N/A | 5.15% | N/A | 2015-2026 | Py | Avance | — | ❌ Timeout (200 stocks × 11 ans hourly trop large) |
| [TurnOfMonth](TurnOfMonth/) | Anomalie calendaire (Turn of Month) | 0.128 | 4.8% | 23.7% | 2015-2026 | Py | Debutant | yfinance | Effet faible en bull 2015-2026 |
| [VIX-TermStructure](VIX-TermStructure/) | Contango/backwardation VIX (SVXY) | 0.051 | 3.6% | 35.2% | 2010-2026 | Py | Avance | yfinance | Post-VIXplosion, SVXY affaibli |

### Exploratoire / Implementation insuffisante (Sharpe < 0)

| Projet | Description | Sharpe | CAGR | Max DD | Periode | Lang | Niveau | Research | Probleme |
|--------|-------------|--------|------|--------|---------|------|--------|----------|----------|
| [TrendFilteredMeanReversion](TrendFilteredMeanReversion/) | RSI(2) pullback SPY en bull regime (SMA200) | -0.016 | 3.4% | 11.4% | 2015-2026 | Py | Debutant | — | Signal reel (73% win) mais trop rare (~9 trades/an) |
| [ForexCarry](ForexCarry/) | FX momentum IR + skip-month G10 | -0.324 | 1.5% | 10.5% | 2013-2026 | Py | Intermediaire | yfinance | CAGR < T-bills, carry prime evaporee |
| [PairsTrading](PairsTrading/) | Statistical arbitrage equity pairs | -0.361 | 0.9% | 15.1% | 2010-2026 | Py | Intermediaire | — | Paires non cointegrees 2010-2026 |
| [ETF-Pairs](ETF-Pairs/) | Cointegration-based ETF pairs | -0.706 | -4.7% | 35.0% | 2020-2026 | Py | Intermediaire | QuantBook | Cointregration instable |

### Machine Learning / Deep Learning / RL (backtestees)

Strategies ML/AI basees sur le livre *Hands-On AI Trading* et implementations internes. Toutes backtestees sur QC Cloud (2015-2026 sauf mention contraire). Les implementations utilisent principalement `sklearn` (RandomForest, XGBoost, MLPClassifier/Regressor) ; les batch HandsOn Ex14/Ex17 utilisent tensorflow/keras (Conv1D) disponible nativement sur QC Cloud ; Ex05 utilise pywt (PyWavelets) + SVR.

| Projet | Description | Sharpe | CAGR | Max DD | Periode | Book | Note |
|--------|-------------|--------|------|--------|---------|------|------|
| [Portfolio-Optimization-ML](Portfolio-Optimization-ML/) | Markowitz + ML returns prediction (15 large-caps) | **0.896** | 27.6% | 41.6% | 2015-2026 | — | Beta 1.14 |
| [Gaussian-Direction-Classifier](Gaussian-Direction-Classifier/) | Gaussian classifier direction (8 stocks, prob-weighted) | **0.761** | --- | 25.6% | 2015-2026 | Ch06-Ex15 | Beta 0.54, Treynor +60% vs v1 |
| [ML-RandomForest](ML-RandomForest/) | Random Forest classification multi-asset (8 ETFs) | **0.682** | 20.1% | 36.4% | 2015-2026 | — | v3, anti-overfitting |
| [ML-XGBoost](ML-XGBoost/) | XGBoost gradient boosting (9 positions, biweekly) | **0.566** | 14.8% | 38.6% | 2015-2026 | — | v2, train/trade separation |
| [ML-Temporal-CNN](ML-Temporal-CNN/) | Real Conv1D Keras CNN direction prediction (QQQ top-3, weekly retrain, confidence gate) | **0.734** | 20.51% | 21.6% | 2019-2024 | Ch06-Ex14 | Alpha 0.11, Beta 0.264, PSR 28.7%, 594 trades |
| [Temporal-CNN-Prediction](Temporal-CNN-Prediction/) | MLP multi-scale temporal features (8 ETFs) | **0.536** | 13.8% | 33.9% | 2015-2026 | Ch06-Ex14 | v2, real MLP(128,64,32) proxy sklearn |
| [RL-DQN-Trading](RL-DQN-Trading/) | DQN portfolio-level actions (MLPRegressor) | **0.533** | 10.9% | 25.8% | 2015-2026 | Ch07-Ex01 | v2.0.1, 3 action templates |
| [LSTM-Forecasting](LSTM-Forecasting/) | MLP temporal features multi-ETF (7 assets) | **0.525** | 11.3% | 32.5% | 2015-2026 | Ch06-Ex07 | v2.1, real MLP(64,32) |
| [Sector-ML-Classification](Sector-ML-Classification/) | RF rank classifier rotation sectorielle (11 ETFs) | **0.473** | 11.9% | 34.4% | 2015-2026 | — | v5, RF as rank not filter |
| [Markov-Regime-Detection](Markov-Regime-Detection/) | Hidden Markov Model regime detection + allocation | **0.408** | --- | --- | 2015-2024 | Ch06-Ex04 | v1.0, TLT risk-off |
| [Chronos-Foundation-Forecasting](Chronos-Foundation-Forecasting/) | GBM+Ridge ensemble forecasting (8 ETFs) | **0.253** | --- | 22.4% | 2015-2026 | Ch06-Ex18 | v2, SMA200 regime filter |
| [ML-SVM](ML-SVM/) | SVM linear kernel equity-only ETFs | **0.147** | 5.2% | 27.1% | 2015-2026 | — | v3, plafond structurel |
| [ML-FX-SVM-Wavelet](ML-FX-SVM-Wavelet/) | SVR + wavelet decomposition 4 Forex pairs (EURJPY/GBPUSD/AUDCAD/NZDCHF) leverage 20x | **0.167** | 5.07% | 20.5% | 2019-2024 | Ch06-Ex05 | 4211 trades (overtrading), Win Rate 12%, echec pedagogique |
| [Dividend-Harvesting-ML](Dividend-Harvesting-ML/) | DecisionTree dividend yield prediction (QQQ top 100) | **0.469** | 12.7% | 30.5% | 2015-2026 | Ch06-Ex06 | v1, fundamental factors |
| [PCA-StatArbitrage](PCA-StatArbitrage/) | PCA + LinearRegression stat-arb mean reversion (top 100) | **0.399** | 12.65% | 31.8% | 2019-2024 | Ch06-Ex13 | v1, sklearn, book period |
| [PCA-StatArb](PCA-StatArb/) | PCA + OLS stat-arb mean reversion (top 100 liquid) | **0.165** | 5.3% | 35.9% | 2015-2026 | Ch06-Ex13 | v1, statsmodels, extended period |
| [Clustering-Fundamentals-ML](Clustering-Fundamentals-ML/) | PCA + GBR fundamental ranking (top 10 of 100) | -0.052 | -1.2% | 15.3% | 2015-2026 | Ch06-Ex10 | v1.1, Runtime Error, a ameliorer |
| [ML-HeadShoulders-CNN](ML-HeadShoulders-CNN/) | Keras CNN Head & Shoulders detection USDCAD (synthetic training fallback) | **-46.8** | 0.03% | 0.1% | 2019-2024 | Ch06-Ex17 | Seulement 4 trades, echec de generalisation synthetique -> reel documente |
| [Stoploss-Volatility-ML](Stoploss-Volatility-ML/) | Lasso regression stop-loss optimization (KO equity) | --- | --- | --- | --- | Ch06-Ex08 | BROKEN: CBOE data unavailable (#233) |
| [InverseVolatility-Rank](InverseVolatility-Rank/) | Ridge regression inverse-vol futures allocation | **0.212** | 5.85% | 54.7% | 2015-2026 | Ch06-Ex11 | v1, MaxDD inacceptable |
| [TradingCosts-Optimization](TradingCosts-Optimization/) | DecisionTree crypto cost optimization (BTCUSDC) | -13.354 | -0.015% | 0.4% | 2015-2026 | Ch06-Ex12 | v1, educatif (quasi flat) |
| [SVM-Wavelet-Forecasting](SVM-Wavelet-Forecasting/) | SVM + wavelet decomposition FX | --- | --- | --- | --- | Ch06-Ex05 | Local only, pas de backtest |
| [Reinforcement-Learning-Trading](Reinforcement-Learning-Trading/) | DQN experience replay (book implementation) | --- | --- | --- | --- | Ch07-Ex01 | Variant pedagogique |
| [ML-Classification](ML-Classification/) | RandomForest classification direction J+1 (SPY, ObjectStore model) | --- | --- | --- | --- | — | Non backtestee (Cloud ID 29434754) |
| [ML-Regression](ML-Regression/) | Ridge Regression prediction returns J+1 (20 stocks, RSI/EMA/vol features) | --- | --- | --- | --- | — | Non backtestee |
| [ML-Ensemble](ML-Ensemble/) | Ensemble Ridge/RF/LightGBM, 30 large-caps, confidence-based sizing | --- | --- | --- | --- | — | Non backtestee |
| [ML-EnhancedPairs](ML-EnhancedPairs/) | ML-enhanced pairs trading (Engle-Granger cointegration + classifier) | --- | --- | --- | --- | — | Non backtestee |
| [ML-DeepLearning](ML-DeepLearning/) | LSTM/GRU deep learning prediction series temporelles (SPY/QQQ/IWM) | --- | --- | --- | --- | — | Non backtestee (PyTorch) |
| [DL-LSTM](DL-LSTM/) | LSTM bidirectionnel pre-entraine (PyTorch, ObjectStore model) | --- | --- | --- | --- | — | Non backtestee (PyTorch) |
| [ML-TextClassification](ML-TextClassification/) | NLP Naive Bayes sentiment simule (TF-IDF headlines, 5 tech stocks) | --- | --- | --- | --- | — | Non backtestee |
| [RL-Portfolio](RL-Portfolio/) | Q-Learning allocation multi-asset (SPY/TLT/GLD/Cash, epsilon-greedy) | --- | --- | --- | --- | — | Non backtestee |
| [Crypto-LSTM-Prediction](Crypto-LSTM-Prediction/) | DLinear (AAAI 2023) SeriesDecomposition BTCUSDT (PyTorch) | --- | --- | --- | --- | — | Research phase |
| [ML-Trend-Scanning](ML-Trend-Scanning/) | t-statistic linear regression slope across multiple windows (SPY/TLT/GLD) | **0.292** | --- | --- | 2015-2026 | Ch06-Ex01 | Trend regime classification |
| [ML-Reversion-Trending](ML-Reversion-Trending/) | GradientBoosting regime classifier (mean-revert vs trend-follow) 5 ETFs | **0.375** | 8.44% | 24.4% | 2015-2026 | Ch06-Ex03 | Dual-strategy switching |
| [ML-HMM-Regime](ML-HMM-Regime/) | Markov-switching dynamic regression 2-regime detection (SPY/TLT) | **0.571** | --- | --- | 2015-2024 | Ch06-Ex04 | statsmodels MarkovRegression |
| [ML-Gaussian-Classifier](ML-Gaussian-Classifier/) | GaussianNB direction prediction tech stocks, prob-weighted sizing | **0.361** | 12.49% | 47.4% | 2015-2026 | Ch06-Ex15 | Cross-sectional features |
| [ML-LLM-Summarization](ML-LLM-Summarization/) | Tiingo news sentiment + optional OpenAI LLM summarization (SPY) | **0.686** | 15.45% | 22.7% | 2015-2026 | Ch06-Ex16 | Keyword fallback, Tiingo data |
| [ML-PCA-StatArb](ML-PCA-StatArb/) | PCA + OLS stat-arb mean-reversion, Z-score residuals (top 100) | **0.399** | 12.65% | 31.8% | 2019-2024 | Ch06-Ex13 | Book period, sklearn |
| [ML-Pairs-PCA-Selection](ML-Pairs-PCA-Selection/) | PCA-based pair selection research | --- | --- | --- | --- | Ch06-Ex09 | Research only (no main.py) |
| [ML-Chronos-Foundation](ML-Chronos-Foundation/) | Amazon Chronos-t5-tiny foundation model portfolio allocation (8 ETFs) | **0.277** | 7.23% | 13.5% | 2015-2026 | Ch06-Ex18 | Foundation model, SMA200 regime |
| [ML-FinBERT-Sentiment](ML-FinBERT-Sentiment/) | ProsusAI/finbert sentiment from Tiingo news, most volatile tech stock | N/A | N/A | N/A | --- | Ch06-Ex19 | TF unavailable on QC Cloud, 0 trades |
| [Positive-Negative-Splits-ML](Positive-Negative-Splits-ML/) | LinearRegression split-event return prediction, sector momentum | **1.736** | 90.83% | 42.4% | 2015-2026 | Ch06-Ex07 | Split factor + XLK ROC features |
| [Adaptive-Conformal-Risk](Adaptive-Conformal-Risk/) | Adaptive Conformal Inference risk overlay on multi-factor momentum (15 large-caps) | --- | --- | --- | --- | ECE-Item6 | ACI algorithm (Gibbs & Candès 2021) |
| [Dynamic-Options-Wheel](Dynamic-Options-Wheel/) | Dynamic delta/skew options wheel, IV percentile OTM targeting (SPY) | **0.119** | 5.59% | --- | 2015-2026 | ECE-Item7 | Extends Option-Wheel with IV regime |
| [CSharp-BTC-MACD-ADX](CSharp-BTC-MACD-ADX/) | MACD + ADX filter BTC daily (C# variant with robustness research) | **1.647** | 38.1% | 48.8% | 2020-2026 | — | C# variant, same as BTC-MACD-ADX |

*78 strategies documentees dans les tables ci-dessus (71 Python, 4 C#) + 8 clones QC Strategy Library + 3 projets research/tools + 6 composants Framework. 95 projets au total dont 89 avec code. Metriques issues des backtests QC Cloud.*
*Multi-Layer-EMA reclassee Historique apres analyse de robustesse (Sharpe gonfle par bulle BTC 2017).*
*Research: type de notebook de recherche (yfinance = donnees Yahoo, QuantBook = donnees QC natives, — = pas de notebook).*
*ML/AI: implementations sklearn (RF, XGBoost, MLP) + tensorflow/Keras (Conv1D, Ex14/Ex17) + pywt (Ex05) validees sur QC Cloud. Les fake implementations (poids hardcodes) ont ete remplacees en mars 2026. Les vrais CNN Keras HandsOn ont ete ajoutes le 2026-04-08 (PR #271).*

### QC Strategy Library Clones (8 projets)

Clones de strategiesQC Cloud Library, ajoutes en avril 2026 comme references avancees.

| Projet | Description | OOS 1Y Sharpe | 5Y CAGR | Source |
|--------|-------------|---------------|---------|--------|
| [AssetClassMomentum-QC](AssetClassMomentum-QC/) | Top-3 momentum 5 ETFs (SPY/EFA/BND/VNQ/GSG), Quantpedia #2 | --- | --- | Quantpedia Strategy #2 |
| [DynamicVIXSpyRegime-QC](DynamicVIXSpyRegime-QC/) | RandomForestClassifier + VIX regime switching SPY/TLT/GLD/BIL | **1.72** | 29.76% | QC Strategy Library #50 |
| [HighBookToMarketFScore-QC](HighBookToMarketFScore-QC/) | Piotroski F-Score >= 8 value screen, top 20% book-to-market | **2.09** | 18.44% | QC Strategy Library #343 |
| [LeveragedETFMomentum-QC](LeveragedETFMomentum-QC/) | RSI + SMA regime conditional leveraged ETF rotation | **1.80** | 101.03% | QC Strategy Library #60 |
| [LongShortHarvest-QC](LongShortHarvest-QC/) | Long-short equity ML overlay, Hurst regime, ATR filters | **3.39** | 57.94% | QC Strategy Library #238 |
| [MacroFactorRotation-QC](MacroFactorRotation-QC/) | DecisionTreeRegressor cross-asset rotation SPY/GLD/BND/BTC | **1.23** | 33.45% | QC Strategy Library #72 |
| [PuppiesOfTheDow-QC](PuppiesOfTheDow-QC/) | Dogs of the Dow value-income tilt, top-5 by dividend yield | **1.99** | 10.16% | QC Strategy Library #211 |
| [TermStructureCommodities-QC](TermStructureCommodities-QC/) | Commodity futures roll returns (backwardation/contango) | -0.041 | -15.71% | Quantpedia Strategy #22 |

*Les metriques OOS proviennent de la QC Strategy Library et n'ont pas ete re-backtestees localement.*

### HMM-KMeans-Voting (Research)

- **HMM-KMeans-Voting** : Custom K-Means clustering (pure numpy) + Hidden Markov Model voting ensemble pour regime detection. Implementation pedagogique sans dependance sklearn. Research notebook uniquement (pas de backtest QC Cloud).

## Description des strategies

### EMA Crossover (Debutant)

Strategies basees sur le croisement de moyennes mobiles exponentielles :

- **EMA-Cross-Crypto** : Long BTCUSDT quand EMA20 > EMA50 ET BTC > SMA200 (filtre bull). Trailing stop 10%, position 80%. Binance Cash, daily.
- **EMA-Cross-Index** : Long SPY quand EMA20 > EMA60, flat sinon. Cooldown 3 jours apres sortie. Daily.
- **EMA-Cross-Stocks** : Equal-weight portfolio de 5 tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA). Chaque stock est long individuellement quand son EMA20 > EMA50.
- **TrendStocksLite** : EMA20/50 + SMA200 filter sur 15 large-caps diversifies (5 secteurs). Equal-weight hebdomadaire. Extension de EMA-Cross-Stocks.
- **Multi-Layer-EMA** : EMA multi-couches sur BTCUSDT avec filtre de volatilite (seuil 60%). Allocation 100%.
- **CSharp-BTC-EMA-Cross** : EMA crossover BTC en C# avec parametres (45, 120). Daily.

### Trend Following & Indicateurs Techniques (Intermediaire/Avance)

- **Trend-Following** : Multi-oracle scoring (MACD, RSI, Bollinger) + detection HH/HL/LL/LH + ATR trailing stop. Universe equity top 600. Multi-fichiers (alpha.py, oracles). Hourly resolution.
- **BTC-MACD-ADX** : MACD + ADX filter sur BTC daily en C#. Backtest long (2019-2026).
- **CSharp-CTG-Momentum** : Momentum strategy avec indicateurs custom en C#.

### Momentum & Rotation (Intermediaire)

- **SectorMomentum** : Dual Momentum d'Antonacci entre SPY/TLT/GLD. Lookback 12 mois.
- **MomentumStrategy** : Rotation mensuelle parmi 11 ETFs sectoriels, top-3 par momentum + stop-loss -10%.
- **FamaFrench** : Rotation trimestrielle entre 5 facteurs Fama-French (VLUE/MTUM/SIZE/QUAL/USMV).
- **DualMomentum** : Momentum absolu + relatif entre equities et bonds.
- **DualMomentumNoTLT** : Momentum rotation mensuelle sur SPY/QQQ/IEF/GLD/XLP (sans TLT). Top-2 par momentum 12M.
- **FuturesTrend** : Donchian breakout sur ETFs (trend following classique).

### Portfolio Construction (Intermediaire/Avance)

- **BlackLitterman-Momentum** (ECE Item 5) : Framework Black-Litterman avec vues momentum multi-fenetres sur 15 large-caps. Calibration Omega He & Litterman 1999, covariance Ledoit-Wolf shrinkage (pure numpy), contraintes de concentration sectorielle, vol targeting. Sharpe 0.779, Net Profit 449.7%, concept etudiant ECE fusionne de 4 groupes.
- **Framework_Composite_TrendWeather** : Composite strategy combinant TrendStocksLite (15 large-caps momentum-weighted) + AllWeather (SPY/IEF/GLD/XLP) via QC Algorithm Framework. T75/AW25 allocation, 3m momentum weighting, monthly rebalance. Itere de v1.0 (Sharpe 0.622) a v1.5 (Sharpe 1.155).
- **Framework_Composite_FamaFrenchAllWeather** : Composite strategy combinant FamaFrench (5 facteurs ETF avec momentum risk-adjusted) + AllWeather (SPY/IEF/GLD/XLP) via QC Algorithm Framework. Baseline FF50/AW50, allocation sweep prevu (FF40/AW60, FF50/AW50, FF60/AW40). **PENDING QC deployment et backtest.**
- **AllWeather** : Portfolio "All Weather" simplifie (SPY 30%/IEF 30%/GLD 30%/XLP 10%, TLT elimine). Drift rebalancing 3%.
- **RiskParity** : Allocation inversement proportionnelle a la volatilite.
- **AdaptiveAssetAllocation (AAA)** : Momentum + minimum-variance sur un univers multi-asset.
- **RegimeSwitching** : Detection de regimes de marche (bull/bear/crisis) et rotation d'actifs.
- **Framework_Composite_EMATrend** : Composite EMA-Cross + TrendStocks via Algorithm Framework. EMA40/Trend60 allocation. Non backtestee.
- **Framework_Composite_MomentumRegime** : Composite SectorMomentum + RegimeSwitching via Algorithm Framework. T60/RS40 allocation. Non backtestee.
- **EMA-Cross-Alpha** : Building block Framework Alpha: EMA 20/50 crossover (5 tech stocks). Composant pour composites.
- **TrendStocks-Alpha** : Building block Framework Alpha: EMA 20/50 + SMA200 trend filter (15 large-caps). Composant pour composites.

### Research & Tools (pas de backtest)

- **Alpha-Correlation-Analysis** : QuantBook notebook pour analyse de correlation entre alphas complementaires (issue #140).
- **ML-FeatureEngineering** : QuantBook reference pedagogique feature engineering (RSI, momentum, vol, volume, PCA, pipeline). 32 cellules.

### Mean Reversion & Pairs (Intermediaire)

- **MeanReversion** : Signaux RSI multi-asset, achat en survente, vente en surachat.
- **TrendFilteredMeanReversion** : RSI(2) pullback sur SPY conditionne par regime bull (SMA200). Time stop 5 jours.
- **PairsTrading** : Arbitrage statistique sur paires d'actions cointegrees.
- **ETF-Pairs** : Cointegration-based pairs trading sur ETFs.

### Options & Volatilite (Avance)

- **OptionsIncome** : Covered calls sur SPY avec filtre VIX (bande 15-35). Resolution MINUTE.
- **Option-Wheel** : Wheel strategy sur SPY (sell puts, si assigne sell calls). DTE 30, OTM 5%.
- **Options-VGT** : Covered calls sur VGT ETF (NVDA/ORCL/CSCO/AMD/QCOM). Resolution MINUTE.
- **VIX-TermStructure** : Trading de la structure a terme du VIX (contango/backwardation).
- **Dynamic-Options-Wheel** (ECE Item 7) : Extension du Option-Wheel avec selection dynamique de strike basee sur IV percentile (2.5-7.5% OTM) et ajustement skew 25-delta. SPY, resolution MINUTE. Concept etudiant ECE (Asseli, Gr01 H.5).
- **Adaptive-Conformal-Risk** (ECE Item 6) : Overlay de risque par inference conforme adaptive (ACI, Gibbs & Candès 2021) sur strategie momentum multi-facteurs. 15 large-caps US (5 secteurs). Concept etudiant ECE (El Bakkali, Gr02). Non backtestee.

### Crypto avancee (Avance)

- **Crypto-MultiCanal** : 3 canaux ZigZag imbriques (macro/meso/micro) sur BTCUSDT. Signaux de rebond sur support et breakout de resistance. Trail SL a breakeven. Binance Cash daily.
- **BTC-ML** : Prediction BTC par machine learning (features techniques + filtre de volatilite 60%).
- **Crypto-LSTM-Prediction** : Deep Learning DLinear (AAAI 2023) pour prediction BTCUSDT. PyTorch avec SeriesDecomposition (trend/seasonal). **Research Phase**.

### Machine Learning / Deep Learning / RL (Intermediaire/Avance)

Strategies ML/AI implementees avec `sklearn` (compatible QC Cloud). Basees sur le livre *Hands-On AI Trading* de Jared Broad et implementations internes.

- **ML-RandomForest** : Random Forest classification sur 8 ETFs (SPY/QQQ/IWM/DIA/EFA/VEA/VWO/GLD). Biweekly rebalance, anti-overfitting (max_depth 5, min_samples 10). v3.
- **ML-XGBoost** : XGBoost gradient boosting sur 9 positions. Train/trade separation (odd/even Mondays), 10-day forward target, biweekly. v2.
- **ML-SVM** : SVM kernel lineaire sur ETFs equity-only. Plafond structurel confirme (0.147). v3.
- **Sector-ML-Classification** : Random Forest comme classifieur de rang (pas filtre binaire) pour rotation sectorielle (11 sector ETFs). Bull: top-4 par proba RF. Bear: defensifs si proba > 0.35. v5.
- **CausalEventAlpha** (ECE Item 3) : Rotation sectorielle causale via proxy DML (rolling OLS) + GradientBoosting classifier par secteur. 8 sector ETFs avec regime bear/bull (SMA 200). Concept etudiant ECE (ErwanSi, Gr03 G.1). Sharpe 0.423, Win Rate 85% (eleve mais CAGR modeste 11.15%).
- **Portfolio-Optimization-ML** : MPT (Markowitz) avec covariance Ledoit-Wolf + returns predits par ML. Universe: 15 large-caps US (5 secteurs). Risk Parity weighting.
- **Gaussian-Direction-Classifier** (Book Ex15) : Classifieur gaussien pour prediction de direction. 8 stocks, seuil confiance 0.60, sizing par probabilite, SMA200 regime filter. v2 risk-adjusted.
- **ML-Temporal-CNN** (Book Ex14, Keras) : Vrai CNN Conv1D Keras pour prediction de direction sur QQQ top-3. Reentrainement hebdomadaire, confidence gate >55%. Sharpe 0.734, alpha 0.11, beta 0.264. Strategie la plus performante du batch HandsOn batch3.
- **Temporal-CNN-Prediction** (Book Ex14, sklearn proxy) : MLPClassifier(128,64,32) avec 18 features temporelles multi-echelle (5j/10j/20j) mimetisant des noyaux CNN. 3 classes (UP/DOWN/NEUTRAL). 8 ETFs. v2 - implementation proxy pour QC Cloud sans tensorflow.
- **LSTM-Forecasting** (Book Ex07) : MLPClassifier(64,32) avec Pipeline+StandardScaler. 20 features temporelles par symbole. 7 ETFs, rebalance hebdo, min_positions=2. v2.1.
- **Chronos-Foundation-Forecasting** (Book Ex18) : Ensemble GBM(50 estimators)+Ridge(alpha=10) avec StandardScaler. 21 features par asset. SMA200 regime filter (bear = defensifs). 8 ETFs. v2.
- **RL-DQN-Trading** (Book Ch07) : MLPRegressor(64,32) avec actions portfolio-level (AGGRESSIVE/MODERATE/DEFENSIVE). Reward risk-adjusted. Replay buffer 5000. 5 ETFs. v2.0.1.
- **Reinforcement-Learning-Trading** (Book Ch07) : Variante pedagogique DQN avec experience replay.
- **Markov-Regime-Detection** (Book Ex04) : HMM 3 regimes (bull/neutral/bear) avec allocation dynamique (SPY/TLT). Monthly rebalance. v1.0.
- **Dividend-Harvesting-ML** (Book Ex06) : DecisionTreeRegressor pour prediction du rendement dividende. Facteurs fondamentaux (PE ratio, revenue growth, free cash flow %, dividend payout ratio, current ratio). Universe QQQ top 100, monthly rebalance. v1.
- **PCA-StatArb** (Book Ex13) : PCA + OLS pour arbitrage statistique mean-reversion. 3 composantes principales, z-score des residus (seuil 1.5). Universe top 100 par dollar volume. Monthly. v1.
- **Clustering-Fundamentals-ML** (Book Ex10) : PCA (5 composantes) + GradientBoostingRegressor sur 26 facteurs fondamentaux. Selectionne top-10 par rendement predit. Equal-weight, monthly. v1.
- **Stoploss-Volatility-ML** (Book Ex08) : Lasso regression pour stop-loss optimal base sur VIX, ATR et std des rendements. Cycles hebdomadaires (lundi-vendredi) sur KO equity. v1.
- **InverseVolatility-Rank** (Book Ex11) : Ridge regression pour prevision volatilite future. Allocation inversement proportionnelle a la volatilite predite sur 12 contrats futures (indices, energie, grains). v1.
- **TradingCosts-Optimization** (Book Ex12) : DecisionTreeRegressor pour optimiser les couts d'execution BTCUSDC. Facteurs: ATR, volume moyen, spread. Vend quand cout predit < moyenne mobile. v1.
- **SVM-Wavelet-Forecasting** (Book Ex05, local only) : SVM + decomposition wavelet pour prediction FX. Implementation locale initiale, pas de backtest QC.
- **ML-FX-SVM-Wavelet** (Book Ex05, QC Cloud) : Portage QC Cloud de Ex05 avec SVR + wavelet sur 4 paires Forex (EURJPY/GBPUSD/AUDCAD/NZDCHF), leverage 20x. Sharpe 0.167, Win Rate 12%, 4211 trades (overtrading). Echec pedagogique documente : le pattern SVM+wavelet est tres sensible aux parametres, et leverage 20x amplifie l'overtrading.
- **ML-HeadShoulders-CNN** (Book Ex17, Keras) : Detection CNN de pattern Head & Shoulders sur USDCAD. Le main.py d'origine chargeait un modele Keras depuis l'Object Store ; fallback synthetique ajoute (commit d34d8b49) qui entraine un petit CNN Conv1D sur des patterns gaussiens generes aleatoirement si le modele n'est pas present. Sharpe -46.8 (artefact de variance minuscule), seulement 4 trades : echec de generalisation synthetique -> reel documente.
- **BTC-ML** : Prediction BTC par machine learning (features techniques + filtre volatilite 60%). Periode courte 2023-2026.
- **PCA-StatArbitrage** (Book Ex13) : PCA + sklearn LinearRegression pour stat-arb. Meme concept que PCA-StatArb mais avec sklearn sur la periode du livre (2019-2024). Sharpe 0.399. v1.
- **ML-Classification** : RandomForest classification direction J+1 sur SPY. Modele charge depuis ObjectStore. Non backtestee.
- **ML-Regression** : Ridge Regression prediction returns J+1 sur 20 stocks. Features: RSI, EMA, volume. Non backtestee.
- **ML-Ensemble** : Ensemble Ridge/RF/LightGBM sur 30 large-caps. Weighted averaging, confidence-based sizing. Non backtestee.
- **ML-EnhancedPairs** : Pairs trading ML-enhanced avec cointegration Engle-Granger + classifier entree/sortie sur ETFs sectoriels. Non backtestee.
- **ML-DeepLearning** : LSTM/GRU deep learning prediction series temporelles (SPY/QQQ/IWM). PyTorch. Non backtestee.
- **DL-LSTM** : LSTM bidirectionnel pre-entraine charge depuis ObjectStore. PyTorch. Non backtestee.
- **ML-TextClassification** : NLP Naive Bayes sur sentiment simule (TF-IDF headlines). 5 tech stocks. Non backtestee.
- **RL-Portfolio** : Q-Learning agent allocation multi-asset (SPY/TLT/GLD/Cash). Epsilon-greedy exploration. Non backtestee.
- **Crypto-LSTM-Prediction** : DLinear (AAAI 2023) avec SeriesDecomposition (trend/seasonal) pour BTCUSDT. PyTorch. Research phase.
- **ML-Trend-Scanning** (Book Ex01) : t-statistique de la pente de regression lineaire sur fenetres multiples (5/10/21/42/63j) pour classifier le regime de tendance. SPY/TLT/GLD, regime bull/bear/neutral.
- **ML-Reversion-Trending** (Book Ex03) : GradientBoosting classifieur de regime (mean-reversion vs trending). Applique RSI+Bollinger en regime mean-reversion, MA crossover en trending. 5 ETFs.
- **ML-HMM-Regime** (Book Ex04) : Modele Markov-switching 2 regimes (haute/basse volatilite) via statsmodels MarkovRegression. Allocation SPY (low-vol) / TLT (high-vol).
- **ML-Gaussian-Classifier** (Book Ex15) : GaussianNB prediction de direction sur tech stocks. Features: rendements open-close cross-sectionnels. Sizing par probabilite.
- **ML-LLM-Summarization** (Book Ex16) : Sentiment news Tiingo + optional OpenAI LLM summarization. Fallback keyword-based. SPY, 2015-2026. Sharpe 0.686.
- **ML-PCA-StatArb** (Book Ex13, book period) : PCA + sklearn LinearRegression stat-arb mean-reversion. Meme concept que PCA-StatArb mais periode du livre (2019-2024). Sharpe 0.399.
- **ML-Pairs-PCA-Selection** (Book Ex09) : PCA-based pair selection. Research uniquement (notebook, pas de main.py).
- **ML-Chronos-Foundation** (Book Ex18) : Modele fondation Chronos-t5-tiny (Amazon) pour prevision de series temporelles. Allocation par Sharpe ratio predit. 8 ETFs.
- **ML-FinBERT-Sentiment** (Book Ex19) : ProsusAI/finbert pour sentiment de news financieres. TF non disponible sur QC Cloud, 0 trades. Reference pedagogique.
- **Positive-Negative-Splits-ML** (Book Ex07) : Prediction du rendement apres split par LinearRegression. Features: split factor, secteur momentum (XLK ROC 22j). Sharpe 1.736, CAGR 90.83%.
- **CSharp-BTC-MACD-ADX** : Variante C# de BTC-MACD-ADX avec recherches de robustesse. Meme algorithme, plus de documentation.
- **HMM-KMeans-Voting** : K-Means clustering custom (numpy pur) + HMM voting ensemble pour regime detection. Implementation pedagogique sans sklearn. Research uniquement.

### QC Strategy Library Clones (Avance)

Strategies clonees depuis la bibliotheque QuantConnect, ajoutees en avril 2026 comme references avancees :

- **AssetClassMomentum-QC** : Top-3 momentum annuel parmi 5 ETFs multi-asset (SPY/EFA/BND/VNQ/GSG). Equal-weight, rebalance mensuel. Source: Quantpedia Strategy #2.
- **DynamicVIXSpyRegime-QC** : RandomForest + StandardScaler ML overlay sur regime VIX. Universe SPY/TLT/GLD/BIL. OOS Sharpe 1.72. Source: QC Library #50.
- **HighBookToMarketFScore-QC** : Piotroski F-Score >= 8 + top 20% book-to-market. Value + quality screen. OOS Sharpe 2.09, Win Rate 62%. Source: QC Library #343.
- **LeveragedETFMomentum-QC** : Rotation sectorielle conditionnelle via ETFs leverages avec RSI + SMA regime detection. OOS Sharpe 1.80, CAGR 101%. Source: QC Library #60.
- **LongShortHarvest-QC** : Long-short equity avec ML overlay, regime detection Hurst, filtres ATR. OOS Sharpe 3.39, Win Rate 76%. Source: QC Library #238.
- **MacroFactorRotation-QC** : DecisionTreeRegressor cross-asset rotation (SPY/GLD/BND/BTC) avec features macro (VIX, yield curve, fed funds). Source: QC Library #72.
- **PuppiesOfTheDow-QC** : Dogs of the Dow : top-10 dividend yield, puis top-5 lowest priced. Annual rebalance. OOS Sharpe 1.99. Source: QC Library #211.
- **TermStructureCommodities-QC** : Long-short commodity futures par roll returns (backwardation = long, contango = short). 5Y Sharpe -0.041. Source: Quantpedia #22.

### Anomalies calendaires (Debutant)

- **TurnOfMonth** : Exploitation de l'anomalie "Turn of Month" (derniers/premiers jours du mois).

### Forex (Intermediaire)

- **ForexCarry** : Strategie momentum FX G10 risk-adjusted (IR + skip-month). Etendue 2013-2026.

## Structure d'un Projet

```
MonProjet/
+-- main.py / Main.cs    # Algorithme Python ou C# (deploye sur QC Cloud)
+-- alpha.py / helpers    # Modules auxiliaires (si applicable)
+-- research.ipynb        # Notebook de recherche exploratoire
+-- quantbook.ipynb       # Notebook QuantBook (donnees QC natives, optionnel)
+-- README.md             # Documentation (optionnel)
```

### Types de notebooks de recherche

| Type | Source de donnees | Avantage | Inconvenient |
|------|-------------------|----------|--------------|
| **yfinance** (standalone) | Yahoo Finance | Executable partout, pas besoin de QC | Divergences possibles avec QC (REITs, bond ETFs, dividendes) |
| **QuantBook** (QC native) | QuantConnect | Donnees identiques au backtest, memes indicateurs | Necessite l'environnement QC (Docker lean ou cloud) |

**Recommandation QC** : Passer plus de temps dans la recherche exploratoire (QuantBook) que dans les backtests d'algo.
Les notebooks yfinance restent utiles pedagogiquement (accessibles aux etudiants sans compte QC)
mais les conclusions doivent etre validees avec les donnees QC avant implementation.

## Lecons Apprises

Patterns transversaux decouverts pendant l'optimisation iterative :

### Risk Management
- **SL 6% minimum sur BTC daily** : 5% trop serre, la volatilite intraday declenche le stop
- **Trail breakeven a 3%** : protege les gains sans couper les gros moves
- **Stop-loss -8% a -12%** pour actions : reduit MaxDD sans tronquer les reversions
- **Profit target 50%** pour options (TastyTrade) + bande VIX 15-35

### Signal Quality
- **TLT risk-off detruit la valeur** sur 2015-2026 (hausse des taux 2022). Alternatives: XLP/IEF/GLD/cash
- **Risk-adjusted momentum** (return/vol) superieur au momentum brut
- **SMA50 >> SMA100 pour crypto** : SMA100 trop lent, filtre les bonnes entrees
- **1 parametre a la fois** : changer plusieurs params simultanement cause des regressions

### Portfolio Construction
- **Drift rebalancing 3%** > SMA overlay pour portfolios statiques
- **Monthly + regime-change rebalancing** > daily : reduit les trades de 80%
- **Vol window 60d > 20d** pour covariance min-var
- **Ne pas combiner risk-adj momentum + min-var** : double penalisation

### Technique QC
- **Binance Cash** : `set_account_currency("USDT")` + `set_cash(N)`
- **Options** : Resolution.MINUTE obligatoire (sinon chain vide)
- **1 backtest a la fois** sur un node QC
- **`read_file` AVANT `update_file_contents`** pour le collaboration lock

## Utilisation

### Sur QuantConnect Cloud

1. Creer un nouveau projet Python
2. Copier le contenu de `main.py` (et `channel_helpers.py` si present)
3. Lancer le backtest

### En Local (research)

```bash
pip install yfinance pandas matplotlib
jupyter notebook projects/MomentumStrategy/research.ipynb
```

## Ressources

- [QuantConnect Community](https://www.quantconnect.com/forum)
- [Algorithm Lab](https://www.quantconnect.com/terminal)
- [Documentation](https://www.quantconnect.com/docs)
