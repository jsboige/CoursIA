# Stratégies QuantConnect — Descriptions Détaillées

Descriptions par catégorie des 116 projets de trading algorithmique. Pour le tableau de performance résumé, voir [README.md](README.md).

> **Lecture vérifiée sous frais réels (#1630, 2018-2025).** Les Sharpes ci-dessous sont des valeurs **catalogue (pré-frais, fenêtres variables)**. La campagne #1630 a re-vérifié 36+ stratégies sous frais IBKR réels sur une fenêtre alignée 2018-2025 — plusieurs s'effondrent, d'autres tiennent :

| Stratégie | Sharpe catalogue | Sharpe aligné | Verdict |
|-----------|------------------|---------------|---------|
| HighBookToMarketFScore | 2.09 | **0.41** | effondrement -80% (MaxDD -60%) |
| PuppiesOfTheDow | 1.99 | **0.30** | effondrement -85% |
| ML-Trend-Scanning | 0.66 | **0.33** | effondrement -50% |
| AllWeather | 0.67 | **0.47** | dégradation -30% |
| LongShortHarvest | 3.39 | **1.64** | tient (PSR 98.7%, le plus robuste) |
| TrendWeather | 1.16 | **0.948** | tient (PSR 56.6%, meilleur composite) |

Leaders vérifiés alignés (backbone no-ML) : **EMATrend 0.611** / **composite-c2 0.574**. Discriminateur : la résistance aux frais dépend du *realized-turnover* (fréquence × taille par trade × homogénéité des frais du panier), pas de l'asset-class. Catalogue complet + comparatifs best-vs-aligned + diagnostics par stratégie : [docs/qc/qc-comparative-backtests.md](../../../docs/qc/qc-comparative-backtests.md) (See #1630).

## EMA Crossover (Débutant)

- **EMA-Cross-Crypto** : Long BTCUSDT quand EMA20 > EMA50 ET BTC > SMA200 (filtre bull). Trailing stop 10%, position 80%. Binance Cash, daily.
- **EMA-Cross-Index** : Long SPY quand EMA20 > EMA60, flat sinon. Cooldown 3 jours après sortie. Daily.
- **EMA-Cross-Stocks** : Equal-weight portfolio de 5 tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA). Chaque stock est long individuellement quand son EMA20 > EMA50.
- **TrendStocksLite** : EMA20/50 + SMA200 filter sur 15 large-caps diversifiés (5 secteurs). Equal-weight hebdomadaire.
- **Multi-Layer-EMA** : EMA multi-couches sur BTCUSDT avec filtre de volatilité (seuil 60%). Allocation 100%. **NON ROBUSTE** : Sharpe chute à 0.38 hors bulle 2017.
- **CSharp-BTC-EMA-Cross** : EMA crossover BTC en C# avec paramètres (45, 120). Daily.

## Trend Following & Indicateurs Techniques (Intermédiaire/Avancé)

- **Trend-Following** : Multi-oracle scoring (MACD, RSI, Bollinger) + détection HH/HL/LL/LH + ATR trailing stop. Universe equity top 600. Multi-fichiers. Hourly resolution. ❌ Timeout (200 stocks × 11 ans hourly trop large).
- **BTC-MACD-ADX** : MACD + ADX filter sur BTC daily en C#. Sharpe 1.647, CAGR 38.1%.
- **CSharp-CTG-Momentum** : Momentum strategy avec indicateurs custom en C#.

## Momentum & Rotation (Intermédiaire)

- **SectorMomentum** : Dual Momentum d'Antonacci entre SPY/TLT/GLD. Lookback 12 mois.
- **MomentumStrategy** : Rotation mensuelle parmi 11 ETFs sectoriels, top-3 par momentum + stop-loss -10%.
- **FamaFrench** : Rotation trimestrielle entre 5 facteurs Fama-French (VLUE/MTUM/SIZE/QUAL/USMV).
- **DualMomentum** : Momentum absolu + relatif entre equities et bonds.
- **DualMomentumNoTLT** : Momentum rotation mensuelle sur SPY/QQQ/IEF/GLD/XLP (sans TLT). Top-2 par momentum 12M.
- **FuturesTrend** : Donchian breakout sur ETFs (trend following classique). Sharpe 0.136.

## Portfolio Construction (Intermédiaire/Avancé)

- **BlackLitterman-Momentum** : Framework Black-Litterman avec vues momentum multi-fenêtres sur 15 large-caps. Calibration Omega He & Litterman 1999, covariance Ledoit-Wolf shrinkage, contraintes sectorielles, vol targeting. Sharpe 0.604.
- **Framework_Composite_TrendWeather** : Composite TrendStocksLite + AllWeather via QC Algorithm Framework. T75/AW25 allocation, ROC63 momentum weighting, monthly rebalance. Itéré de v1.0 (Sharpe 0.622) à v1.5 (Sharpe 1.155).
- **Framework_Composite_FamaFrenchAllWeather** : Composite FamaFrench + AllWeather. Baseline FF50/AW50. **PENDING QC deployment**.
- **Framework_Composite_EMATrend** : Composite EMA-Cross + TrendStocks. EMA40/Trend60. Non backtestée.
- **Framework_Composite_MomentumRegime** : Composite SectorMomentum + RegimeSwitching. T60/RS40. Non backtestée.
- **AllWeather** : Portfolio "All Weather" simplifié (SPY 30%/IEF 30%/GLD 30%/XLP 10%, TLT éliminé). Drift rebalancing 3%.
- **RiskParity** : Allocation inversement proportionnelle à la volatilité. Plafond confirmé (3 hypothèses rejetées).
- **AdaptiveAssetAllocation** : Momentum + minimum-variance sur univers multi-asset.
- **RegimeSwitching** : Détection de régimes de marché (bull/bear/crisis) et rotation d'actifs.
- **EMA-Cross-Alpha** : Building block Framework Alpha : EMA 20/50 crossover (5 tech stocks).
- **TrendStocks-Alpha** : Building block Framework Alpha : EMA 20/50 + SMA200 trend filter (15 large-caps).

## Research & Tools (pas de backtest)

- **Alpha-Correlation-Analysis** : QuantBook notebook pour analyse de corrélation entre alphas complémentaires (issue #140).
- **ML-FeatureEngineering** : RF+GB ensemble feature engineering pipeline sur 15 large-caps. Sharpe 0.571, MaxDD 19.6%.

## Mean Reversion & Pairs (Intermédiaire)

- **MeanReversion** : Signaux RSI multi-asset, achat en survente, vente en surachat.
- **TrendFilteredMeanReversion** : RSI(2) pullback sur SPY conditionné par régime bull (SMA200). Time stop 5 jours. Signal réel (73% win) mais trop rare (~9 trades/an).
- **PairsTrading** : Arbitrage statistique sur paires d'actions cointégrées. Paires non cointégrées 2010-2026.
- **ETF-Pairs** : Cointegration-based pairs trading sur ETFs. Cointégration instable.

## Options & Volatilité (Avancé)

- **OptionsIncome** : Covered calls sur SPY avec filtre VIX (bande 15-35). Resolution MINUTE.
- **Option-Wheel** : Wheel strategy sur SPY (sell puts, si assigné sell calls). DTE 30, OTM 5%.
- **Options-VGT** : Covered calls sur VGT ETF (NVDA/ORCL/CSCO/AMD/QCOM). Resolution MINUTE.
- **VIX-TermStructure** : Trading de la structure à terme du VIX (contango/backwardation). Post-VIXplosion, SVXY affaibli.
- **Dynamic-Options-Wheel** : Extension du Option-Wheel avec sélection dynamique de strike basée sur IV percentile (2.5-7.5% OTM) et ajustement skew 25-delta.
- **Adaptive-Conformal-Risk** : Overlay de risque par inference conforme adaptive (ACI, Gibbs & Candes 2021) sur stratégie momentum multi-facteurs. 15 large-caps US.

## Crypto avancée (Avancé)

- **Crypto-MultiCanal** : 3 canaux ZigZag imbriqués (macro/meso/micro) sur BTCUSDT. ❌ Runtime Error : cannot import 'find_envelope_line'.
- **BTC-ML** : Prediction BTC par machine learning (features techniques + filtre volatilité 60%). Période courte 2023-2026.
- **Crypto-LSTM-Prediction** : Deep Learning DLinear (AAAI 2023) pour prédiction BTCUSDT. PyTorch. **Research Phase**.

## Machine Learning / Deep Learning / RL (Intermédiaire/Avancé)

Stratégies ML/AI implémentées avec `sklearn` (compatible QC Cloud). Basées sur le livre *Hands-On AI Trading* de Jared Broad et implémentations internes.

| Projet | Description | Sharpe | Book Ref |
|--------|-------------|--------|----------|
| [Positive-Negative-Splits-ML](Positive-Negative-Splits-ML/) | LinearRegression split-event return prediction | **1.736** | Ch06-Ex07 |
| [ML-Temporal-CNN](ML-Temporal-CNN/) | Conv1D Keras CNN direction prediction (QQQ top-3) | **0.734** | Ch06-Ex14 |
| [ML-LLM-Summarization](ML-LLM-Summarization/) | Tiingo news sentiment + optional OpenAI LLM | **0.686** | Ch06-Ex16 |
| [ML-RandomForest](ML-RandomForest/) | RF classification multi-asset (8 ETFs) | **0.682** | — |
| [ML-Trend-Scanning](ML-Trend-Scanning/) | t-statistic regression slope multi-windows | **0.656** | Ch06-Ex01 |
| [Portfolio-Optimization-ML](Portfolio-Optimization-ML/) | Markowitz + ML returns prediction | **0.896** | — |
| [CausalEventAlpha](CausalEventAlpha/) | CATE sector rotation via DML proxy + GB | **0.779** | — |
| [Gaussian-Direction-Classifier](Gaussian-Direction-Classifier/) | Gaussian classifier direction, prob-weighted | **0.761** | Ch06-Ex15 |
| [ML-FeatureEngineering](ML-FeatureEngineering/) | RF+GB ensemble feature engineering pipeline | **0.571** | — |
| [ML-XGBoost](ML-XGBoost/) | XGBoost gradient boosting (9 positions, biweekly) | **0.566** | — |
| [Markov-Regime-Detection](Markov-Regime-Detection/) | Markov-switching dynamic regression 2-regime | **0.571** | Ch06-Ex04 |
| [Temporal-CNN-Prediction](Temporal-CNN-Prediction/) | MLP multi-scale temporal features (8 ETFs) | **0.536** | Ch06-Ex14 |
| [RL-DQN-Trading](RL-DQN-Trading/) | DQN portfolio-level actions (MLPRegressor) | **0.533** | Ch07-Ex01 |
| [LSTM-Forecasting](LSTM-Forecasting/) | MLP temporal features multi-ETF (7 assets) | **0.525** | Ch06-Ex07 |
| [Sector-ML-Classification](Sector-ML-Classification/) | RF rank classifier rotation sectorielle | **0.473** | — |
| [Dividend-Harvesting-ML](Dividend-Harvesting-ML/) | DecisionTree dividend yield prediction | **0.469** | Ch06-Ex06 |
| [ML-Reversion-Trending](ML-Reversion-Trending/) | GB regime classifier (mean-revert vs trend) | **0.292** | Ch06-Ex03 |
| [Chronos-Foundation-Forecasting](Chronos-Foundation-Forecasting/) | GBM+Ridge ensemble forecasting | **0.253** | Ch06-Ex18 |
| [ML-Chronos-Foundation](ML-Chronos-Foundation/) | Chronos-t5-tiny foundation model allocation | **0.277** | Ch06-Ex18 |
| [ML-Gaussian-Classifier](ML-Gaussian-Classifier/) | GaussianNB direction prediction tech stocks | **0.361** | Ch06-Ex15 |
| [ML-FX-SVM-Wavelet](ML-FX-SVM-Wavelet/) | SVR + wavelet 4 Forex pairs (leverage 20x) | **0.167** | Ch06-Ex05 |
| [ML-SVM](ML-SVM/) | SVM linear kernel equity-only ETFs | **0.147** | — |
| [InverseVolatility-Rank](InverseVolatility-Rank/) | Ridge regression inverse-vol futures | **0.212** | Ch06-Ex11 |
| [PCA-StatArbitrage](PCA-StatArbitrage/) | PCA + LinearRegression stat-arb mean reversion | **0.399** | Ch06-Ex13 |
| [Adaptive-Conformal-Risk](Adaptive-Conformal-Risk/) | ACI risk overlay multi-factor momentum | **0.423** | — |
| [Dynamic-Options-Wheel](Dynamic-Options-Wheel/) | Dynamic delta/skew options wheel (SPY) | **0.119** | — |

### Non backtestées / Research

- [ML-Classification](ML-Classification/) : RF direction J+1 (ObjectStore model)
- [ML-Regression](ML-Regression/) : Ridge prediction returns J+1 (20 stocks)
- [ML-Ensemble](ML-Ensemble/) : Ensemble Ridge/RF/LightGBM, 30 large-caps
- [ML-EnhancedPairs](ML-EnhancedPairs/) : ML-enhanced pairs trading
- [ML-DeepLearning](ML-DeepLearning/) : LSTM/GRU prediction (PyTorch)
- [DL-LSTM](DL-LSTM/) : LSTM bidirectionnel pré-entraîné (PyTorch)
- [ML-TextClassification](ML-TextClassification/) : NLP Naive Bayes sentiment simulé
- [RL-Portfolio](RL-Portfolio/) : Q-Learning allocation multi-asset
- [Reinforcement-Learning-Trading](Reinforcement-Learning-Trading/) : DQN experience replay (book implementation)
- [SVM-Wavelet-Forecasting](SVM-Wavelet-Forecasting/) : SVM + wavelet FX (local only)
- [ML-Pairs-PCA-Selection](ML-Pairs-PCA-Selection/) : PCA pair selection (research only)
- [Clustering-Fundamentals-ML](Clustering-Fundamentals-ML/) : PCA + GBR fundamental ranking. Runtime Error.
- [Stoploss-Volatility-ML](Stoploss-Volatility-ML/) : Lasso stop-loss optimization. BROKEN (CBOE data unavailable).
- [TradingCosts-Optimization](TradingCosts-Optimization/) : DecisionTree crypto cost optimization. Quasi flat.
- [ML-HeadShoulders-CNN](ML-HeadShoulders-CNN/) : CNN Head & Shoulders detection USDCAD. Échec de généralisation synthétique → réel.
- [ML-FinBERT-Sentiment](ML-FinBERT-Sentiment/) : FinBERT sentiment. TF unavailable on QC Cloud, 0 trades.

### Consolidated (code merged)

- ~~PCA-StatArb~~ → [PCA-StatArbitrage](PCA-StatArbitrage/) (statsmodels version non compatible QC)
- ~~ML-HMM-Regime~~ → [Markov-Regime-Detection](Markov-Regime-Detection/) (code identique)
- ~~ML-PCA-StatArb~~ → [PCA-StatArbitrage](PCA-StatArbitrage/) (code identique)

## QC Strategy Library Clones (Avancé)

Références avancées clonées depuis la QC Cloud Library (avril 2026). Métriques OOS de la QC Strategy Library (non re-backtestées localement).

| Projet | Description | OOS Sharpe | 5Y CAGR | Source |
|--------|-------------|------------|---------|--------|
| [LongShortHarvest-QC](LongShortHarvest-QC/) | Long-short equity ML overlay, Hurst regime | **3.39** | 57.94% | QC Library #238 |
| [HighBookToMarketFScore-QC](HighBookToMarketFScore-QC/) | Piotroski F-Score >= 8 + book-to-market | **2.09** | 18.44% | QC Library #343 |
| [PuppiesOfTheDow-QC](PuppiesOfTheDow-QC/) | Dogs of the Dow value-income tilt | **1.99** | 10.16% | QC Library #211 |
| [LeveragedETFMomentum-QC](LeveragedETFMomentum-QC/) | RSI + SMA leveraged ETF rotation | **1.80** | 101.03% | QC Library #60 |
| [DynamicVIXSpyRegime-QC](DynamicVIXSpyRegime-QC/) | RF + VIX regime switching | **1.72** | 29.76% | QC Library #50 |
| [MacroFactorRotation-QC](MacroFactorRotation-QC/) | DecisionTree cross-asset rotation | **1.23** | 33.45% | QC Library #72 |
| [AssetClassMomentum-QC](AssetClassMomentum-QC/) | Top-3 momentum 5 ETFs | — | — | Quantpedia #2 |
| [TermStructureCommodities-QC](TermStructureCommodities-QC/) | Commodity futures roll returns | -0.041 | -15.71% | Quantpedia #22 |

## Anomalies calendaires (Débutant)

- **TurnOfMonth** : Anomalie "Turn of Month" (derniers/premiers jours du mois). Effet faible en bull 2015-2026.

## Forex (Intermédiaire)

- **ForexCarry** : Momentum FX G10 risk-adjusted (IR + skip-month). Étendue 2013-2026. CAGR < T-bills, carry prime évaporée.

## Research (hors backtest)

- **HMM-KMeans-Voting** : K-Means clustering custom (numpy pur) + HMM voting ensemble pour regime detection. Implémentation pédagogique sans sklearn. Research notebook uniquement.

---

Voir aussi : [README.md](README.md) (résumé) · [Leçons](../../../docs/qc/quantconnect.md) · [Catalogue QC Cloud](../docs/qc_strategies_catalog.md)
