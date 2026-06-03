# Hands-On AI Trading — Book-to-Series Mapping

Maps the 63 examples (71 deliverables) from [HandsOnAITradingBook](https://github.com/QuantConnect/HandsOnAITradingBook) (Jared Broad) to our QuantConnect notebooks and projects.

Status: `COVERED` = we have equivalent content, `PARTIAL` = partial coverage, `GAP` = no equivalent.

---

## Ch04 — Dataset Preparation (21 scripts)

All standalone Python scripts using synthetic data. Not QuantConnect algorithms.

| # | Book Example | ML Technique | Our Resource | Status |
|---|-------------|-------------|-------------|--------|
| 01 | ExploratoryDataAnalysis (Sweetviz) | EDA | QC-Py-03 Data Management | PARTIAL |
| 02 | IdentifyingMissingData | NaN detection | QC-Py-03 | PARTIAL |
| 03 | BoxPlotOutliers | Box plot | — | GAP |
| 04 | ZScoreOutliers | Z-score | — | GAP |
| 05 | IQROutliers | IQR | — | GAP |
| 06 | RemovingOutliers | Filter Z<=2 | — | GAP |
| 07 | TransformingOutliers | Log transform | — | GAP |
| 08 | CappingFlooringOutliers | Winsorization | — | GAP |
| 09 | FeatureEngineering | MA, RSI, BB, lagged returns | **QC-Py-18 ML Features Engineering** | COVERED |
| 10 | Normalization | MinMaxScaler | QC-Py-18 | PARTIAL |
| 11 | Standardization | StandardScaler | QC-Py-18 | PARTIAL |
| 12 | StationaryTransform | Differencing + ADF | QC-Py-18 | PARTIAL |
| 13 | ADFTest + FracDiff | ADF + fractional diff (Lopez de Prado) | — | GAP |
| 14 | EngleGrangerTest | Cointegration | **PairsTrading/research.ipynb** | COVERED |
| 15 | HurstCoefficient | Mean-reverting vs trending | — | GAP |
| 16 | CorrelationAnalysis | Pearson + heatmap | QC-Py-03 | PARTIAL |
| 17 | FeatureImportance (RF) | RF importance + corr drop | QC-Py-18 | PARTIAL |
| 18 | AutoIdentificationFeatures (RFE) | Recursive Feature Elimination | — | GAP |
| 19 | PCA | Principal Components | **QC-Py-21 Portfolio Optimization ML** | COVERED |
| 20 | DataSplit | Train/test 80/20 | QC-Py-18 (implicit) | PARTIAL |
| 21 | KFoldCrossValidation | 5-fold CV + RF | QC-Py-15 Parameter Optimization | PARTIAL |

**Coverage**: 3 COVERED, 13 PARTIAL, 5 GAP.
**Priority gaps**: FracDiff (#13), Hurst (#15), RFE (#18), outlier methods (#03-08).

---

## Ch05 — Model Choice (18 scripts)

Standalone ML scripts using synthetic data.

| # | Book Example | Model Family | Our Resource | Status |
|---|-------------|-------------|-------------|--------|
| 01 | LinearRegression | Regression | **QC-Py-20 ML Regression Prediction** | COVERED |
| 02 | PolynomialRegression | Poly degree 2 | — | GAP |
| 03 | LassoRegression | L1 regularization | — | GAP |
| 04 | RidgeRegression | L2 regularization | — | GAP |
| 05 | MarkovSwitchingDynamicRegression | Regime switching (statsmodels) | **QC-Py-Cloud-05 RegimeSwitching** | COVERED |
| 06 | DecisionTreeRegression | DT regressor | — | GAP |
| 07 | SVMWaveletForecasting | SVR + wavelet | — | GAP |
| 08 | SVRGridSearch | SVR hyperopt | — | GAP |
| 09 | MulticlassRF (LightGBM) | Gradient boosting | **projects/ML-XGBoost** | PARTIAL |
| 10 | LogisticRegression | Binary classification | — | GAP |
| 11 | HiddenMarkovModels | GaussianHMM (hmmlearn) | **QC-Py-Cloud-05 RegimeSwitching** | COVERED |
| 12 | GaussianNaiveBayes | GNB classification | — | GAP |
| 13 | CNN + LSTM | Deep learning (Keras) | **QC-Py-30 LSTM Training**, **QC-Py-31 Transformer Training** | COVERED |
| 14 | LGBRanker | Learning-to-rank | **projects/ML-RandomForest**, **projects/ML-XGBoost** | PARTIAL |
| 15 | OPTICSClustering | Density clustering | — | GAP |
| 16 | OpenAILanguageModel | GPT-4 sentiment | **QC-Py-17 Sentiment Analysis** | COVERED |
| 17 | AmazonChronosModel | Chronos-T5 forecasting | **projects/Chronos-Foundation-Forecasting** | COVERED |
| 18 | FinBERTModel | FinBERT NLP | **QC-Py-Cloud-01-FinBERT-Sentiment** | COVERED |

**Coverage**: 7 COVERED, 2 PARTIAL, 9 GAP.
**Priority gaps**: Lasso/Ridge (#03-04), DT (#06), SVM+Wavelet (#07-08), GNB (#12), OPTICS (#15). Lower priority: PolyReg (#02), Logistic (#10).

---

## Ch06 — Applied Machine Learning (19 examples, 27 sub-items)

Full QuantConnect LEAN algorithms using real market data. Core chapter.

| # | Book Example | Technique | Our Resource | Status |
|---|-------------|-----------|-------------|--------|
| 01 | ML Trend Scanning (MLFinLab) | Trend labels + BTC | — | GAP (requires MLFinLab license) |
| 02 | Factor Preprocessing Regime Detection | RF + factor engineering | **RegimeSwitching/research.ipynb** | PARTIAL |
| 03 | Reversion vs Trending Classification | NN momentum/reversion | **TrendFilteredMeanReversion/** | PARTIAL |
| 04/01 | HMM Equities (SPY/TLT) | Markov regime | **RegimeSwitching/**, **DynamicVIXSpyRegime-QC** | COVERED |
| 04/02 | HMM Equity Options (SPY) | Regime + options | **Options-VGT/** | PARTIAL |
| 04/03 | HMM Index Options (SPX) | Regime + index options | — | GAP |
| 05 | FX SVM Wavelet Forecasting | SVR + wavelet + forex | — | GAP |
| 06 | Dividend Harvesting | DT regression + yields | — | GAP |
| 07 | Stock Splits Effect | Linear regression | — | GAP |
| 08/01 | Fixed Stop Loss (benchmark) | No ML | **QC-Py-09 Order Types** | PARTIAL |
| 08/02 | ML Placed Stop Loss | Lasso + VIX/ATR | — | GAP |
| 08/03 | ML Put Option Hedge | Lasso + options hedge | — | GAP |
| 09 | ML Pairs Selection | PCA + OPTICS + cointegration | **PairsTrading/** | COVERED |
| 10 | Stock Selection Clustering | PCA + LGBMRanker | **projects/SectorMomentum/** | COVERED |
| 11 | Inverse Vol Futures | Ridge + futures | — | GAP |
| 12 | Trading Costs Optimization | DT regression + BTC | — | GAP |
| 13 | PCA Statistical Arbitrage | PCA + mean reversion | — | GAP |
| 14 | Temporal CNN Prediction | 1D-CNN + QQQ | **projects/Temporal-CNN-Prediction** | COVERED |
| 15 | Gaussian Classifier Direction | GNB + tech sector | — | GAP |
| 16 | LLM Tiingo News Summarization | GPT + TSLA | **QC-Py-Cloud-01-FinBERT-Sentiment** | PARTIAL |
| 17 | Head Shoulders CNN Pattern | CNN + USDCAD | — | GAP |
| 18/01 | Chronos Base Model | Chronos-T5 + portfolio | **projects/Chronos-Foundation-Forecasting** | COVERED |
| 18/02 | Chronos Fine-Tuned | Chronos fine-tune | **projects/Chronos-Foundation-Forecasting** | COVERED |
| 19/01 | FinBERT Base Model | FinBERT + volatile stocks | **QC-Py-Cloud-01-FinBERT-Sentiment** | COVERED |
| 19/02 | FinBERT Fine-Tuned | FinBERT fine-tune | — | GAP |

**Coverage**: 9 COVERED, 5 PARTIAL, 13 GAP.
**Priority gaps**: SVM Wavelet (#05), Dividend Harvesting (#06), ML Stop Loss (#08/02-03), PCA Stat Arb (#13), Trading Costs (#12). Nice-to-have: HMM Index Options (#04/03), Head Shoulders CNN (#17), FX specific (#05).

---

## Ch07 — Reinforcement Learning (1 example)

| # | Book Example | Technique | Our Resource | Status |
|---|-------------|-----------|-------------|--------|
| 01 | RL Hedging Options (AAPL) | Policy Gradient + delta hedging | **QC-Py-32 RL DQN Trading**, **QC-Py-33 RL PPO Trading**, **projects/Reinforcement-Learning-Trading** | PARTIAL |

**Coverage**: 0 COVERED, 1 PARTIAL, 0 GAP.
**Gap analysis**: Our RL notebooks cover DQN/PPO/SAC/A2C for equity trading, but NOT options delta hedging. The book's approach (PyTorch policy gradient for delta prediction) is unique.

---

## Ch08 — Risk Management & Optimization (2 examples)

| # | Book Example | Technique | Our Resource | Status |
|---|-------------|-----------|-------------|--------|
| 01 | Conditional Portfolio Optimization | PredictNow.ai CPO (external) | **RiskParity/**, **QC-Py-10 Risk Portfolio Mgmt** | PARTIAL |
| 02 | Corrective AI (EURUSD) | PredictNow.ai CAI (external) | — | GAP |

**Coverage**: 0 COVERED, 1 PARTIAL, 1 GAP.
**Note**: Both rely on PredictNow.ai external API (paid service). Our RiskParity covers optimization concepts without external dependency.

---

## Shared Libraries (00)

| Module | Content | Our Equivalent | Status |
|--------|---------|---------------|--------|
| backtestlib | `rough_daily_backtest()` equity curve | QC-Py-12 Backtesting Analysis | COVERED |
| tearsheet | Performance plot generation | QC-Py-12 + QC framework | COVERED |

---

## Summary

| Chapter | COVERED | PARTIAL | GAP | Total |
|---------|---------|---------|-----|-------|
| Ch04 Dataset Preparation | 3 | 13 | 5 | 21 |
| Ch05 Model Choice | 7 | 2 | 9 | 18 |
| Ch06 Applied ML | 9 | 5 | 13 | 27 |
| Ch07 RL Hedging | 0 | 1 | 0 | 1 |
| Ch08 Risk Management | 0 | 1 | 1 | 2 |
| Shared Libraries | 2 | 0 | 0 | 2 |
| **Total** | **21** | **22** | **28** | **71** |

**Coverage rate**: 30% COVERED, 31% PARTIAL, 39% GAP.

---

## Priority Gaps (recommended additions)

### Tier 1 — High value, complements existing content

| Gap | Book Example | Why valuable | Suggested notebook |
|-----|-------------|-------------|-------------------|
| FracDiff stationarity | Ch04 #13 | Core technique (Lopez de Prado Advances in Financial ML) | QC-Py-18b or extend QC-Py-18 |
| Hurst exponent | Ch04 #15 | Mean-reverting vs trending classification | Extend QC-Py-18 or PairsTrading |
| Outlier detection suite | Ch04 #03-08 | Data cleaning pipeline | QC-Py-18c or extend QC-Py-18 |
| Lasso/Ridge regression | Ch05 #03-04 | Regularization basics for quant | QC-Py-20b or extend QC-Py-20 |
| SVM + Wavelet forecasting | Ch06 #05 | Unique hybrid signal processing | QC-Py-24 (new) |
| ML Stop Loss placement | Ch06 #08/02-03 | Practical risk management | QC-Py-10b or extend QC-Py-10 |
| PCA Statistical Arbitrage | Ch06 #13 | Classic quant strategy | QC-Py-25 (new) |
| Trading Costs optimization | Ch06 #12 | Execution quality | QC-Py-26 (new) |

### Tier 2 — Nice to have, specialized domains

| Gap | Book Example | Why valuable | Notes |
|-----|-------------|-------------|-------|
| RL Options Hedging | Ch07 #01 | Unique RL application | Needs options data + PyTorch |
| HMM Index Options | Ch06 #04/03 | Options + regime | European-style SPX specific |
| Head Shoulders CNN | Ch06 #17 | Pattern recognition | Image-like chart processing |
| Dividend Harvesting | Ch06 #06 | Fundamental + ML | Requires dividend data |
| FinBERT Fine-Tuned | Ch06 #19/02 | NLP advanced | Labeled dataset construction |
| Chronos Fine-Tuned | Ch06 #18/02 | Foundation model tuning | Already partially in our Chronos project |
| DecisionTreeRegression | Ch05 #06 | Interpretable ML | Basic, gap in curriculum |
| GaussianNaiveBayes | Ch05 #12 | Simple classifier | Basic, gap in curriculum |
| OPTICS Clustering | Ch05 #15 | Advanced clustering | Complements PCA coverage |
| RFE Feature Selection | Ch04 #18 | Auto feature selection | Complements QC-Py-18 |

### Tier 3 — External dependency or niche

| Gap | Book Example | Notes |
|-----|-------------|-------|
| ML Trend Scanning | Ch06 #01 | Requires MLFinLab license |
| PredictNow.ai CPO/CAI | Ch08 #01-02 | External paid API |
| FX SVM Wavelet | Ch06 #05 | Forex-specific, could adapt to equity |
| Stock Splits | Ch06 #07 | Event-driven, niche |

---

## Cross-references

- Our QC Python series: `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-XX`
- Our QC projects: `MyIA.AI.Notebooks/QuantConnect/projects/`
- Book repo: https://github.com/QuantConnect/HandsOnAITradingBook
- Book website: https://www.hands-on-ai-trading.com/
