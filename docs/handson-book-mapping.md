# Hands-On AI Trading — Book-to-Curriculum Mapping

**Book**: Hands-On AI Trading with Python, QuantConnect, and AWS (Pik, Chan, Broad, Sun, Singh — Wiley 2025)
**PDF**: `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\2025 - Hands_On_AI_Trading_with_Python_QuantCon.pdf`
**Context**: Issue #143, ML SOTA Curriculum (Issue #754)
**Date**: 2026-05-07

---

## Part I — Foundations of Capital Markets and Quantitative Trading

| Book Chapter | Pages | Topic | CoursIA Notebook | Notes |
|---|---|---|---|---|
| Ch1: Foundations of Capital Markets | 3-13 | Market mechanics, LOB, data feeds, brokerages, transaction costs, security identifiers | [QC-Py-01-Setup.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-01-Setup.ipynb), [QC-Py-02-Platform-Fundamentals.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-02-Platform-Fundamentals.ipynb) | QC platform basics overlap |
| Ch2: Assets and Derivatives | 15-23 | US equities, options, index options, futures, crypto | [QC-Py-06-Options-Trading.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-06-Options-Trading.ipynb), [QC-Py-07-Futures-Forex.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-07-Futures-Forex.ipynb) | Our notebooks go deeper on each asset class |
| Ch2 (cont): Foundations of Quantitative Trading | 25-44 | Research process, backtesting, parameter optimization, debugging, coding process, look-ahead bias | [QC-Py-03-Data-Management.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-03-Data-Management.ipynb), [QC-Py-04-Research-Workflow.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-04-Research-Workflow.ipynb), [QC-Py-12-Backtesting-Analysis.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-12-Backtesting-Analysis.ipynb) | Research workflow covered |
| Ch2 (cont): Strategy Styles | 29-33 | Trading signals, capital allocation, regimes, portfolios | [QC-Py-13-Alpha-Models.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-13-Alpha-Models.ipynb), [QC-Py-10-Risk-Portfolio-Management.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-10-Risk-Portfolio-Management.ipynb) | |
| Ch2 (cont): Parameter Sensitivity | 33-35 | Remove/Replace/Reduce, sensitivity testing | [QC-Py-15-Parameter-Optimization.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-15-Parameter-Optimization.ipynb) | Direct match |
| Ch2 (cont): Margin Modeling | 35-36 | Equities, options, futures margin | Partial — covered in QC-Py-06/07 | No dedicated margin notebook |
| Ch2 (cont): Diversification & Asset Selection | 37-41 | Fundamental, ETF constituents, dollar-volume, universe settings | [QC-Py-05-Universe-Selection.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-05-Universe-Selection.ipynb) | |
| Ch2 (cont): Indicators | 41-44 | Automatic/manual indicators, warm up, events | [QC-Py-11-Technical-Indicators.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-11-Technical-Indicators.ipynb) | Direct match |
| Ch2 (cont): Sourcing Ideas | 43-45 | Hypothesis testing, Quantpedia, QC Research Explorer | [QC-Py-04-Research-Workflow.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-04-Research-Workflow.ipynb) | |

---

## Part II — Foundations of AI and ML in Algorithmic Trading

| Book Section | Pages | Topic | CoursIA Notebook | Notes |
|---|---|---|---|---|
| Step 1: Problem Definition | 49 | Framing trading as ML problem | [QC-Py-18-ML-Features-Engineering.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-18-ML-Features-Engineering.ipynb) | |
| Step 2: Dataset Preparation | 49-82 | Data collection, EDA, preprocessing, missing data, outliers, feature engineering | [QC-Py-18-ML-Features-Engineering.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-18-ML-Features-Engineering.ipynb) | Extensive overlap |
| Normalization & Stationarity | 64-76 | Stationary transforms, cointegration (Engle-Granger) | [QC-Py-18-ML-Features-Engineering.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-18-ML-Features-Engineering.ipynb), [QC-Py-Cloud-04-MeanReversion.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-MeanReversion.ipynb) | Cointegration = mean reversion |
| Feature Selection & Dimensionality Reduction | 76-82 | Correlation, importance, auto-identification, PCA | [QC-Py-18-ML-Features-Engineering.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-18-ML-Features-Engineering.ipynb) | |
| Data Splitting | 82-83 | Train/test/validation splits | ML-Training-Pipeline wf_framework | Our walk-forward is more rigorous |
| Step 3: Model Choice — Regression | 83-110 | Linear, polynomial, LASSO, Ridge, Markov switching, decision tree, SVM+wavelet | [QC-Py-20-ML-Regression-Prediction.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-20-ML-Regression-Prediction.ipynb) | |
| Step 3: Classification | 110-130 | Random forest, logistic regression, HMM, Gaussian NB, CNN | [QC-Py-19-ML-Supervised-Classification.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-19-ML-Supervised-Classification.ipynb) | |
| Step 3: Ranking | 127-130 | LGBRanker | No dedicated notebook | GAP — potential new notebook |
| Step 3: Clustering | 130-132 | OPTICS clustering | No dedicated notebook | GAP — potential new notebook |
| Step 3: Language Models | 132-140 | OpenAI, Amazon Chronos, FinBERT | [QC-Py-26-LLM-Trading-Signals.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-26-LLM-Trading-Signals.ipynb), [QC-Py-Cloud-01-FinBERT-Sentiment.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-01-FinBERT-Sentiment.ipynb) | |

---

## Part III — Advanced Applications (19 Examples)

### Chapter 6: Applied Machine Learning

| # | Book Example | Pages | Topic | CoursIA Mapping | Status |
|---|---|---|---|---|---|
| 1 | ML Trend Scanning with MLFinlab | 143-148 | Trend scanning, CUSUM | No direct mapping | GAP — MLFinlab dependency |
| 2 | Factor Preprocessing for Regime Detection | 148-154 | Regime detection via factors | [QC-Py-28-Market-Regime-Detection.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-28-Market-Regime-Detection.ipynb) | OVERLAP |
| 3 | Reversion vs Trending Strategy Selection | 154-158 | Classification selects strategy style | [QC-Py-Cloud-04-MeanReversion.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-MeanReversion.ipynb), [QC-Py-Cloud-03-DualMomentum.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-03-DualMomentum.ipynb) | Partial |
| 4 | Alpha by Hidden Markov Models | 158-170 | HMM for alpha generation | [QC-Py-28-Market-Regime-Detection.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-28-Market-Regime-Detection.ipynb) | OVERLAP — HMM section |
| 5 | FX SVM Wavelet Forecasting | 170-176 | SVM + wavelet on FX | No FX-specific notebook | GAP — FX not covered |
| 6 | Dividend Harvesting Selection | 176-181 | ML for high-yield asset selection | No dividend notebook | GAP |
| 7 | Positive-Negative Splits Effect | 181-185 | ML analysis of return asymmetry | No direct mapping | GAP — niche topic |
| 8 | Stop Loss Based on Volatility & Drawdown | 185-197 | Volatility-adjusted stop loss | [QC-Py-10-Risk-Portfolio-Management.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-10-Risk-Portfolio-Management.ipynb) | Partial — risk management overlap |
| 9 | ML Trading Pairs Selection | 197-207 | ML-driven pairs trading | [QC-Py-Cloud-04-MeanReversion.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-MeanReversion.ipynb), [ESGF ETF-Pairs-Trading](../MyIA.AI.Notebooks/QuantConnect/ESGF-2026/examples/ETF-Pairs-Trading/) | OVERLAP |
| 10 | Stock Selection through Clustering | 207-214 | Clustering fundamental data | No clustering notebook | GAP |
| 11 | Inverse Volatility Rank & Allocate Futures | 214-221 | Vol-targeting futures portfolio | [QC-Py-Cloud-06-VolTargeting.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-06-VolTargeting.ipynb), [QC-Py-Cloud-03-Risk-Parity.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-03-Risk-Parity.ipynb) | OVERLAP |
| 12 | Trading Costs Optimization | 221-228 | Transaction cost modeling | No dedicated cost notebook | GAP — important topic |
| 13 | PCA Statistical Arbitrage Mean Reversion | 228-233 | PCA + stat arb | [QC-Py-Cloud-04-MeanReversion.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-MeanReversion.ipynb) | Partial |
| 14 | Temporal CNN Prediction | 233-242 | 1D-CNN for price prediction | [QC-Py-22-Deep-Learning-LSTM.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-22-Deep-Learning-LSTM.ipynb) | GAP — no CNN notebook |
| 15 | Gaussian Classifier for Direction Prediction | 242-250 | Gaussian NB for trading | [QC-Py-19-ML-Supervised-Classification.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-19-ML-Supervised-Classification.ipynb) | OVERLAP |
| 16 | LLM Summarization of Tiingo News | 250-256 | LLM for news summarization | [QC-Py-26-LLM-Trading-Signals.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-26-LLM-Trading-Signals.ipynb) | Partial |
| 17 | Head-Shoulders Pattern with CNN | 256-265 | CNN chart pattern recognition | No chart pattern notebook | GAP — image-based DL |
| 18 | Amazon Chronos Model | 265-272 | Foundation model forecasting | No Chronos notebook | GAP — foundation model |
| 19 | FinBERT Model | 272-281 | Sentiment via FinBERT | [QC-Py-Cloud-01-FinBERT-Sentiment.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-01-FinBERT-Sentiment.ipynb) | OVERLAP |

### Chapter 7: Better Hedging with Reinforcement Learning

| Book Section | Pages | Topic | CoursIA Mapping | Notes |
|---|---|---|---|---|
| RL for hedging | 281-303 | Policy network, simulation, refinement on market data, QC implementation | [QC-Py-25-Reinforcement-Learning.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-25-Reinforcement-Learning.ipynb), [QC-Py-32-RL-DQN-Trading.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-32-RL-DQN-Trading.ipynb), [QC-Py-Cloud-04-RL-DQN-Trading.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-RL-DQN-Trading.ipynb) | Book applies RL to hedging specifically; our notebooks focus on trading signals |

### Chapter 8: AI for Risk Management and Optimization

| Book Section | Pages | Topic | CoursIA Mapping | Notes |
|---|---|---|---|---|
| Corrective AI & Conditional Parameter Optimization | 303-322 | Daily seasonal FX, ETF strategy, unconditional vs conditional optimization | [QC-Py-15-Parameter-Optimization.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-15-Parameter-Optimization.ipynb) | Book uses PredictNow.ai corrective AI; our focus is QC native optimization |
| Conditional Portfolio Optimization (CPO) | 322-341 | Regime-aware portfolio optimization, ranking, Fama-French | [QC-Py-21-Portfolio-Optimization-ML.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-21-Portfolio-Optimization-ML.ipynb), [QC-Py-Cloud-01-RiskParity-Composite.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-01-RiskParity-Composite.ipynb) | |

### Chapter 9: LLMs and Generative AI in Trading

| Book Section | Pages | Topic | CoursIA Mapping | Notes |
|---|---|---|---|---|
| LLM for alpha, prompt engineering, RAG | 341-379 | Generative AI, hallucination, RAG in SageMaker, summarization, AI platforms | [QC-Py-26-LLM-Trading-Signals.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-26-LLM-Trading-Signals.ipynb) | Book uses AWS Bedrock/SageMaker; we use QC Cloud directly |

---

## Coverage Summary

| Category | Count | Percentage |
|---|---|---|
| **OVERLAP** (direct notebook match) | 19 | 51% |
| **Partial** (related but not exact) | 9 | 24% |
| **GAP** (no notebook coverage) | 9 | 24% |

### Gaps Worth Addressing (Priority Order)

1. **Temporal CNN (Ex14)** — Important DL architecture, would fit between LSTM and Transformer notebooks
2. **Amazon Chronos Foundation Model (Ex18)** — TSFM trend, aligned with our Stage 7 curriculum plans
3. **ML Trading Pairs Selection (Ex9)** — ML-enhanced pairs, extends existing pairs trading
4. **Clustering for Asset Selection (Ex10)** — Unsupervised ML for universe selection
5. **Trading Costs Optimization (Ex12)** — Practical transaction cost modeling
6. **FX SVM Wavelet (Ex5)** — SVM + signal processing, unique technique
7. **Chart Pattern CNN (Ex17)** — Image-based DL for pattern recognition
8. **MLFinlab Trend Scanning (Ex1)** — Requires MLFinlab license (commercial)
9. **Dividend Harvesting (Ex6)** — Niche, lower priority

### Topics Beyond Book Scope (Our Curriculum Extensions)

| Topic | CoursIA Notebook | Beyond Book |
|---|---|---|
| Walk-Forward Validation Framework | ML-Training-Pipeline/wf_framework | Anti-overfitting, expanding/rolling windows |
| Mamba/SSM Architectures | ML-Training-Pipeline/scripts/train_mamba.py | O(L) complexity, Stage 5 |
| MoE Regime-Aware Training | ML-Training-Pipeline/scripts/train_moe.py | Mixture of Experts, Stage 4 |
| PatchTST/iTransformer | [QC-Py-23b-PatchTST-iTransformer.ipynb](../MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-23b-PatchTST-iTransformer.ipynb) | Modern Transformer variants |
| Multi-Asset Walk-Forward | ML-Training-Pipeline/scripts/train_transformer.py --panier | Bonferroni-corrected multi-asset |
| Volatility Forecasting (GARCH+DL) | feat/ml-volatility-forecasting-garch-dl branch | Hybrid GARCH-DL, pivot from failed direction prediction |
| XGBoost/LightGBM/CatBoost Baselines | ML-Training-Pipeline/scripts/train_classification.py | Classical ML baselines with panier system |

---

## Book GitHub Repository

Examples at: https://github.com/QuantConnect/HandsOnAITrading (referenced in book)
Clone directly in QC Cloud for instant experimentation.
