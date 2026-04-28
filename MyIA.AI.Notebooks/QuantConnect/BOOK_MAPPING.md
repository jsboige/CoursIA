# Hands-On AI Trading Book -> CoursIA Mapping

Reference mapping between the 22 examples from [Hands-On AI Trading with Python, QuantConnect, and AWS](https://github.com/QuantConnect/HandsOnAITradingBook) by Jared Broad and the CoursIA QuantConnect resources.

---

## Chapter 06: Applied Machine Learning (19 Examples)

| # | Book Example | Our Project | Notebook | Sharpe | CAGR | MaxDD | QC Cloud ID | Status |
|---|-------------|-------------|----------|--------|------|-------|-------------|--------|
| 01 | ML Trend Scanning with MLFinlab | `projects/ML-Trend-Scanning` | QC-Py-11, QC-Py-13 | 0.292 | -- | -- | -- | Done |
| 02 | Factor Preprocessing for Regime Detection | `projects/Markov-Regime-Detection`, `projects/HMM-KMeans-Voting` | QC-Py-28 | -- | -- | -- | -- | Done |
| 03 | Reversion vs Trending - Classification | `projects/ML-Reversion-Trending` | QC-Py-19 | 0.375 | 8.44% | 24.4% | 29398512 | Done |
| 04 | Alpha by Hidden Markov Models | `projects/ML-HMM-Regime` | QC-Py-28 | 0.571 | -- | -- | -- | Done |
| 05 | FX SVM Wavelet Forecasting | `projects/ML-FX-SVM-Wavelet`, `projects/SVM-Wavelet-Forecasting` | QC-Py-19 | 0.375 | 8.44% | 24.4% | -- | Done |
| 06 | Dividend Harvesting Selection | `projects/Dividend-Harvesting-ML` | QC-Py-05, QC-Py-13 | 0.468 | 12.66% | 30.6% | 29443034 | Done |
| 07 | Effect of Positive-Negative Splits | `projects/Positive-Negative-Splits-ML` | QC-Py-19 | 1.736 | 90.83% | 42.4% | 30317350 | Done |
| 08 | Stoploss Based on Volatility/Drawdown | `projects/Stoploss-Volatility-ML` | QC-Py-10, QC-Py-20 | 0.291 | 7.83% | 20.0% | 29463529 | Done |
| 09 | ML Trading Pairs Selection | `projects/ML-PCA-StatArb` | QC-Py-13 | N/A | -- | -- | -- | Done |
| 10 | Stock Selection by Clustering | `projects/Clustering-Fundamentals-ML` | QC-Py-19 | 0.244 | 7.68% | 44.8% | 30317074 | Done |
| 11 | Inverse Volatility Rank/Allocate | `projects/InverseVolatility-Rank` | QC-Py-10 | 0.124 | 4.13% | -- | 29463533 | Done |
| 12 | Trading Costs Optimization | `projects/TradingCosts-Optimization` | QC-Py-14 | N/A* | -- | -- | 29463540 | Done* |
| 13 | PCA Statistical Arbitrage | `projects/ML-PCA-StatArb`, `projects/PCA-StatArb` | QC-Py-13, QC-Py-24 | 0.399 | 12.65% | 31.8% | -- | Done |
| 14 | Temporal CNN Prediction | `projects/ML-Temporal-CNN`, `projects/Temporal-CNN-Prediction` | QC-Py-22 | 0.73** | -- | -- | -- | Done |
| 15 | Gaussian Classifier for Direction | `projects/ML-Gaussian-Classifier`, `projects/Gaussian-Direction-Classifier` | QC-Py-19 | 0.361 | 12.49% | 47.4% | -- | Done |
| 16 | LLM Summarization of Tiingo News | `projects/ML-LLM-Summarization` | QC-Py-26 | 0.686 | 15.45% | 22.7% | -- | Done |
| 17 | Head Shoulders Pattern CNN | `projects/ML-HeadShoulders-CNN` | QC-Py-22, QC-Py-23 | N/A*** | -- | -- | -- | Done |
| 18 | Amazon Chronos Model | `projects/ML-Chronos-Foundation`, `projects/Chronos-Foundation-Forecasting` | QC-Py-22 | 0.277 | 7.23% | 13.5% | -- | Done |
| 19 | FinBERT Model | `projects/ML-FinBERT-Sentiment` | QC-Py-17, QC-Py-26 | N/A**** | -- | -- | -- | Done |

**Footnotes:**
- *Ex12: Educational demo of ML cost prediction, not a standalone profitable strategy
- **Ex14: Sharpe from Temporal-CNN-Prediction variant
- ***Ex17: Requires pre-trained model from research.ipynb; backtest depends on model availability
- ****Ex19: TF model weights unavailable in QC Cloud; 0 trades generated

## Chapter 07: Reinforcement Learning (1 Example)

| # | Book Example | Our Project | Notebook | Status |
|---|-------------|-------------|----------|--------|
| 01 | RL Hedging Options | `projects/RL-DQN-Trading`, `projects/Reinforcement-Learning-Trading` | QC-Py-25, QC-Py-06 | **Partial** |

**Gap**: No dedicated RL-based options hedging project. Existing RL projects focus on equity trading (DQN), not options delta hedging. The book example trains an RL agent to minimize hedging cost vs Black-Scholes delta hedge.

## Chapter 08: Risk Management & Optimization (2 Examples)

| # | Book Example | Our Project | Notebook | Status |
|---|-------------|-------------|----------|--------|
| 01 | Conditional Portfolio Optimization | `projects/Portfolio-Optimization-ML` | QC-Py-21 | Done |
| 02 | Corrective AI Applied | -- | QC-Py-27 | **Gap** |

**Gap (Ex02)**: No dedicated corrective AI project. The book implements an AI system that learns from past prediction errors and applies corrections. QC-Py-27 covers production deployment but not the corrective AI pattern itself.

---

## Supporting Chapters

| Section | Book Directory | Our Notebooks | Status |
|---------|---------------|---------------|--------|
| 00 Libraries | `00 Libraries` | QC-Py-12, QC-Py-14 | Covered |
| 04 Dataset Preparation | `04 Step 2 - Dataset Preparation` (10 scripts) | QC-Py-03, QC-Py-18 | Covered |
| 05 Model Choice | `05 Step 3 - Model Choice` (10 scripts) | QC-Py-19, QC-Py-20 | Covered |

---

## Gap Analysis

### Critical Gaps (no dedicated project)

| Priority | Example | Description | Effort | Notes |
|----------|---------|-------------|--------|-------|
| HIGH | Ch07-01: RL Options Hedging | RL agent for delta hedging vs Black-Scholes benchmark | 4-6h | Requires options data pipeline + RL environment |
| MEDIUM | Ch08-02: Corrective AI | AI correction system from prediction errors | 3-4h | Needs a base strategy to apply corrections to |

### Quality Gaps (project exists, limited backtest)

| Priority | Example | Issue | Recommendation |
|----------|---------|-------|----------------|
| LOW | Ch06-01: ML Trend Scanning | Partial alignment with book | Enhance to use MLFinlab specifically |
| LOW | Ch06-17: Head Shoulders CNN | Needs pre-trained model | Add research.ipynb for model training |
| LOW | Ch06-19: FinBERT | TF incompatible with QC Cloud | Rewrite using PyTorch/transformers |

### Notebook Coverage

Our 28-notebook series (QC-Py-01 to QC-Py-28) covers the full book spectrum:
- **Chapters 00-05**: Covered by notebooks 01-20 (foundations through ML basics)
- **Chapter 06**: Covered by notebooks 17-26 (sentiment through LLM)
- **Chapter 07**: Partially covered by notebook 25 (RL)
- **Chapter 08**: Covered by notebooks 10, 21, 27 (risk, portfolio, deployment)

---

## Resources

- **Book**: [Hands-On AI Trading with Python, QuantConnect, and AWS](https://qnt.co/book-amazon)
- **Book Repo**: https://github.com/QuantConnect/HandsOnAITradingBook
- **Our Projects**: `MyIA.AI.Notebooks/QuantConnect/projects/`
- **Our Notebooks**: `MyIA.AI.Notebooks/QuantConnect/Python/`
- **Detailed Mapping**: `docs/HANDSON_AI_TRADING_MAPPING.md` (full notebook-level breakdown)

---

Version: 1.0 | Issue: #107 | Date: 2026-04-27
