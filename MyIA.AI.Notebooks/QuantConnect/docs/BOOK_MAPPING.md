# Hands-On AI Trading Book -> CoursIA Mapping

Reference mapping between the 22 examples from [Hands-On AI Trading with Python, QuantConnect, and AWS](https://github.com/QuantConnect/HandsOnAITradingBook) by Jared Broad and the CoursIA QuantConnect resources.

---

## Chapter 06: Applied Machine Learning (19 Examples)

| # | Book Example | Our Project | Notebook | Sharpe | CAGR | MaxDD | QC Cloud ID | Status |
|---|-------------|-------------|----------|--------|------|-------|-------------|--------|
| 01 | ML Trend Scanning with MLFinlab | `projects/ML-Trend-Scanning` | QC-Py-11, QC-Py-13 | 0.292 | -- | -- | -- | Done |
| 02 | Factor Preprocessing for Regime Detection | `projects/Markov-Regime-Detection`, `projects/HMM-KMeans-Voting` | QC-Py-28 | -- | -- | -- | -- | Done |
| 03 | Reversion vs Trending - Classification | `projects/ML-Reversion-Trending` | QC-Py-19 | 0.375 | 8.44% | 24.4% | 29398512 | Done |
| 04 | Alpha by Hidden Markov Models | `projects/Markov-Regime-Detection` | QC-Py-28 | 0.571 | -- | -- | -- | Done |
| 05 | FX SVM Wavelet Forecasting | `projects/ML-FX-SVM-Wavelet`, `projects/SVM-Wavelet-Forecasting` | QC-Py-19 | 0.375 | 8.44% | 24.4% | -- | Done |
| 06 | Dividend Harvesting Selection | `projects/Dividend-Harvesting-ML` | QC-Py-05, QC-Py-13 | 0.468 | 12.66% | 30.6% | 29443034 | Done |
| 07 | Effect of Positive-Negative Splits | `projects/Positive-Negative-Splits-ML` | QC-Py-19 | 1.736 | 90.83% | 42.4% | 30317350 | Done |
| 08 | Stoploss Based on Volatility/Drawdown | `projects/Stoploss-Volatility-ML` | QC-Py-10, QC-Py-20 | 0.291 | 7.83% | 20.0% | 29463529 | Done |
| 09 | ML Trading Pairs Selection | `projects/PCA-StatArbitrage` | QC-Py-13 | N/A | -- | -- | -- | Done |
| 10 | Stock Selection by Clustering | `projects/Clustering-Fundamentals-ML` | QC-Py-19 | 0.244 | 7.68% | 44.8% | 30317074 | Done |
| 11 | Inverse Volatility Rank/Allocate | `projects/InverseVolatility-Rank` | QC-Py-10 | 0.124 | 4.13% | -- | 29463533 | Done |
| 12 | Trading Costs Optimization | `projects/TradingCosts-Optimization` | QC-Py-14 | N/A* | -- | -- | 29463540 | Done* |
| 13 | PCA Statistical Arbitrage | `projects/PCA-StatArbitrage` | QC-Py-13, QC-Py-24 | 0.399 | 12.65% | 31.8% | -- | Done |
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

| # | Book Example | Our Project | Notebook | Sharpe | CAGR | MaxDD | QC Cloud ID | Status |
|---|-------------|-------------|----------|--------|------|-------|-------------|--------|
| 01 | RL Hedging Options | `RL-Options-Hedging` (Deep Hedging) | QC-Py-25 | -1.264 | -- | -- | 30800109 | **Deployed** |

**Extended implementations:**

| Project | Variant | Sharpe | Cloud ID | Description |
|---------|---------|--------|----------|-------------|
| `RL-DQN-Trading` | DQN portfolio-level | 0.533 | 29443478 | MLPRegressor(64,32), 3 action templates, 5 ETFs |
| `Reinforcement-Learning-Trading` | DQN experience replay | --- | -- | Template/skeleton (pedagogical variant) |
| `RL-Portfolio` | RL portfolio opt | --- | -- | Template/skeleton |

**Analysis**: The book's single Ch07 example (RL for options hedging) is implemented as a dedicated project with research notebook. The RL-DQN-Trading variant extends beyond the book's scope with portfolio-level DQN actions. Both have cloud deployments. Options hedging variant has negative Sharpe (-1.264) — expected for RL learning curves on options. The DQN variant achieves 0.533 Sharpe.

**QC Notebooks**: QC-Py-25 (Reinforcement Learning) covers the conceptual foundation. QC-Py-32/33/34 were planned for DQN/PPO/SAC extensions but not yet created as separate notebooks.

## Chapter 08: Risk Management & Optimization (2 Examples)

| # | Book Example | Our Project | Notebook | Sharpe | CAGR | MaxDD | QC Cloud ID | Status |
|---|-------------|-------------|----------|--------|------|-------|-------------|--------|
| 01 | Conditional Portfolio Optimization | `Portfolio-Optimization-ML` | QC-Py-21 | 0.896 | -- | -- | 29318874 | Done |
| 02 | Corrective AI Applied | `Corrective-AI` | QC-Py-27 (linked) | -0.151 | 2.22% | 11.3% | 30800636 | **Deployed** |

**Analysis (Ex02)**: Dedicated Corrective-AI project now exists with cloud deployment. Meta-labeling approach: primary SMA crossover + corrective filter. 70% win rate but negative Sharpe — average loss (-0.18%) exceeds average win (0.12%). Multi-asset (SPY/TLT/GLD) diversification present but SMA lag hurts in sideways markets. Research notebook includes signal reduction analysis.

**Quality assessment**: Both Ch08 examples have cloud deployments. Portfolio-Optimization-ML performs well (0.896 Sharpe). Corrective-AI underperforms but is structurally sound — needs position sizing/timing improvements, not fundamental redesign.

---

## Supporting Chapters

| Section | Book Directory | Our Notebooks | Status |
|---------|---------------|---------------|--------|
| 00 Libraries | `00 Libraries` | QC-Py-12, QC-Py-14 | Covered |
| 04 Dataset Preparation | `04 Step 2 - Dataset Preparation` (10 scripts) | QC-Py-03, QC-Py-18 | Covered |
| 05 Model Choice | `05 Step 3 - Model Choice` (10 scripts) | QC-Py-19, QC-Py-20 | Covered |

---

## Gap Analysis

### Cycle 7 Progress (2026-05-07)

- **ML Training Pipeline**: GNN walk-forward 5-fold x 5 seeds completed (EPIC #754 closed — all models NO BEATS on direction prediction)
- **Volatility Pivot**: Per research study (#779), DL strength in finance is volatility modeling, not direction. Regime classifier LSTM h=64 in progress (Track A).
- **RL Series**: QC-Py-32 DQN done, QC-Py-33 PPO + QC-Py-34 SAC/A2C planned

### Resolved Gaps (Ch07+Ch08 audit, 2026-05-12)

| Example | Previous Status | Current Status | Resolution |
|---------|----------------|----------------|------------|
| Ch07-01: RL Options Hedging | HIGH gap | **Deployed** (Sharpe -1.264, 5 BTs) | Project `RL-Options-Hedging` + `RL-DQN-Trading` + research notebooks |
| Ch08-02: Corrective AI | MEDIUM gap | **Deployed** (Sharpe -0.151, 2 BTs) | Project `Corrective-AI` with meta-labeling + research notebook |

### Remaining Quality Gaps (project exists, limited backtest)

| Priority | Example | Issue | Recommendation |
|----------|---------|-------|----------------|
| LOW | Ch06-01: ML Trend Scanning | Partial alignment with book | Enhance to use MLFinlab specifically |
| LOW | Ch06-17: Head Shoulders CNN | Needs pre-trained model | Add research.ipynb for model training |
| LOW | Ch06-19: FinBERT | TF incompatible with QC Cloud | Rewrite using PyTorch/transformers |
| LOW | Ch08-02: Corrective AI | Negative Sharpe (-0.151) | Position sizing + exit timing improvements |
| LOW | Ch07-01: RL Options Hedging | Negative Sharpe (-1.264) | Expected RL learning curve; improve reward function |

### Notebook Coverage

Our 28-notebook series (QC-Py-01 to QC-Py-28) covers the full book spectrum:
- **Chapters 00-05**: Covered by notebooks 01-20 (foundations through ML basics)
- **Chapter 06**: Covered by notebooks 17-26 (sentiment through LLM)
- **Chapter 07**: Covered by notebooks 25 (RL), projects RL-Options-Hedging + RL-DQN-Trading
- **Chapter 08**: Covered by notebooks 10, 21, 27 (risk, portfolio, deployment), project Corrective-AI

---

## Resources

- **Book**: [Hands-On AI Trading with Python, QuantConnect, and AWS](https://qnt.co/book-amazon)
- **Book Repo**: https://github.com/QuantConnect/HandsOnAITradingBook
- **Our Projects**: `MyIA.AI.Notebooks/QuantConnect/projects/`
- **Our Notebooks**: `MyIA.AI.Notebooks/QuantConnect/Python/`
- **Detailed Mapping**: `docs/HANDSON_AI_TRADING_MAPPING.md` (full notebook-level breakdown)

---

Version: 1.2 | Issue: #107 | Date: 2026-05-12 | Ch07+Ch08 audit (po-2023 C25)
