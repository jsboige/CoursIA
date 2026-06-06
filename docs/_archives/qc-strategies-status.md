# QC Strategies & Notebooks — Unified Status

Generated: 2026-05-28 | Source: issue #1628, exhaustive audit of `MyIA.AI.Notebooks/QuantConnect/`
Previous version: 2026-05-07 (issue #29)

## 4-Type Classification

Every notebook in the QC tree falls into exactly one type:

| Type | Label | Definition | Execution |
|------|-------|-----------|-----------|
| **(a)** | quantbook QC Cloud | Uses `QuantBook()` or is a cloud-deploy descriptor (`QC-Py-Cloud-*`) | QC Cloud only |
| **(b)** | research linked to quantbook | Companion analysis paired with a type-(a) notebook | QC Cloud (QuantBook) + local |
| **(c)** | standalone research | Independent analysis using yfinance/pandas/sklearn, no QuantConnect dependency | Local |
| **(d)** | pedagogical placeholder | Course material with embedded `QCAlgorithm` strings, `# TODO` stubs, or descriptive text | Read-only / QC Cloud copy-paste |

## Summary Statistics

| Directory | Type (a) | Type (b) | Type (c) | Type (d) | Total |
|-----------|----------|----------|----------|----------|-------|
| `projects/` | 45 | 49 | 0 | 0 | **94** |
| `projects/` (other nb) | 0 | 8 | 0 | 0 | **8** |
| `research/` | 0 | 0 | 14 | 0 | **14** |
| `Python/` | 14 | 2 | 6 | 33 | **55** |
| `ML-Training-Pipeline/` | 0 | 0 | 4 | 0 | **4** |
| `partner-course-quant-trading/` | 0 | 7 | 0 | 0 | **7** |
| Top-level strategy dirs | 0 | ~10 | 0 | 0 | **~10** |
| **Total** | **59** | **~76** | **24** | **33** | **~192** |

---

## projects/ — Strategies & Notebooks (95 projects, 94 notebooks)

45 quantbook.ipynb (type a) + 49 research.ipynb (type b) + 8 other notebooks (type b/c).

### Performance Classification (from projects/README.md)

#### Robuste (Sharpe > 0.5)

| Project | Sharpe | CAGR | Max DD | Type | Research | Note |
|---------|--------|------|--------|------|----------|------|
| Positive-Negative-Splits-ML | 1.736 | 90.83% | 42.4% | a+b | — | Split factor + XLK ROC |
| ~~BTC-MACD-ADX~~ | 1.647 | 38.1% | 48.8% | a | — | ARCHIVED 2026-05-29: misleading name (EMA crossover, not MACD+ADX) |
| LeveragedETFMomentum-QC | 1.80 | 101.03% | — | — | b | QC Library #60 |
| LongShortHarvest-QC | 3.39 | 57.94% | — | — | b | QC Library #238 |
| Framework_Composite_TrendWeather | 1.155 | 27.4% | 27.7% | a | QuantBook | T75/AW25 composite |
| CSharp-BTC-EMA-Cross | 1.094 | 36.2% | 40.7% | a | — | C# |
| HighBookToMarketFScore-QC | 2.09 | 18.44% | — | — | b | QC Library #343 |
| PuppiesOfTheDow-QC | 1.99 | 10.16% | — | — | — | QC Library #211 |
| DynamicVIXSpyRegime-QC | 1.72 | 29.76% | — | — | b | QC Library #50 |
| Portfolio-Optimization-ML | 0.896 | 27.6% | 41.6% | a+b | — | Markowitz + ML |
| EMA-Cross-Stocks | 0.872 | 25.7% | 35.7% | a | — | |
| CausalEventAlpha | 0.779 | 16.75% | 22.1% | a | — | CATE sector rotation |
| Gaussian-Direction-Classifier | 0.761 | — | 25.6% | a | — | Book Ex15 |
| ML-Temporal-CNN | 0.734 | 20.51% | 21.6% | a | — | Book Ex14, real Keras |
| ML-LLM-Summarization | 0.686 | 15.45% | 22.7% | — | — | Book Ex16, Tiingo |
| ML-RandomForest | 0.682 | 20.1% | 36.4% | a+b | yfinance | v3 |
| ML-Trend-Scanning | 0.656 | 19.1% | 34.8% | a | — | Book Ex01 |
| TrendStocksLite | 0.719 | 18.2% | 33.7% | a+b | yfinance | |
| AllWeather | 0.667 | 9.3% | 16.4% | a+b | yfinance | |
| SectorMomentum | 0.621 | 13.2% | 22.8% | a+b | yfinance | Antonacci |
| MomentumStrategy | 0.565 | 11.8% | 25.8% | a+b | yfinance | |
| ML-FeatureEngineering | 0.571 | 10.5% | 19.6% | a | — | Best Drawdown |
| Markov-Regime-Detection | 0.571 | — | — | a | — | Book Ex04 |
| ML-XGBoost | 0.566 | 14.8% | 38.6% | a+b | — | v2 |
| RegimeSwitching | 0.553 | 11.7% | 33.0% | a | — | |
| FamaFrench | 0.540 | 12.1% | 24.2% | a+b | yfinance | |
| Temporal-CNN-Prediction | 0.536 | 13.8% | 33.9% | a+b | — | Book Ex14 proxy |
| RL-DQN-Trading | 0.533 | 10.9% | 25.8% | a | — | Book Ch07 |
| LSTM-Forecasting | 0.525 | 11.3% | 32.5% | a+b | — | Book Ex07 |
| Option-Wheel | 0.524 | 12.69% | 26.40% | a+b | — | Validated 2015-2026 |
| AdaptiveAssetAllocation | 0.518 | 8.0% | 18.8% | a | — | |
| Options-VGT | 0.507 | 14.2% | 16.2% | a | — | |
| CSharp-CTG-Momentum | 0.507 | 17.7% | 36.1% | a | — | |
| MacroFactorRotation-QC | 1.23 | 33.45% | — | — | — | QC Library #72 |
| BlackLitterman-Momentum | 0.604 | 13.7% | 33.1% | a | — | He & Litterman |

#### Historique / Regime-dependante (Sharpe 0-0.5)

| Project | Sharpe | CAGR | Max DD | Type | Research | Note |
|---------|--------|------|--------|------|----------|------|
| Multi-Layer-EMA | 0.928 | 120.9% | 54.4% | a+b | QuantBook | NON ROBUSTE hors bulle |
| Crypto-MultiCanal | 0.486 | 7.6% | 16.8% | a+b | QuantBook | BUG: import error |
| EMA-Cross-Index | 0.470 | 9.4% | 17.5% | a+b | yfinance | |
| DualMomentumNoTLT | 0.469 | 11.0% | 23.6% | a | — | |
| Dividend-Harvesting-ML | 0.469 | 12.7% | 30.5% | a | — | Book Ex06 |
| Sector-ML-Classification | 0.473 | 11.9% | 34.4% | a+b | — | v5 |
| Adaptive-Conformal-Risk | 0.423 | 11.15% | 38.7% | a | — | ACI (Gibbs & Candes) |
| RiskParity | 0.399 | 7.8% | 20.9% | a+b | — | Plafond |
| PCA-StatArbitrage | 0.399 | 12.65% | 31.8% | a | — | Book Ex13 |
| DualMomentum | 0.350 | 9.2% | 33.6% | a+b | yfinance | COVID structurel |
| ML-Gaussian-Classifier | 0.361 | 12.49% | 47.4% | a | — | Book Ex15 |
| ML-Reversion-Trending | 0.292 | 6.6% | 29.4% | a+b | — | Book Ex03 |
| BTC-ML | 0.282 | 8.3% | 13.7% | a+b | QuantBook | Periode courte |
| ML-Chronos-Foundation | 0.277 | 7.23% | 13.5% | a+b | — | Book Ex18 |
| Chronos-Foundation-Forecasting | 0.253 | — | 22.4% | a+b | — | Book Ex18 v2 |
| EMA-Cross-Crypto | 0.244 | 3.804% | 37.2% | a+b | yfinance | |
| InverseVolatility-Rank | 0.212 | 5.85% | 54.7% | a+b | — | Book Ex11 |
| OptionsIncome | 0.207 | 5.435% | 17.50% | a+b | yfinance | Validated |
| Dynamic-Options-Wheel | 0.119 | 5.59% | 31.4% | a | — | IV regime extension |
| FuturesTrend | 0.136 | 4.896% | 18.70% | a+b | yfinance | |
| MeanReversion | 0.294 | 7.5% | 16.5% | a+b | yfinance | |
| VIX-TermStructure | 0.051 | 3.6% | 35.2% | a+b | yfinance | Post-VIXplosion |
| ML-FX-SVM-Wavelet | 0.167 | 5.07% | 20.5% | a | — | Book Ex05, overtrading |
| ML-SVM | 0.147 | 5.2% | 27.1% | a | — | Plafond |
| TurnOfMonth | 0.128 | 4.8% | 23.7% | a+b | yfinance | Effet faible |
| TermStructureCommodities-QC | -0.041 | -15.71% | — | — | — | Quantpedia #22 |

#### Exploratoire (Sharpe < 0)

| Project | Sharpe | CAGR | Max DD | Type | Research | Note |
|---------|--------|------|--------|------|----------|------|
| TrendFilteredMeanReversion | -0.016 | 3.4% | 11.4% | a | — | ~9 trades/an |
| ForexCarry | -0.324 | 1.5% | 10.5% | a+b | yfinance | Carry evaporee |
| PairsTrading | -0.361 | 0.9% | 15.1% | a+b | — | Non cointegrees |
| ETF-Pairs | -0.706 | -4.7% | 35.0% | a+b | QuantBook | Cointregration instable |
| Clustering-Fundamentals-ML | -0.052 | -1.2% | 15.3% | a | — | Runtime Error |
| TradingCosts-Optimization | -13.354 | -0.015% | 0.4% | a | — | Quasi flat |
| ML-HeadShoulders-CNN | -46.8 | 0.03% | 0.1% | a+b | — | 4 trades only |

#### NO_BACKTEST (not yet evaluated)

| Project | Type | Note |
|---------|------|------|
| ML-Classification | a | Cloud ID 29434754 |
| ML-Regression | a | |
| ML-Ensemble | a | |
| ML-EnhancedPairs | a | |
| ML-DeepLearning | a | PyTorch |
| DL-LSTM | a | PyTorch |
| ML-TextClassification | a | |
| RL-Portfolio | a | |
| Crypto-LSTM-Prediction | — | Research phase |
| Reinforcement-Learning-Trading | a | Pedagogical variant |
| SVM-Wavelet-Forecasting | — | Local only |
| Stoploss-Volatility-ML | a+b | BROKEN: CBOE data |
| ~~ML-Pairs-PCA-Selection~~ | — | ARCHIVED 2026-05-29: no main.py, concept covered by PCA-StatArbitrage |
| ML-FinBERT-Sentiment | — | TF unavailable, 0 trades |
| Framework_Composite_FamaFrenchAllWeather | a | PENDING QC deploy |
| Framework_Composite_EMATrend | a | Not backtested |
| Framework_Composite_MomentumRegime | a | Not backtested |
| EMA-Cross-Alpha | a | Framework building block |
| TrendStocks-Alpha | a | Framework building block |
| Alpha-Correlation-Analysis | a | QuantBook research |
| AssetClassMomentum-QC | — | No local backtest |
| HMM-KMeans-Voting | — | Research only |
| Research-Executor | — | Tool (runner + 8 QC Library research notebooks) |

---

## research/ — Standalone Research (14 notebooks, all type c)

| Notebook | Topic | Data Source |
|----------|-------|-------------|
| `research_btc_ml.ipynb` | BTC ML prediction features | yfinance |
| `research_composite_ff_aw.ipynb` | FamaFrench + AllWeather composite | yfinance |
| `research_composite_mom_regime.ipynb` | Momentum + Regime composite | yfinance |
| `research_m11ef_ensemble.ipynb` | Ensemble methods | yfinance |
| `research_m12_har_rv_j.ipynb` | HAR-RV-J volatility model | yfinance |
| `research_quality_lowvol.ipynb` | Quality + Low Vol factor | yfinance |
| `research_risk_parity.ipynb` | Risk parity allocation | yfinance |
| `research_rl_grpo.ipynb` | RL GRPO trading agent | yfinance |
| `research_rl_intro.ipynb` | RL introduction | yfinance |
| `research_rl_multi_asset.ipynb` | RL multi-asset allocation | yfinance |
| `research_rl_ppo.ipynb` | PPO trading agent | yfinance |
| `research_rl_reward_shaping.ipynb` | RL reward shaping | yfinance |
| `research_rl_tactical_overlay.ipynb` | RL tactical overlay | yfinance |
| `research_vrp_putwrite.ipynb` | VRP put-write strategy | yfinance |

---

## Python/ — Pedagogical Series (55 notebooks)

| Type | Count | Notebooks |
|------|-------|-----------|
| **(d)** | 33 | QC-Py-01 to 28 (course series), QC-Py-35, QC-Py-40/41 (+ outputs) |
| **(a)** | 14 | QC-Py-04 (QuantBook live), QC-Py-Cloud-01 to 07 (cloud-deploy descriptors) |
| **(c)** | 6 | QC-Py-30 to 34 (local yfinance training), QC-Py-Dataset-Workflow |
| **(b)** | 2 | research/research_classification (-> QC-Py-19), research/research_lstm (-> QC-Py-22) |

Full classification table in [Python/README.md](../MyIA.AI.Notebooks/QuantConnect/Python/README.md).

---

## ML-Training-Pipeline/ — Local Training (4 notebooks, all type c)

| Notebook | Topic | Model |
|----------|-------|-------|
| `ML-Research-Template.ipynb` | Template for ML research | Generic |
| `m3_har_asymmetric_semivariance.ipynb` | HAR asymmetric semivariance | HAR |
| `research_what_dl_can_predict.ipynb` | What DL can predict in finance | Various DL |
| `research_l4_decision_transformer.ipynb` | Decision Transformer evaluation | RL/DT |

---

## partner-course-quant-trading/ — Course Examples (7 notebooks, type b)

| Notebook | Topic | Source |
|----------|-------|--------|
| `examples/Crypto-MultiCanal/research.ipynb` | Crypto MultiCanal analysis | QC project |
| `examples/Sector-Momentum/deep_research_optimization.ipynb` | Sector momentum deep research | QC project |
| `examples/Sector-Momentum/research_robustness.ipynb` | Sector momentum robustness | QC project |
| `kit-transitoire/01-ML-RandomForest/research.ipynb` | ML RF course example | QC project |
| `kit-transitoire/02-ML-XGBoost/research.ipynb` | XGBoost course example | QC project |
| `kit-transitoire/03-Framework-Composite/research.ipynb` | Composite framework example | QC project |
| `examples/Crypto-MultiCanal/research_archive.ipynb` | Archive | QC project |

---

## Naming Convention

| Pattern | Type | Location | Example |
|---------|------|----------|---------|
| `projects/<Name>/quantbook.ipynb` | (a) | QC Cloud | `projects/EMA-Cross-Stocks/quantbook.ipynb` |
| `projects/<Name>/research.ipynb` | (b) | QC Cloud + local | `projects/MomentumStrategy/research.ipynb` |
| `research/<topic>.ipynb` | (c) | Local (yfinance) | `research/research_rl_ppo.ipynb` |
| `Python/QC-Py-XX-*.ipynb` | (d) | Course material | `Python/QC-Py-15-Parameter-Optimization.ipynb` |
| `Python/QC-Py-Cloud-XX-*.ipynb` | (a) | QC Cloud descriptor | `Python/QC-Py-Cloud-07-TemporalCNN.ipynb` |
| `Python/QC-Py-XX-<model>-Training.ipynb` | (c) | Local training | `Python/QC-Py-30-LSTM-Training.ipynb` |
| `ML-Training-Pipeline/*.ipynb` | (c) | Local training | `ML-Training-Pipeline/research_l4_decision_transformer.ipynb` |
| `partner-course-quant-trading/` | (b) | QC Cloud + local | Course examples + kit-transitoire |

---

## Actions Taken

- **Cycle 5 (2026-05-07)**: Initial classification from issue #29 — 34 strategies, 5 categories (BROKEN_PEDAGOGICAL, BROKEN_TO_FIX, NEEDS_IMPROVEMENT, HEALTHY, NO_BACKTEST)
- **Cycle 91 (2026-05-28)**: Full refonte — 4-type classification (a/b/c/d) covering ~192 notebooks across 7 directories, merged with 95-project performance data from projects/README.md
- **2026-05-29 (po-2023, #1627)**: Dedup audit — 50 projects scanned across 9 families (EMA-Cross, DualMomentum, BTC, ML-*, Crypto, Vol-*, Pairs, Cloud-*, HAR-RV). 4 archived (BTC-MACD-ADX misleading name, ML-Pairs-PCA-Selection no main.py, Cloud-DualMomentum-NoTLT duplicate, Simple-Equity-EMA-Crossing minimal). 1 dead code removed (EMA-Cross-Stocks/alpha_model.py). 7 README fixed. 0 duplicates remaining.
