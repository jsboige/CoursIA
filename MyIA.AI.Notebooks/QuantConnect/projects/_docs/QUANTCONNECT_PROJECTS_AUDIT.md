# QuantConnect Projects Audit — 2026-04-21

**Scope**: Read-only audit of 95 project directories in `MyIA.AI.Notebooks/QuantConnect/projects/`.
**Method**: Automated scan of artifacts (main.py, research.ipynb, README.md, config.json with cloud-id).
**No QC API calls** (rate-limit preserved during ESGF course).

## Summary

| Metric | Count |
|--------|-------|
| Total project directories | 95 |
| Complete (3 files + cloud-id) | 0 |
| Complete (3 files, no cloud-id) | 12 |
| Incomplete (missing 1+ files) | 83 |
| Has cloud-id | 7 |
| Has config.json | 12 |
| Archived | 3 |
| C# projects (Main.cs) | 4 |
| No code files | 2 |

## Artifact Coverage

| Artifact | Present | Missing |
|----------|---------|---------|
| main.py (or Main.cs) | 91 | 4 (2 no-code + 2 C#-only dirs) |
| research.ipynb | 44 | 51 |
| quantbook.ipynb (alternate) | 48 | — |
| research.ipynb OR quantbook.ipynb | 86 | 9 |
| README.md | 12 | 83 |
| config.json | 12 | 83 |

## Categories

### ARCHIVED (3)

These strategies reached their Sharpe ceiling and are documented in ARCHIVE.md.

| Project | Sharpe | Reason |
|---------|--------|--------|
| MomentumStrategy | ~0.47 | ML momentum ceiling |
| SectorMomentum | ~0.56 | Dual momentum ceiling |
| TurnOfMonth | ~0.13 | Calendar anomaly diluted in 2015-2026 bull |

### COMPLETE — All 3 Files, No Cloud-id (12)

Projects with main.py + research.ipynb + README.md but no cloud-id in config.

| Project | Language | config.json |
|---------|----------|-------------|
| AllWeather | Python | Y (local-id only) |
| Crypto-LSTM-Prediction | Python | Y (cloud-id: null) |
| DualMomentum | Python | N |
| ETF-Pairs | Python | N |
| FuturesTrend | Python | N |
| MomentumStrategy | Python (ARCHIVED) | N |
| OptionsIncome | Python | N |
| PairsTrading | Python | N |
| Portfolio-Optimization-ML | Python | Y (cloud-id: null) |
| RiskParity | Python | N |
| Sector-ML-Classification | Python | Y (cloud-id: null) |
| TrendFilteredMeanReversion | Python | N |

### HAS CLOUD-ID (7)

| Project | Cloud ID | Has All Files? |
|---------|----------|----------------|
| BlackLitterman-Momentum | 29816300 | N (missing research.ipynb, README.md) |
| EMA-Cross-Alpha | 28885488 | N (missing research.ipynb, README.md) |
| ML-Classification | 29434754 | N (missing research.ipynb) |
| ML-RandomForest | 29434751 | N (missing README.md) |
| ML-SVM | 29434752 | N (missing research.ipynb, README.md) |
| ML-XGBoost | 29434753 | N (missing README.md) |
| TrendStocks-Alpha | 28885507 | N (missing research.ipynb, README.md) |

### C# PROJECTS (4)

| Project | Has Main.cs | Has Research.ipynb | Has README.md |
|---------|-------------|---------------------|---------------|
| BTC-MACD-ADX | Y | Y | N |
| CSharp-BTC-EMA-Cross | Y | N (has research_robustness) | Y |
| CSharp-BTC-MACD-ADX | Y | Y | Y |
| CSharp-CTG-Momentum | Y | N (has research_robustness) | Y |

### NO CODE FILES (2)

| Project | Files Present |
|---------|---------------|
| Alpha-Correlation-Analysis | quantbook.ipynb, README.md |
| ML-Pairs-PCA-Selection | research.ipynb only |

### MOST COMMON MISSING ARTIFACTS

1. **README.md**: 83/95 missing (87%) — most projects lack documentation
2. **research.ipynb**: 51/95 missing (54%) — but 48 have quantbook.ipynb as alternate
3. **config.json**: 83/95 missing (87%) — most projects have no QC cloud config

### PROJECTS MISSING main.py BUT HAVE NOTEBOOK (2)

| Project | Has | Missing |
|---------|-----|---------|
| Alpha-Correlation-Analysis | quantbook.ipynb, README.md | main.py, config.json |
| ML-Pairs-PCA-Selection | research.ipynb | main.py, README.md, config.json |

## Full Inventory

| # | Project | main.py | research.ipynb | README.md | config.json | cloud-id | Verdict |
|---|---------|---------|----------------|-----------|-------------|----------|---------|
| 1 | Adaptive-Conformal-Risk | Y | N | N | N | — | INCOMPLET |
| 2 | AdaptiveAssetAllocation | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 3 | AllWeather | Y | Y | Y | Y | null | OK |
| 4 | Alpha-Correlation-Analysis | N | N (has quantbook) | Y | N | — | NO-CODE |
| 5 | AssetClassMomentum-QC | Y | N | N | N | — | INCOMPLET |
| 6 | BTC-MACD-ADX | N (has Main.cs) | Y | N | N | — | CSHARP |
| 7 | BTC-ML | Y | Y | N | N | — | INCOMPLET |
| 8 | BlackLitterman-Momentum | Y | N | N | Y | 29816300 | INCOMPLET |
| 9 | CSharp-BTC-EMA-Cross | N (has Main.cs) | N | Y | N | — | CSHARP |
| 10 | CSharp-BTC-MACD-ADX | N (has Main.cs) | Y | Y | N | — | CSHARP |
| 11 | CSharp-CTG-Momentum | N (has Main.cs) | N | Y | N | — | CSHARP |
| 12 | CausalEventAlpha | Y | N | N | N | — | INCOMPLET |
| 13 | Chronos-Foundation-Forecasting | Y | Y | N | N | — | INCOMPLET |
| 14 | Clustering-Fundamentals-ML | Y | N | N | N | — | INCOMPLET |
| 15 | Crypto-LSTM-Prediction | Y | Y | Y | Y | null | OK |
| 16 | Crypto-MultiCanal | Y | Y | N | N | — | INCOMPLET |
| 17 | DL-LSTM | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 18 | Dividend-Harvesting-ML | Y | N | N | N | — | INCOMPLET |
| 19 | DualMomentum | Y | Y | Y | N | — | OK |
| 20 | DualMomentumNoTLT | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 21 | Dynamic-Options-Wheel | Y | N | N | N | — | INCOMPLET |
| 22 | DynamicVIXSpyRegime-QC | Y | Y | N | N | — | INCOMPLET |
| 23 | EMA-Cross-Alpha | Y | N (has quantbook) | N | Y | 28885488 | INCOMPLET |
| 24 | EMA-Cross-Crypto | Y | Y | N | N | — | INCOMPLET |
| 25 | EMA-Cross-Index | Y | Y | N | N | — | INCOMPLET |
| 26 | EMA-Cross-Stocks | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 27 | ETF-Pairs | Y | Y | Y | N | — | OK |
| 28 | FamaFrench | Y | Y | N | N | — | INCOMPLET |
| 29 | ForexCarry | Y | Y | N | N | — | INCOMPLET |
| 30 | Framework_Composite_EMATrend | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 31 | Framework_Composite_FamaFrenchAllWeather | Y | N (has quantbook) | Y | Y | null | INCOMPLET |
| 32 | Framework_Composite_MomentumRegime | Y | N (has quantbook) | Y | N | — | INCOMPLET |
| 33 | Framework_Composite_TrendWeather | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 34 | FuturesTrend | Y | Y | Y | N | — | OK |
| 35 | Gaussian-Direction-Classifier | Y | N | N | N | — | INCOMPLET |
| 36 | HMM-KMeans-Voting | Y | N | N | N | — | INCOMPLET |
| 37 | HighBookToMarketFScore-QC | Y | N | N | N | — | INCOMPLET |
| 38 | InverseVolatility-Rank | Y | N | N | N | — | INCOMPLET |
| 39 | LSTM-Forecasting | Y | Y | N | N | — | INCOMPLET |
| 40 | LeveragedETFMomentum-QC | Y | N | N | N | — | INCOMPLET |
| 41 | LongShortHarvest-QC | Y | Y | N | N | — | INCOMPLET |
| 42 | ML-Chronos-Foundation | Y | N | N | N | — | INCOMPLET |
| 43 | ML-Classification | Y | N (has quantbook) | Y | Y | 29434754 | INCOMPLET |
| 44 | ML-DeepLearning | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 45 | ML-EnhancedPairs | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 46 | ML-Ensemble | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 47 | ML-FX-SVM-Wavelet | Y | N | N | N | — | INCOMPLET |
| 48 | ML-FeatureEngineering | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 49 | ML-FinBERT-Sentiment | Y | N | N | N | — | INCOMPLET |
| 50 | ML-Gaussian-Classifier | Y | N | N | N | — | INCOMPLET |
| 51 | ML-HMM-Regime | Y | N | N | N | — | INCOMPLET |
| 52 | ML-HeadShoulders-CNN | Y | Y | N | N | — | INCOMPLET |
| 53 | ML-LLM-Summarization | Y | N | N | N | — | INCOMPLET |
| 54 | ML-PCA-StatArb | Y | N | N | N | — | INCOMPLET |
| 55 | ML-Pairs-PCA-Selection | N | Y | N | N | — | NO-CODE |
| 56 | ML-RandomForest | Y | Y | N | Y | 29434751 | INCOMPLET |
| 57 | ML-Regression | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 58 | ML-Reversion-Trending | Y | N | N | N | — | INCOMPLET |
| 59 | ML-SVM | Y | N (has quantbook) | N | Y | 29434752 | INCOMPLET |
| 60 | ML-Temporal-CNN | Y | N | N | N | — | INCOMPLET |
| 61 | ML-TextClassification | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 62 | ML-Trend-Scanning | Y | N | N | N | — | INCOMPLET |
| 63 | ML-XGBoost | Y | Y | N | Y | 29434753 | INCOMPLET |
| 64 | MacroFactorRotation-QC | Y | N | N | N | — | INCOMPLET |
| 65 | Markov-Regime-Detection | Y | N | N | N | — | INCOMPLET |
| 66 | MeanReversion | Y | Y | N | N | — | INCOMPLET |
| 67 | MomentumStrategy | Y | Y | Y | N | — | ARCHIVED |
| 68 | Multi-Layer-EMA | Y | Y | N | N | — | INCOMPLET |
| 69 | Option-Wheel | Y | Y | N | N | — | INCOMPLET |
| 70 | Options-VGT | Y | N (has quantbook) | Y | N | — | INCOMPLET |
| 71 | OptionsIncome | Y | Y | Y | N | — | OK |
| 72 | PCA-StatArb | Y | N | N | N | — | INCOMPLET |
| 73 | PCA-StatArbitrage | Y | N | N | N | — | INCOMPLET |
| 74 | PairsTrading | Y | Y | Y | N | — | OK |
| 75 | Portfolio-Optimization-ML | Y | Y | Y | Y | null | OK |
| 76 | Positive-Negative-Splits-ML | Y | N | N | N | — | INCOMPLET |
| 77 | PuppiesOfTheDow-QC | Y | N | N | N | — | INCOMPLET |
| 78 | RL-DQN-Trading | Y | N | N | N | — | INCOMPLET |
| 79 | RL-Portfolio | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 80 | RegimeSwitching | Y | N (has quantbook) | N | N | — | INCOMPLET |
| 81 | Reinforcement-Learning-Trading | Y | Y | N | N | — | INCOMPLET |
| 82 | RiskParity | Y | Y | Y | N | — | OK |
| 83 | SVM-Wavelet-Forecasting | Y | N | N | N | — | INCOMPLET |
| 84 | Sector-ML-Classification | Y | Y | Y | Y | null | OK |
| 85 | SectorMomentum | Y | Y | N | N | — | ARCHIVED |
| 86 | Stoploss-Volatility-ML | Y | N | N | N | — | INCOMPLET |
| 87 | Temporal-CNN-Prediction | Y | Y | N | N | — | INCOMPLET |
| 88 | TermStructureCommodities-QC | Y | N | N | N | — | INCOMPLET |
| 89 | TradingCosts-Optimization | Y | N | N | N | — | INCOMPLET |
| 90 | Trend-Following | Y | N (has quantbook) | Y | N | — | INCOMPLET |
| 91 | TrendFilteredMeanReversion | Y | Y | Y | N | — | OK |
| 92 | TrendStocks-Alpha | Y | N (has quantbook) | N | Y | 28885507 | INCOMPLET |
| 93 | TrendStocksLite | Y | Y | N | N | — | INCOMPLET |
| 94 | TurnOfMonth | Y | Y | N | N | — | ARCHIVED |
| 95 | VIX-TermStructure | Y | Y | N | N | — | INCOMPLET |

## Recommendations

1. **README.md is the biggest gap** (83/95 missing). These projects need at minimum a one-line description + backtest results.
2. **Cloud-id linkage**: Only 7 projects have a cloud-id. The rest are local-only and not linked to QC Cloud projects.
3. **quantbook.ipynb vs research.ipynb**: 48 projects have quantbook.ipynb but not research.ipynb. Consider standardizing to research.ipynb.
4. **2 projects with no code** (Alpha-Correlation-Analysis, ML-Pairs-PCA-Selection) should either have code added or be reclassified as research-only notebooks.
5. **C# projects** (4) are complete in their own right but use Main.cs instead of main.py.

## Audit metadata

- **Date**: 2026-04-21
- **Auditor**: myia-po-2024
- **Method**: Automated filesystem scan, no QC API calls
- **Branch**: chore/qc-audit-projects-coverage
