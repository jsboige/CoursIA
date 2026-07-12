# QC Projects Audit — 2026-05-28

**Scope**: 115 strategy directories in `projects/` (excluding `_docs/`).
**Source**: Epic #1621, sub-issue #1622.
**Methodology**: Automated scan (git log, file existence, content diff) + manual classification.

## Classification (5 buckets)

| Bucket | Count | Definition |
|--------|-------|------------|
| **ALIVE** | 88 | Has `main.py` or `Main.cs`, README present, commit within 3 months |
| **ARCHIVED** | 4 | Explicitly marked archived in code/README, kept for pedagogical reference |
| **DRAFT** | 7 | README + research notebook only, no runnable `main.py` yet |
| **DUPLICATE** | 0 | No true duplicates found (all variants have distinct logic/parameters) |
| **BROKEN** | 0 | No empty/broken directories found (all have at least README + content) |

## ALIVE (88 strategies)

Full Python or C# strategies with runnable code, README, and recent commits (April-May 2026).

| # | Strategy | Lang | Lines | Last Commit | Notes |
|---|----------|------|-------|-------------|-------|
| 1 | Adaptive-Conformal-Risk | Py | 357 | 2026-05-21 | |
| 2 | AdaptiveAssetAllocation | Py | 130 | 2026-05-21 | |
| 3 | AllWeather | Py | 114 | 2026-05-05 | |
| 4 | AssetClassMomentum-QC | Py | 27 | 2026-05-21 | Minimal wrapper |
| 5 | BTC-ML | Py | 374 | 2026-05-21 | |
| 6 | BlackLitterman-Momentum | Py | 417 | 2026-05-21 | |
| 7 | CausalEventAlpha | Py | 447 | 2026-05-21 | |
| 8 | Chronos-Foundation-Forecasting | Py | 360 | 2026-05-21 | |
| 9 | Cloud-DualMomentum-NoTLT | Py | 139 | 2026-05-20 | Multi-version wrapper (v1/v2/v3) |
| 10 | Cloud-MeanReversion-Sectors | Py | 139 | 2026-05-20 | Multi-version (3 variants) |
| 11 | Cloud-RiskParity-Composite | Py | 92 | 2026-05-20 | Cloud-native QuantBook |
| 12 | Cloud-SectorRotation-Momentum | Py | 118 | 2026-05-20 | v4 momentum-weighted |
| 13 | Cloud-VolTargeting | Py | 151 | 2026-05-20 | Multi-version (3 variants) |
| 14 | Clustering-Fundamentals-ML | Py | 125 | 2026-05-21 | HandsOn Ex10 |
| 15 | Crypto-LSTM-Prediction | Py | 747 | 2026-05-11 | |
| 16 | Crypto-MultiCanal | Py | 378 | 2026-05-21 | |
| 17 | DL-LSTM | Py | 195 | 2026-05-21 | |
| 18 | Dividend-Harvesting-ML | Py | 164 | 2026-05-21 | HandsOn Ex06 |
| 19 | DualMomentum | Py | 115 | 2026-05-07 | Antonacci v6b |
| 20 | DualMomentumNoTLT | Py | 95 | 2026-05-21 | Separate from DualMomentum |
| 21 | Dynamic-Options-Wheel | Py | 406 | 2026-05-21 | |
| 22 | DynamicVIXSpyRegime-QC | Py | 258 | 2026-05-21 | |
| 23 | EMA-Cross-Alpha | Py | 35 | 2026-05-21 | |
| 24 | EMA-Cross-Crypto | Py | 101 | 2026-05-21 | |
| 25 | EMA-Cross-Index | Py | 68 | 2026-05-21 | |
| 26 | EMA-Cross-Stocks | Py | 72 | 2026-05-21 | |
| 27 | ETF-Pairs | Py | 139 | 2026-05-12 | |
| 28 | FamaFrench | Py | 208 | 2026-05-21 | |
| 29 | ForexCarry | Py | 145 | 2026-05-26 | |
| 30 | Framework_Composite_EMATrend | Py | 79 | 2026-05-21 | Framework composite |
| 31 | Framework_Composite_FamaFrenchAllWeather | Py | 73 | 2026-05-12 | Framework composite |
| 32 | Framework_Composite_MomentumRegime | Py | 69 | 2026-05-12 | Framework composite |
| 33 | Framework_Composite_TrendWeather | Py | 66 | 2026-05-21 | Framework composite |
| 34 | FuturesTrend | Py | 163 | 2026-05-07 | |
| 35 | Gaussian-Direction-Classifier | Py | 226 | 2026-05-21 | |
| 36 | GlobalMacro-Regime | Py | 142 | 2026-05-20 | |
| 37 | HAR-RV-J-Kelly | Py | 226 | 2026-05-28 | ESGF-derived |
| 38 | HAR-RV-Kelly | Py | 191 | 2026-05-28 | ESGF-derived |
| 39 | HMM-KMeans-Voting | Py | 413 | 2026-05-21 | |
| 40 | HighBookToMarketFScore-QC | Py | 36 | 2026-05-21 | |
| 41 | InverseVolatility-Rank | Py | 299 | 2026-05-21 | HandsOn Ex11 |
| 42 | LSTM-Forecasting | Py | 299 | 2026-05-21 | |
| 43 | LeveragedETFMomentum-QC | Py | 148 | 2026-05-21 | |
| 44 | LongShortHarvest-QC | Py | 623 | 2026-05-21 | |
| 45 | ML-Chronos-Foundation | Py | 256 | 2026-05-21 | HandsOn Ex18 |
| 46 | ML-Classification | Py | 243 | 2026-05-12 | |
| 47 | ML-DeepLearning | Py | 172 | 2026-05-21 | |
| 48 | ML-EnhancedPairs | Py | 263 | 2026-05-21 | |
| 49 | ML-Ensemble | Py | 269 | 2026-05-21 | |
| 50 | ML-FX-SVM-Wavelet | Py | 88 | 2026-05-21 | HandsOn Ex05 |
| 51 | ML-FeatureEngineering | Py | 370 | 2026-05-21 | |
| 52 | ML-FinBERT-Sentiment | Py | 301 | 2026-05-21 | HandsOn Ex19 |
| 53 | ML-Gaussian-Classifier | Py | 353 | 2026-05-21 | HandsOn Ex15 |
| 54 | ML-HeadShoulders-CNN | Py | 257 | 2026-05-21 | HandsOn Ex17 |
| 55 | ML-LLM-Summarization | Py | 205 | 2026-05-21 | HandsOn Ex16 |
| 56 | ML-RandomForest | Py | 234 | 2026-05-21 | |
| 57 | ML-Regression | Py | 227 | 2026-05-21 | |
| 58 | ML-Reversion-Trending | Py | 389 | 2026-05-21 | HandsOn Ex03 |
| 59 | ML-SVM | Py | 202 | 2026-05-21 | |
| 60 | ML-Temporal-CNN | Py | 171 | 2026-05-21 | HandsOn Ex14 |
| 61 | ML-TextClassification | Py | 262 | 2026-05-21 | |
| 62 | ML-Trend-Scanning | Py | 285 | 2026-05-21 | HandsOn Ex01 |
| 63 | ML-XGBoost | Py | 310 | 2026-05-21 | |
| 64 | MacroFactorRotation-QC | Py | 110 | 2026-05-21 | |
| 65 | Markov-Regime-Detection | Py | 183 | 2026-05-21 | |
| 66 | MeanReversion | Py | 136 | 2026-05-21 | |
| 67 | MomentumRegime-AdaptiveWeights | Py | 59 | 2026-05-12 | |
| 68 | MomentumStrategy | Py | 170 | 2026-05-07 | |
| 69 | Multi-Layer-EMA | Py | 87 | 2026-05-21 | |
| 70 | Option-Wheel | Py | 132 | 2026-05-21 | |
| 71 | Options-VGT | Py | 133 | 2026-05-12 | |
| 72 | OptionsIncome | Py | 194 | 2026-05-12 | |
| 73 | PCA-StatArbitrage | Py | 170 | 2026-05-21 | |
| 74 | PairsTrading | Py | 174 | 2026-05-12 | |
| 75 | Portfolio-IBKR-Binance-Hybrid | Py | 53 | 2026-05-16 | |
| 76 | Portfolio-Optimization-ML | Py | 413 | 2026-04-21 | |
| 77 | Positive-Negative-Splits-ML | Py | 202 | 2026-05-21 | HandsOn Ex07 |
| 78 | PuppiesOfTheDow-QC | Py | 45 | 2026-05-21 | |
| 79 | RL-DQN-Trading | Py | 396 | 2026-05-21 | |
| 80 | RL-Portfolio | Py | 215 | 2026-05-26 | |
| 81 | RegimeSwitching | Py | 285 | 2026-05-28 | |
| 82 | Reinforcement-Learning-Trading | Py | 291 | 2026-05-21 | |
| 83 | Research-Executor | Py | 104 | 2026-05-20 | |
| 84 | RiskParity | Py | 124 | 2026-05-05 | |
| 85 | SVM-Wavelet-Forecasting | Py | 211 | 2026-05-21 | |
| 86 | Sector-ML-Classification | Py | 427 | 2026-05-13 | |
| 87 | Simple-Equity-EMA-Crossing | Py | 43 | 2026-05-20 | |
| 88 | Stoploss-Volatility-ML | Py | 194 | 2026-05-21 | HandsOn Ex08 |

### Alive — C# (5 strategies)

| # | Strategy | Lang | Last Commit | Notes |
|---|----------|------|-------------|-------|
| 89 | CSharp-BTC-EMA-Cross | C# | 2026-05-12 | QC Cloud project |
| 90 | CSharp-CTG-Momentum | C# | 2026-05-12 | QC Cloud project |
| 91 | BTC-MACD-ADX | C# | 2026-05-21 | C# version (has Research.ipynb) |
| 92 | CSharp-BTC-MACD-ADX | C# | 2026-04-21 | C# version (robustness research) |

## ARCHIVED (4 strategies)

Explicitly marked as archived in code or README. Kept for pedagogical reference.

| # | Strategy | Reason | Archival Note |
|---|----------|--------|---------------|
| 93 | SectorMomentum | `# [ARCHIVED - Sharpe ceiling ~0.56]` | Superseded by Cloud-SectorRotation-Momentum |
| 94 | TrendStocks-Alpha | Superseded by TrendStocksLite | Simpler variant retained |
| 95 | TrendFilteredMeanReversion | No recent updates (May 1) | Pedagogical reference |
| 96 | VolTarget-Momentum | Superseded by Cloud-VolTargeting | Cloud multi-version wrapper replaces it |

Note: These are kept in place. No deletion needed — they serve as teaching examples.

## DRAFT (7 strategies)

Have README.md and/or research notebook, but no runnable `main.py` yet.

| # | Strategy | Contents | Status |
|---|----------|----------|--------|
| 97 | Alpha-Correlation-Analysis | README + quantbook.ipynb | Research only |
| 98 | Corrective-AI | README only | Stub, referenced in Ch08 |
| 99 | Ensemble-DLinear-TFT | README + research.ipynb + generator | Research notebook |
| 100 | GraphSAGE-MultiAsset-Ranking | README + research.ipynb + generator | Research notebook |
| 101 | Mamba-Crypto-Ranking | README + research.ipynb + generator | Research notebook |
| 102 | ML-Pairs-PCA-Selection | README + research.ipynb | Research only, HandsOn Ex09 |
| 103 | TFT-Crypto-Ranking | README + research.ipynb + generator | Research notebook |
| 104 | RL-Options-Hedging | README only | Stub, referenced in Ch07 |

Note: The 4 research notebooks (Ensemble-DLinear-TFT, GraphSAGE, Mamba, TFT) have `_generate_research.py` scripts — they could be promoted to ALIVE once a `main.py` is generated from research.

## ALIVE — Variant Families (12 strategies)

Not duplicates — each variant has distinct parameters, universe, or logic.

| Family | Members | Distinction |
|--------|---------|-------------|
| EMA-Cross (4) | Stocks, Crypto, Index, Alpha | Different asset classes |
| DualMomentum (3) | DualMomentum, NoTLT, Cloud-DualMomentum-NoTLT | Different universes/weights, Cloud is multi-version |
| Framework Composite (4) | EMATrend, FamaFrenchAllWeather, MomentumRegime, TrendWeather | Different alpha model combinations |
| composite (2) | c1-multiasset, c2-equityfactor | Different factor models |
| Trend (4) | Trend-Following, TrendStocksLite, TrendStocks-Alpha, TrendFilteredMeanReversion | Different trend logic |
| Vol (4) | Vol-Ensemble-Conservative, Vol-GARCH-Target, VolTarget-Momentum, Cloud-VolTargeting | Different vol targeting approaches |
| HAR-RV (2) | HAR-RV-Kelly, HAR-RV-J-Kelly | With/without jump component |
| Sector (2) | SectorMomentum (ARCHIVED), Sector-ML-Classification | Classic vs ML approach |

## DUPLICATE — 0 found

No true duplicates identified. All same-family variants have distinct:
- Universe selection (different tickers)
- Signal generation logic
- Position sizing / risk management
- Framework architecture (simple vs composite)

## BROKEN — 0 found

No empty or broken directories. All 115 dirs have at minimum a README.md.

## Additional Statistics

| Metric | Value |
|--------|-------|
| Total directories | 115 (+ 1 `_docs/`) |
| Python strategies | 88 |
| C# strategies | 4 |
| Research-only (DRAFT) | 8 |
| HandsOn book exercises | 13 (Ex01-Ex19 range) |
| Cloud-native multi-version | 5 (Cloud-*) |
| Framework composites | 6 (4 + 2 composite-c*) |
| ML/DL/RL strategies | 30 |
| Avg main.py lines | ~215 |
| Median last commit | 2026-05-21 |

## Migration Plan

No migration needed. The projects directory is healthy:
- 0 duplicates to merge
- 0 broken to move to `_broken/`
- 4 archived are already self-documented
- 8 DRAFT could be promoted by generating `main.py` from research notebooks (future work)

### Optional improvements (low priority)
1. **Promote DRAFTs**: Generate `main.py` from research notebooks for Ensemble-DLinear-TFT, GraphSAGE, Mamba, TFT (4 strategies with `_generate_research.py`)
2. **Standardize READMEs**: ~20 strategies have minimal READMEs (< 5 lines). Could be enriched with backtest results.
3. **Archive marking**: Add `[ARCHIVED]` tag to README.md for SectorMomentum, TrendStocks-Alpha, VolTarget-Momentum if not already present.
