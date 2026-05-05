# QuantConnect Strategies Catalog

**Updated**: 2026-05-04 | **Source**: QC Cloud API + catalog_enrichment.json
**Total ALIVE projects**: 96 (22 DEAD/SUPERSEDED deleted 03/05)
**Reference**: [AUDIT_QC_CLOUD.md](audits/AUDIT_QC_CLOUD.md) for full classification

## Top Performers (Sharpe > 0.8)

| # | Strategy | ID | Sharpe | BTs | Category |
|---|----------|----|--------|-----|----------|
| 1 | HandsOn-Ex07-Positive-Negative-Splits | 30317350 | **1.736** | 2 | HandsOn |
| 2 | Framework_Composite_TrendWeather | 28825960 | **1.156** | 11 | Framework |
| 3 | BTC-MACD-ADX-Researcher 5 | 28418632 | **1.171** | 4 | Researcher |
| 4 | Volatility Regime ML | 29687293 | **1.29** | - | Imported |
| 5 | Long-Short Harvest | 29687399 | **1.505** | - | Imported |
| 6 | EMA-Cross-Alpha | 28885488 | **0.996** | 9 | Alpha |
| 7 | Portfolio-Optimization-ML | 29318874 | **0.896** | 2 | ML |
| 8 | Multi-Layer-EMA-Crypto | 30395392 | **0.900** | 2 | Alpha |
| 9 | Multi-Layer-EMA-Researcher | 28433748 | **0.900** | 9 | Researcher |
| 10 | EMA-Cross-Stocks | 28789946 | **0.867** | 2 | Alpha |
| 11 | Framework_Composite_EMATrend | 28911253 | **0.867** | 6 | Framework |
| 12 | TrendStocksLite | 28817425 | **0.752** | 2 | Alpha |
| 13 | HandsOn-Gaussian-Direction-Classifier | 29398513 | **0.761** | 2 | HandsOn |
| 14 | BlackLitterman-Momentum | 29816300 | **0.766** | 6 | Alpha |
| 15 | CSharp-BTC-MACD-ADX | 30751067 | **0.787** | 8 | Alpha |

## Performance Top 10 by Sharpe (Active projects only)

| # | Strategy | ID | Sharpe | BTs | Category |
|---|----------|----|--------|-----|----------|
| 1 | HandsOn-Ex07-Positive-Negative-Splits | 30317350 | **1.736** | 2 | HandsOn |
| 2 | BTC-MACD-ADX-Researcher 5 | 28418632 | **1.171** | 4 | Researcher |
| 3 | Framework_Composite_TrendWeather | 28825960 | **1.156** | 11 | Framework |
| 4 | EMA-Cross-Alpha | 28885488 | **0.996** | 9 | Alpha |
| 5 | Multi-Layer-EMA-Crypto | 30395392 | **0.900** | 2 | Alpha |
| 6 | Multi-Layer-EMA-Researcher | 28433748 | **0.900** | 9 | Researcher |
| 7 | Portfolio-Optimization-ML | 29318874 | **0.896** | 2 | ML |
| 8 | Framework_Composite_EMATrend | 28911253 | **0.867** | 6 | Framework |
| 9 | EMA-Cross-Stocks | 28789946 | **0.867** | 2 | Alpha |
| 10 | CSharp-BTC-MACD-ADX | 30751067 | **0.787** | 8 | Alpha |

## Top 5 by Backtest Count (most iterated projects)

| # | Strategy | ID | BTs | Sharpe | Category |
| --- | ---------- | --- | --- | -------- | ---------- |
| 1 | Sector-ML-Classification | 29318875 | **31** | 0.505 | ML |
| 2 | DualMomentum | 28693650 | **19** | 0.600 | Alpha |
| 3 | HandsOn-Ex08-Stoploss-Volatility-ML | 29463529 | **19** | N/A | HandsOn |
| 4 | Framework_Composite_FamaFrenchAllWeather | 28882145 | **19** | 0.546 | Framework |
| 5 | MeanReversion | 30776121 | **18** | 0.461 | Alpha |

## Category Distribution

| Category | Total | Active |
| ---------- | ------- | -------- |
| Alpha | 29 | 25 |
| ML/RL | 22 | 16 |
| HandsOn | 21 | 15 |
| ESGF | 18 | 4 |
| Researcher | 15 | 11 |
| Cloud | 6 | 6 |
| Framework | 6 | 6 |
| Imported | 8 | 8 |

## All ALIVE Projects by Family

### Alpha Strategies (single-signal, systematic)

| Strategy | ID | Sharpe | BTs | Signal |
|----------|----|--------|-----|--------|
| EMA-Cross-Alpha | 28885488 | 0.996 | 9 | EMA crossover |
| EMA-Cross-Stocks | 28789946 | 0.867 | 2 | EMA on equities |
| Multi-Layer-EMA-Crypto | 30395392 | 0.900 | 2 | Multi-layer EMA crypto |
| TrendStocks-Alpha | 28885507 | 0.609 | 3 | Trend following stocks |
| TrendStocksLite | 28817425 | 0.752 | 2 | Lightweight trend |
| EMA-Cross-Index | 28789945 | 0.470 | 2 | EMA index ETFs |
| EMA-Cross-Crypto | 28789943 | 0.244 | 8 | EMA crypto |
| BlackLitterman-Momentum | 29816300 | 0.766 | 6 | BL model + momentum |
| MeanReversion | 30776121 | 0.461 | 18 | Mean reversion |
| CausalEventAlpha | 29809163 | 0.423 | 1 | Causal event signals |
| Adaptive-Conformal-Risk | 29841071 | 0.604 | 1 | Conformal prediction |
| Dividend-Harvesting-ML | 29461593 | 0.468 | 2 | Dividend + ML filter |
| Crypto-MultiCanal | 30750734 | 0.581 | 1 | Multi-channel crypto |
| BTC-ML | 29318876 | 0.106 | 1 | BTC ML signals |
| CSharp-BTC-MACD-ADX | 30751067 | 0.787 | 8 | C# BTC MACD+ADX |

### Multi-Asset / Macro Rotation

| Strategy | ID | Sharpe | BTs | Signal |
|----------|----|--------|-----|--------|
| GlobalMacro-Regime | 30781695 | 0.607 | 7 | Macro regime detection |
| DualMomentumNoTLT | 28817424 | 0.469 | 1 | Antonacci dual momentum |
| RegimeSwitching | 28693650 | 0.565 | 5 | Regime switching |
| AdaptiveAssetAllocation | 28693649 | 0.518 | 5 | Adaptive allocation |
| RiskParity-v2 | 30780629 | 0.515 | 5 | Risk parity v2 |
| VolTarget-Momentum | 30784745 | 0.652 | 6 | Vol targeting + momentum |
| Options-VGT | 28797529 | 0.507 | 1 | Options on VGT |
| Dynamic-Options-Wheel | 30119363 | 0.119 | 4 | Options wheel strategy |
| HMM-KMeans-Voting | 29702014 | 0.488 | 1 | HMM + KMeans ensemble |

### Trend Following / AQR-style

| Strategy | ID | Sharpe | BTs | Signal |
|----------|----|--------|-----|--------|
| Trend-Following | 28797562 | 0.577 | 17 | AQR multi-asset trend |
| Sector-ML-Classification | 29318875 | 0.505 | 31 | ML sector classification |

### ML / RL Models

| Strategy | ID | Sharpe | BTs | Model |
|----------|----|--------|-----|-------|
| Portfolio-Optimization-ML | 29318874 | 0.896 | 2 | ML portfolio opt |
| ML-RandomForest | 29434751 | 0.682 | 4 | Random Forest |
| ML-FeatureEngineering | 29808616 | 0.656 | 1 | Feature engineering |
| C42-EquityFactor | 30809425 | 0.659 | 12 | Equity factor ML |
| ML-XGBoost | 29434753 | 0.566 | 4 | XGBoost |
| ML-Reversion-Trending | 29808861 | 0.571 | 2 | Reversion vs trending ML |
| ML-Trend-Scanning | 29808859 | 0.292 | 1 | Trend scanning ML |
| ML-SVM | 29434752 | 0.147 | 4 | SVM classifier |
| Clustering-Fundamentals-ML | 29461805 | 0.142 | 4 | Clustering fundamentals |
| PCA-StatArb | 29461658 | 0.165 | 1 | PCA stat arb |
| C41-MultiAsset-Rotation | 30809259 | 0.225 | 11 | Multi-asset rotation ML |
| RL-Options-Hedging-Ch07 | 30800109 | -1.264 | 5 | RL options hedging |
| Corrective-AI-Ch08 | 30800636 | -0.048 | 2 | Corrective AI |

### Cloud Projects (recently synced to local)

| Strategy | ID | Sharpe | BTs | Description |
|----------|----|--------|-----|-------------|
| Cloud-RegimeSwitching | 30823208 | 0.622 | 3 | Regime switching cloud |
| Cloud-SectorRotation-Momentum | 30821748 | 0.614 | 4 | Momentum-weighted sectors |
| Cloud-VolTargeting | 30823587 | 0.425 | 4 | Vol targeting variants |
| Cloud-DualMomentum-NoTLT | 30822524 | 0.392 | 3 | Antonacci no TLT |
| Cloud-MeanReversion-Sectors | 30822855 | 0.307 | 3 | RSI mean reversion sectors |
| Cloud-RiskParity-Composite | 30820857 | 0.278 | 4 | AQR risk parity composite |
| Research-Executor | 30867612 | N/A | 1 | Research notebook executor |

### Framework Composites

| Strategy | ID | Sharpe | BTs | Composition |
|----------|----|--------|-----|-------------|
| Framework_Composite_TrendWeather | 28825960 | **1.156** | 11 | Trend + AllWeather |
| Framework_Composite_EMATrend | 28911253 | 0.867 | 6 | EMA + Trend |
| Framework_Composite_FamaFrenchAllWeather | 28882145 | 0.546 | 19 | FF + AllWeather |
| Framework_Composite_TrendWeather (ESGF) | 28825740 | 0.619 | 1 | TrendWeather ESGF org |
| Framework_Composite_FamaFrenchAllWeather (ESGF) | 29032797 | 0.577 | 1 | FF/AW ESGF org |
| Framework_Composite_MomentumRegime | 28871239 | 0.241 | 4 | Momentum regime |

### ESGF Organization (Active)

| Strategy | ID | Sharpe | BTs | Status |
|----------|----|--------|-----|--------|
| ESGF-SectorMomentum | 29686886 | 0.509 | 4 | Active |
| ESGF-MomentumStrategy | 29686991 | 0.479 | 7 | Active |
| ESGF-ML-RandomForest | 29686996 | 0.130 | 1 | Suspicious |
| ESGF-ML-XGBoost | 29686997 | 0.130 | 1 | Suspicious |
| ESGF-Option-Wheel | 29687004 | 0.130 | 1 | Suspicious |
| ESGF-RL-DQN-Trading | 29687000 | -0.341 | 1 | Negative |
| ESGF-RegimeSwitching | 29686994 | N/A | 1 | Stats unavailable |
| ESGF-Framework-Composite | 29687005 | N/A | 0 | Framework stub |
| ESGF-Intermediate-Validation | 29540896 | 0.192 | 1 | Validation |
| ESGF-Advanced-Validation | 29540897 | 0.154 | 2 | Validation |

### HandsOn Exercises (Hands-On AI Trading)

| Strategy | ID | Sharpe | BTs | Chapter |
|----------|----|--------|-----|---------|
| HandsOn-Ex07-Positive-Negative-Splits | 30317350 | **1.736** | 2 | Ch07 |
| HandsOn-Gaussian-Direction-Classifier | 29398513 | 0.761 | 2 | Ch05 |
| HandsOn-Ex14-Temporal-CNN | 29816576 | 0.734 | 1 | Ch14 |
| HandsOn-Ex16-LLM-Summarization | 29936071 | 0.686 | 1 | Ch16 |
| HandsOn-Ex08-RL-DQN-Trading | 29443478 | 0.533 | 3 | Ch08 |
| HandsOn-Ex05-FX-SVM-Wavelet | 29816575 | 0.525 | 5 | Ch05 |
| HandsOn-Ex06-Dividend-Harvesting | 29443034 | 0.468 | 5 | Ch06 |
| HandsOn-Ex13-PCA-StatArbitrage | 29463543 | 0.399 | 3 | Ch13 |
| HandsOn-Markov-Regime-Detection | 29398512 | 0.375 | 7 | Ch04 |
| HandsOn-Ex15-Gaussian-Classifier | 29936070 | 0.361 | 1 | Ch15 |
| HandsOn-Ex18-Chronos-Foundation | 29936072 | 0.277 | 1 | Ch18 |
| HandsOn-Ex09-Chronos-Foundation | 29443479 | 0.253 | 9 | Ch09 |
| HandsOn-Ex12-TradingCosts-Optimization | 29463540 | 0.244 | 1 | Ch12 |
| HandsOn-Ex07-LSTM-Forecasting | 29443476 | 0.167 | 1 | Ch07 |
| HandsOn-Ex11-InverseVolatility-Rank | 29463533 | 0.124 | 7 | Ch11 |
| HandsOn-Ex08-Stoploss-Volatility-ML | 29463529 | N/A | 19 | Ch08 |
| HandsOn-Ex19-FinBERT-Sentiment | 29936073 | 0.000 | 1 | Ch19 |
| HandsOn-Ex10-Clustering-Fundamentals | 30317074 | -15.249 | 7 | Ch10 (broken) |

### Researcher Organization (Reference Implementations)

| Strategy | ID | Sharpe | BTs | Note |
|----------|----|--------|-----|------|
| BTC-MACD-ADX-Researcher 5 | 28418632 | **1.171** | 4 | Best researcher |
| Multi-Layer-EMA-Researcher | 28433748 | 0.900 | 9 | Multi-layer EMA |
| AllWeather-Researcher | 28657833 | 0.667 | 8 | AllWeather ref |
| Sector-Momentum-Researcher | 28433643 | 0.621 | 15 | Sector momentum |
| FamaFrench-Researcher | 28657910 | 0.540 | 3 | Fama-French |
| Option-Wheel-Researcher | 28433749 | 0.529 | 7 | Options wheel |
| MomentumStrategy-Researcher | 28657837 | 0.565 | 8 | Momentum ref |
| BTC-ML-Researcher | 28433750 | 0.281 | 6 | BTC ML |
| FuturesTrend-Researcher | 28657834 | 0.223 | 16 | Futures trend |
| OptionsIncome-Researcher | 28657838 | 0.213 | 9 | Options income |
| TurnOfMonth-Researcher | 28657905 | 0.119 | 14 | Turn of month |
| VIX-TermStructure-Researcher | 28657907 | -0.125 | 13 | VIX term structure |
| ForexCarry-Researcher | 28657908 | -0.849 | 17 | Forex carry |
| ETF-Pairs-Researcher 2 | 28433746 | -0.233 | 5 | ETF pairs |
| MeanReversion-Researcher | 28657904 | N/A | 10 | Stats unavailable |
| Crypto-MultiCanal-Researcher | 28679473 | 0.018 | 5 | Crypto multi |

### Structural Issues (negative Sharpe, preserved for analysis)

| Strategy | ID | Sharpe | BTs | Issue |
|----------|----|--------|-----|-------|
| PairsTrading | 28693651 | -1.152 | 8 | Structural flaw |
| RL-Options-Hedging-Ch07 | 30800109 | -1.264 | 5 | RL learning curve |
| ForexCarry-Researcher | 28657908 | -0.849 | 17 | Negative carry |
| TrendFilteredMeanReversion | 28817422 | -0.129 | 4 | Structural |
| VIX-TermStructure-Researcher | 28657907 | -0.125 | 13 | Negative |
| Corrective-AI-Ch08 | 30800636 | -0.048 | 2 | Experimental |
| ETF-Pairs-Researcher 2 | 28433746 | -0.233 | 5 | Structural |
| ESGF-RL-DQN-Trading | 29687000 | -0.341 | 1 | Negative |

## Imported Strategy Library (Detailed Cards)

8 strategies imported from QC Strategy Library and Quantpedia with full documentation.

### 1. Asset Class Momentum

- **Folder**: `projects-imported/asset-class-momentum/`
- **Source**: QC Strategy #278 (Keter Oak), Quantpedia Strategy #331
- **QC Cloud Project**: 29687233
- **Concept**: Momentum-based tactical asset allocation across 8 ETF classes. Monthly ranking by 12-month return, equal-weighted top-N selection.
- **Harmonized (2007-2026)**: Sharpe 0.153, CAGR 4.76%, MaxDD 55.3%

### 2. Volatility Regime ML

- **Folder**: `projects-imported/volatility-regime-ml/`
- **Source**: QC Strategy #224 (Derek Melchin)
- **QC Cloud Project**: 29687293
- **Concept**: RandomForest regime detection using VIX + FRED macro indicators. SPY position sizing by regime.
- **Harmonized (2008-2026)**: Sharpe 1.29, CAGR 24.99%, MaxDD 19.1%

### 3. Defensive ETF Rotation

- **Folder**: `projects-imported/defensive-etf-rotation/`
- **Source**: QC Strategy #54 (Nathan Swenson), Quantpedia Strategy #383
- **QC Cloud Project**: N/A (not cloned)
- **Concept**: Dual momentum defensive rotation. Falls to SHY when all negative.
- **Status**: No cloud project

### 4. Puppies of the Dow

- **Folder**: `projects-imported/puppies-of-dow/`
- **Source**: QC Strategy #366 (Louis Szeto), Quantpedia Strategy #356
- **QC Cloud Project**: 29687759
- **Concept**: Dogs of the Dow + Puppies (high yield + low price). Annual universe refresh.
- **Harmonized (2005-2026)**: Sharpe 0.386, CAGR 10.86%, MaxDD 54.2%

### 5. Macro Factor Rotation

- **Folder**: `projects-imported/macro-factor-rotation/`
- **Source**: QC Strategy #72 (Derek Melchin)
- **QC Cloud Project**: 29687828
- **Concept**: DecisionTreeRegressor with VIX, yield curve, fed funds. 150% gross exposure.
- **Harmonized (2013-2026)**: Sharpe 0.927, CAGR 27.20%, MaxDD 41.9%

### 6. Long-Short Harvest

- **Folder**: `projects-imported/long-short-harvest/`
- **Source**: QC Strategy #69 (Jared Broad), Quantpedia Strategy #15
- **QC Cloud Project**: 29687399
- **Concept**: Long-short equity. Top decile momentum = long, bottom = short. ATR trailing stops.
- **Harmonized (2005-2026)**: Sharpe 1.505, CAGR 40.15%, MaxDD 16.7%

### 7. Piotroski F-Score Quality Value

- **Folder**: `projects-imported/piotroski-fscore/`
- **Source**: QC Strategy #343 (Louis Szeto), Piotroski (2000)
- **QC Cloud Project**: 29687591
- **Concept**: Top 20% by book-to-market, filtered for F-Score >= 8. 9-component accounting score.
- **Harmonized (2005-2026)**: Sharpe 0.362, CAGR 11.82%, MaxDD 60.3%

### 8. Commodity Term Structure

- **Folder**: `projects-imported/commodity-term-structure/`
- **Source**: QC Strategy #26, Quantpedia Strategy #22
- **QC Cloud Project**: 29688398
- **Concept**: Long-short commodity futures based on roll returns. 21 futures across 5 sectors.
- **Harmonized (2005-2026)**: Sharpe 0.009, CAGR -11.39%, MaxDD 97.5%

## Backtest Workflow

To verify each strategy via QC MCP:

```
1. Get project ID from cloud-id file
2. create_compile(projectId) -> compileId
3. read_compile(projectId, compileId) -> state == "BuildSuccess"
4. create_backtest(projectId, compileId, "name") -> backtestId
5. read_backtest(projectId, backtestId) -> statistics
```

## Source Attribution

Strategies from [QuantConnect Strategy Library](https://www.quantconnect.com/strategies/) and [Quantpedia](https://quantpedia.com/). Each strategy retains its original author attribution and license (QuantConnect Community Strategy - open source unless otherwise noted).
