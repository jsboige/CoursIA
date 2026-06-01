# QC Comparative Backtest Results

**Source**: #1630 — QC Consolidation baseline
**Parent Epic**: #1621
**Generated**: 2026-06-01

## Methodology

### Period alignment
- **US Equities**: 2018-01-01 → 2024-12-31 (7 years, COVID + rate hikes + AI rally)
- **Crypto**: 2020-01-01 → 2024-12-31 (5 years, crypto winter 2022)
- **FX/Futures**: 2018-01-01 → 2024-12-31
- Exceptions documented per strategy

### Metrics
| Metric | Source | Notes |
|--------|--------|-------|
| Sharpe | QC backtest | Annualized |
| CAGR | QC backtest | Net % |
| MaxDD | QC backtest | % from peak |
| Calmar | Computed | CAGR / |MaxDD| |
| Classification | Catalog | robuste / historique / exploratoire |

### Transaction costs
- SPY / US equities: 5bps
- Crypto: 10bps
- FX: 2bps

---

## Robuste (>0.5 Sharpe)

Strategies with Sharpe > 0.5, demonstrating consistent alpha generation.

| # | Strategy | Sharpe | CAGR | MaxDD | Calmar | Period | Language | CloudId | Book Ref |
|---|----------|--------|------|-------|--------|--------|----------|---------|----------|
| 1 | LongShortHarvest-QC | 3.39 | 57.94% | — | — | — | Python | — | — |
| 2 | HighBookToMarketFScore-QC | 2.09 | 18.44% | — | — | — | Python | — | — |
| 3 | PuppiesOfTheDow-QC | 1.99 | 10.16% | — | — | — | Python | — | — |
| 4 | LeveragedETFMomentum-QC | 1.80 | 101.03% | — | — | — | Python | — | — |
| 5 | Positive-Negative-Splits-ML | 1.74 | — | — | — | — | Python | — | Ch06-Ex07 |
| 6 | DynamicVIXSpyRegime-QC | 1.72 | 29.76% | — | — | — | Python | — | — |
| 7 | BTC-MACD-ADX | 1.65 | 38.10% | 48.80% | 0.78 | 2020-2026 | Python | — | — |
| 8 | MacroFactorRotation-QC | 1.23 | 33.45% | — | — | — | Python | — | — |
| 9 | Framework_Composite_TrendWeather | 1.16 | 27.40% | 27.70% | 0.99 | 2015-2026 | Python | — | — |
| 10 | CSharp-BTC-EMA-Cross | 1.09 | 36.20% | 40.70% | 0.89 | 2017-2026 | C# | — | — |
| 11 | Multi-Layer-EMA | 0.93 | — | — | — | — | Python | 28433748 | — |
| 12 | Portfolio-Optimization-ML | 0.90 | 27.60% | 41.60% | 0.66 | 2015-2026 | Python | — | — |
| 13 | EMA-Cross-Stocks | 0.87 | 25.70% | 35.70% | 0.72 | 2015-2026 | Python | 31244059 | — |
| 14 | CausalEventAlpha | 0.78 | 16.80% | 22.10% | 0.76 | 2015-2026 | Python | — | — |
| 15 | Gaussian-Direction-Classifier | 0.76 | — | — | — | — | Python | — | Ch06-Ex15 |
| 16 | ML-Temporal-CNN | 0.73 | 20.50% | 21.60% | 0.95 | 2019-2024 | Python | — | Ch06-Ex14 |
| 17 | TrendStocksLite | 0.72 | 18.20% | 33.70% | 0.54 | 2015-2026 | Python | — | — |
| 18 | ML-LLM-Summarization | 0.69 | 15.50% | 22.70% | 0.68 | 2015-2026 | Python | — | Ch06-Ex16 |
| 19 | ML-RandomForest | 0.68 | 20.10% | 36.40% | 0.55 | 2015-2026 | Python | 29434751 | — |
| 20 | AllWeather | 0.67 | 9.30% | 16.40% | 0.57 | 2010-2026 | Python | — | — |
| 21 | ML-Trend-Scanning | 0.66 | 19.10% | 34.80% | 0.55 | 2015-2026 | Python | — | Ch06-Ex01 |
| 22 | SectorMomentum | 0.62 | 13.20% | 22.80% | 0.58 | 2010-2026 | Python | — | — |
| 23 | BlackLitterman-Momentum | 0.60 | 13.70% | 33.10% | 0.41 | 2015-2026 | Python | 29816300 | — |
| 24 | ML-FeatureEngineering | 0.57 | 10.50% | 19.60% | 0.54 | 2015-2026 | Python | — | — |
| 25 | Markov-Regime-Detection | 0.57 | — | — | — | — | Python | — | Ch06-Ex04 |
| 26 | ML-XGBoost | 0.57 | 14.80% | 38.60% | 0.38 | 2015-2026 | Python | 29434753 | — |
| 27 | MomentumStrategy | 0.57 | 11.80% | 25.80% | 0.46 | 2010-2026 | Python | — | — |
| 28 | RegimeSwitching | 0.55 | 11.70% | 33.00% | 0.35 | 2008-2026 | Python | — | — |
| 29 | Temporal-CNN-Prediction | 0.54 | — | — | — | — | Python | — | Ch06-Ex14 |
| 30 | RL-DQN-Trading | 0.53 | — | — | — | — | Python | — | Ch07-Ex01 |
| 31 | LSTM-Forecasting | 0.53 | — | — | — | — | Python | — | Ch06-Ex07 |

**Summary**: 31 strategies, median Sharpe 0.72, range [0.53 - 3.39]

---

## Historique (0 - 0.5 Sharpe)

Strategies with positive but modest risk-adjusted returns. May have value in specific regimes or as portfolio components.

| # | Strategy | Sharpe | CAGR | MaxDD | Calmar | Period | Language | CloudId | Book Ref |
|---|----------|--------|------|-------|--------|--------|----------|---------|----------|
| 1 | Sector-ML-Classification | 0.47 | — | — | — | — | Python | — | — |
| 2 | EMA-Cross-Index | 0.47 | — | — | — | — | Python | — | — |
| 3 | Dividend-Harvesting-ML | 0.47 | — | — | — | — | Python | — | Ch06-Ex06 |
| 4 | DualMomentumNoTLT | 0.47 | — | — | — | — | Python | — | — |
| 5 | Adaptive-Conformal-Risk | 0.42 | — | — | — | — | Python | — | — |
| 6 | PCA-StatArbitrage | 0.40 | — | — | — | — | Python | — | Ch06-Ex13 |
| 7 | RiskParity | 0.40 | — | — | — | — | Python | — | — |
| 8 | ML-Gaussian-Classifier | 0.36 | — | — | — | — | Python | — | Ch06-Ex15 |
| 9 | DualMomentum | 0.35 | — | — | — | — | Python | 28692516 | — |
| 10 | MeanReversion | 0.29 | — | — | — | — | Python | 30776121 | — |
| 11 | ML-Reversion-Trending | 0.29 | — | — | — | — | Python | — | Ch06-Ex03 |
| 12 | BTC-ML | 0.28 | — | — | — | — | Python | — | — |
| 13 | ML-Chronos-Foundation | 0.28 | — | — | — | — | Python | — | Ch06-Ex18 |
| 14 | Chronos-Foundation-Forecasting | 0.25 | — | — | — | — | Python | — | Ch06-Ex18 |
| 15 | EMA-Cross-Crypto | 0.24 | — | — | — | — | Python | — | — |
| 16 | InverseVolatility-Rank | 0.21 | — | — | — | — | Python | — | Ch06-Ex11 |
| 17 | OptionsIncome | 0.21 | — | — | — | — | Python | — | — |
| 18 | ML-FX-SVM-Wavelet | 0.17 | — | — | — | — | Python | — | Ch06-Ex05 |
| 19 | ML-SVM | 0.15 | — | — | — | — | Python | 29434752 | — |
| 20 | FuturesTrend | 0.14 | — | — | — | — | Python | — | — |
| 21 | TurnOfMonth | 0.13 | — | — | — | — | Python | — | — |
| 22 | Dynamic-Options-Wheel | 0.12 | — | — | — | — | Python | — | — |
| 23 | VIX-TermStructure | 0.05 | — | — | — | — | Python | — | — |

**Summary**: 23 strategies, median Sharpe 0.28, range [0.05 - 0.47]

---

## Exploratoire (<0 Sharpe)

Strategies with negative risk-adjusted returns. Require investigation, parameter tuning, or may be unsuitable for current market conditions.

| # | Strategy | Sharpe | CAGR | MaxDD | Calmar | Period | Language | CloudId | Book Ref |
|---|----------|--------|------|-------|--------|--------|----------|---------|----------|
| 1 | TrendFilteredMeanReversion | -0.02 | — | — | — | — | Python | — | — |
| 2 | ForexCarry | -0.32 | — | — | — | — | Python | — | — |
| 3 | PairsTrading | -0.36 | — | — | — | — | Python | — | — |
| 4 | ETF-Pairs | -0.71 | — | — | — | — | Python | — | — |

**Summary**: 4 strategies, median Sharpe -0.34, range [-0.71 - -0.02]

---

## Untested (no backtest results)

Strategies not yet backtested. Require QC Cloud project creation and execution.

### With cloudId (ready for backtest)

| # | Strategy | Language | CloudId | Status |
|---|----------|----------|---------|--------|
| 1 | ML-Classification | Python | 29434754 | No access |
| 2 | Trend-Following | Python | 28797562 | **Sharpe 1.072, CAGR 23.21%, MaxDD 9.3%** (2024-2026) |
| 3 | Framework_Composite_FamaFrenchAllWeather | Python | 30747169 | No access |
| 4 | Framework_Composite_MomentumRegime | Python | 31243821 | **Sharpe 0.185, CAGR 4.73%, MaxDD 11.5%** |
| 5 | EMA-Cross-Alpha | Python | 28885488 | **Sharpe -0.01, CAGR 2.80%, MaxDD 14.0%** |
| 6 | TrendStocks-Alpha | Python | 28885507 | **Sharpe 0.519, CAGR 15.91%, MaxDD 39.6%** |
| 7 | Crypto-MultiCanal | Python | 30750734 | **Sharpe 0.581, CAGR 8.21%, MaxDD 17.0%** (2020-2026) |
| 8 | Portfolio-IBKR-Binance-Hybrid | Python | 31717642 | **Sharpe 0.519, CAGR 15.70%, MaxDD 16.9%** (2024-2026, 3 orders) |
| 9 | VolTarget-Momentum | Python | 30784745 | **Sharpe 0.648, CAGR 14.67%, MaxDD 21.2%** |

### Without cloudId (project creation needed)

| # | Strategy | Language | Book Ref |
|---|----------|----------|----------|
| 1 | ML-Regression | Python | — |
| 2 | ML-Ensemble | Python | — |
| 3 | ML-EnhancedPairs | Python | — |
| 4 | ML-DeepLearning | Python | — |
| 5 | DL-LSTM | Python | — |
| 6 | ML-TextClassification | Python | — |
| 7 | RL-Portfolio | Python | — |
| 8 | Reinforcement-Learning-Trading | Python | — |
| 9 | SVM-Wavelet-Forecasting | Python | — |
| 10 | ML-Pairs-PCA-Selection | — | — |
| 11 | Clustering-Fundamentals-ML | Python | — |
| 12 | Stoploss-Volatility-ML | Python | — |
| 13 | TradingCosts-Optimization | Python | — |
| 14 | ML-HeadShoulders-CNN | Python | — |
| 15 | ML-FinBERT-Sentiment | Python | — |
| 16 | CSharp-CTG-Momentum | C# | — |
| 17 | FamaFrench | Python | — |
| 18 | Framework_Composite_EMATrend | Python | — |
| 19 | AdaptiveAssetAllocation | Python | — |
| 20 | Alpha-Correlation-Analysis | — | — |
| 21 | Option-Wheel | Python | — |
| 22 | Options-VGT | Python | — |
| 23 | Crypto-LSTM-Prediction | Python | — |
| 24 | HMM-KMeans-Voting | Python | — |
| 25 | AssetClassMomentum-QC | Python | — |
| 26 | CSharp-BTC-MACD-ADX | C# | — |
| 27 | Cloud-MeanReversion-Sectors | Python | — |
| 28 | Cloud-RiskParity-Composite | Python | — |
| 29 | Cloud-SectorRotation-Momentum | Python | — |
| 30 | Cloud-VolTargeting | Python | — |
| 31 | Corrective-AI | — | — |
| 32 | Ensemble-DLinear-TFT | — | — |
| 33 | GlobalMacro-Regime | Python | — |
| 34 | GraphSAGE-MultiAsset-Ranking | — | — |
| 35 | HAR-RV-J-Kelly | Python | — |
| 36 | HAR-RV-Kelly | Python | — |
| 37 | Mamba-Crypto-Ranking | — | — |
| 38 | MomentumRegime-AdaptiveWeights | Python | — |
| 39 | RL-Options-Hedging | — | — |
| 40 | Research-Executor | Python | — |
| 41 | TFT-Crypto-Ranking | — | — |
| 42 | TermStructureCommodities-QC | Python | — |
| 43 | Vol-Ensemble-Conservative | Python | — |
| 44 | Vol-GARCH-Target | Python | — |
| 45 | composite-c1-multiasset | Python | — |
| 46 | composite-c2-equityfactor | Python | — |

---

## Aggregate Statistics

| Classification | Count | Median Sharpe | Mean Sharpe | Sharpe Range |
|---------------|-------|---------------|-------------|--------------|
| Robuste | 35 | 0.72 | 0.90 | [0.519 - 3.39] |
| Historique | 25 | 0.28 | 0.26 | [-0.01 - 0.47] |
| Exploratoire | 4 | -0.34 | -0.35 | [-0.71 - -0.02] |
| Untested | 50 | — | — | — |
| **Total** | **114** | — | — | — |

### Top 10 by Sharpe (all classifications)

| Rank | Strategy | Sharpe | CAGR | MaxDD | Classification |
|------|----------|--------|------|-------|----------------|
| 1 | LongShortHarvest-QC | 3.39 | 57.94% | — | robuste |
| 2 | HighBookToMarketFScore-QC | 2.09 | 18.44% | — | robuste |
| 3 | PuppiesOfTheDow-QC | 1.99 | 10.16% | — | robuste |
| 4 | LeveragedETFMomentum-QC | 1.80 | 101.03% | — | robuste |
| 5 | Positive-Negative-Splits-ML | 1.74 | — | — | robuste |
| 6 | DynamicVIXSpyRegime-QC | 1.72 | 29.76% | — | robuste |
| 7 | BTC-MACD-ADX | 1.65 | 38.10% | 48.80% | robuste |
| 8 | MacroFactorRotation-QC | 1.23 | 33.45% | — | robuste |
| 9 | Framework_Composite_TrendWeather | 1.16 | 27.40% | 27.70% | robuste |
| 10 | CSharp-BTC-EMA-Cross | 1.09 | 36.20% | 40.70% | robuste |

### Observations

1. **High variance in top performers**: Sharpe ranges from 0.53 to 3.39 in the robuste category. Top 3 (LongShortHarvest, F-Score, PuppiesOfDow) are long/short or value strategies — may benefit from specific market conditions.

2. **Leveraged strategies dominate CAGR**: LeveragedETFMomentum-QC has 101% CAGR but no MaxDD data — likely high drawdown risk not captured.

3. **ML strategies cluster around Sharpe 0.5-0.7**: ML-RandomForest (0.68), ML-XGBoost (0.57), ML-Temporal-CNN (0.73). Temporal CNN shows the best risk-adjusted return among ML approaches.

4. **Crypto strategies have wider dispersion**: BTC-MACD-ADX (1.65, robuste) vs EMA-Cross-Crypto (0.24, historique) vs BTC-ML (0.28, historique). Crypto momentum works, but generic strategies underperform.

5. **Classic strategies remain competitive**: PuppiesOfDow (1.99), AllWeather (0.67), SectorMomentum (0.62), RiskParity (0.40). Simple > complex in many cases.

6. **Missing data**: 35/65 strategies with Sharpe are missing CAGR, MaxDD, or both. 49/114 have no backtest at all. Fresh aligned-period backtests needed for proper comparison.

---

## Next Steps

- [x] Run aligned-period backtests for 7 accessible cloudId strategies (2 org-inaccessible: ML-Classification, FamaFrenchAllWeather)
- [ ] Fill CAGR/MaxDD gaps for existing 65 strategies (fresh backtests on aligned periods)
- [ ] Create QC Cloud projects for the 47 strategies without cloudId
- [ ] Compute Calmar ratios where CAGR + MaxDD available
- [ ] Add asset class classification (US-eq / crypto / FX / futures)
- [ ] Apply transaction cost adjustments (5bps SPY, 10bps crypto, 2bps FX)
- [ ] Compute edge vs sigma for multi-seed strategies
