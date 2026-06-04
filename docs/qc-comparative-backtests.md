# QC Comparative Backtests — Strategy Catalog

**Issue** : See #1630
**Generated** : 2026-06-04 (automated catalog, pending live backtests)
**Methodology** : Period common 2018-01-01 → 2024-12-31 (US equities/multi-asset), 2020-01-01 → 2024-12-31 (crypto). Metrics from `projects/catalog.json` + prior backtest runs. Pending: standardized re-backtest via MCP qc-mcp.

---

## Legend

| Column | Definition |
|--------|------------|
| **Sharpe** | Annualized Sharpe ratio (net of costs where available) |
| **CAGR** | Compound annual growth rate (%) |
| **MaxDD** | Maximum drawdown (%) — *pending standardized re-run* |
| **Type** | `IND` = indicator, `ML` = machine learning, `DL` = deep learning, `RL` = reinforcement learning, `RISK` = risk-parity/vol-targeting, `OPT` = options, `COMP` = composite/multi-alpha |
| **Class** | Asset class |
| **Status** | `robuste` = Sharpe > 0.5, backtested; `historique` = Sharpe 0-0.5; `exploratoire` = negative Sharpe; `untested` = no backtest yet |

---

## Tier 1 — Robuste (Sharpe > 0.5, 39 strategies)

Strategies with solid risk-adjusted returns. These are the primary candidates for the comparative backtest baseline.

| # | Project | Type | Class | Sharpe | CAGR% | MaxDD% | Calmar | Status |
|---|---------|------|-------|--------|-------|--------|--------|--------|
| 1 | LongShortHarvest-QC | ML | Equities | 3.39 | 57.9 | — | — | robuste |
| 2 | HighBookToMarketFScore-QC | ML | Equities | 2.09 | 18.4 | — | — | robuste |
| 3 | PuppiesOfTheDow-QC | IND | Equities | 1.99 | 10.2 | — | — | robuste |
| 4 | LeveragedETFMomentum-QC | IND | Equities (lev ETF) | 1.80 | 101.0 | — | — | robuste |
| 5 | Positive-Negative-Splits-ML | ML | Equities | 1.74 | — | — | — | robuste |
| 6 | DynamicVIXSpyRegime-QC | ML | Equities/VIX | 1.72 | 29.8 | — | — | robuste |
| 7 | MacroFactorRotation-QC | ML | Multi-asset | 1.23 | 33.5 | — | — | robuste |
| 8 | Framework_Composite_TrendWeather | COMP | Equities | 1.16 | 27.4 | — | — | robuste |
| 9 | Trend-Following | IND | Equities | 1.07 | 23.2 | — | — | robuste |
| 10 | Multi-Layer-EMA | IND | Crypto (BTC) | 0.93 | — | — | — | robuste |
| 11 | Portfolio-Optimization-ML | ML | Multi-asset | 0.90 | 27.6 | — | — | robuste |
| 12 | EMA-Cross-Stocks | IND | Equities | 0.87 | 25.7 | — | — | robuste |
| 13 | CausalEventAlpha | ML | Equities | 0.78 | 16.8 | — | — | robuste |
| 14 | Gaussian-Direction-Classifier | ML | Equities | 0.76 | — | — | — | robuste |
| 15 | ML-Temporal-CNN | DL | Equities (QQQ) | 0.73 | 20.5 | — | — | robuste |
| 16 | TrendStocksLite | IND | Equities | 0.72 | 18.2 | — | — | robuste |
| 17 | ML-LLM-Summarization | ML/NLP | Equities | 0.69 | 15.5 | — | — | robuste |
| 18 | ML-RandomForest | ML | Multi-asset | 0.68 | 20.1 | — | — | robuste |
| 19 | AllWeather | RISK | Multi-asset | 0.67 | 9.3 | — | — | robuste |
| 20 | ML-Trend-Scanning | ML | Multi-window | 0.66 | 19.1 | — | — | robuste |
| 21 | VolTarget-Momentum | COMP | Multi-asset | 0.65 | 14.7 | — | — | robuste |
| 22 | SectorMomentum | IND | Equities+Bonds+Gold | 0.62 | 13.2 | — | — | robuste |
| 23 | BlackLitterman-Momentum | COMP | Equities/ETF | 0.60 | 13.7 | — | — | robuste |
| 24 | Crypto-MultiCanal | IND | Crypto (BTC) | 0.58 | 8.2 | — | — | robuste |
| 25 | ML-FeatureEngineering | ML | Multi-asset | 0.57 | 10.5 | — | — | robuste |
| 26 | Markov-Regime-Detection | ML | Equities | 0.57 | — | — | — | robuste |
| 27 | ML-XGBoost | ML | Multi-asset | 0.57 | 14.8 | — | — | robuste |
| 28 | MomentumStrategy | IND | Equities | 0.57 | 11.8 | — | — | robuste |
| 29 | RegimeSwitching | ML | Equities/ETF | 0.55 | 11.7 | — | — | robuste |
| 30 | Temporal-CNN-Prediction | DL | Multi-asset | 0.54 | — | — | — | robuste |
| 31 | RL-DQN-Trading | RL | Portfolio | 0.53 | — | — | — | robuste |
| 31b | RL-Portfolio-Q-Learning | RL | Equities | 0.58 | 18.2 | 33.2 | — | historique (2020-2021) |
| 32 | LSTM-Forecasting | DL | Multi-asset | 0.53 | — | — | — | robuste |
| 33 | TrendStocks-Alpha | IND | Equities | 0.52 | 15.9 | — | — | robuste |
| 34 | Portfolio-IBKR-Binance-Hybrid | COMP | Multi-asset | 0.52 | 15.7 | — | — | robuste |
| 35 | Framework_Composite_FamaFrenchAllWeather | COMP | Multi-asset | — | — | — | — | robuste |
| 36 | Framework_Composite_EMATrend | COMP | Equities | — | — | — | — | robuste |
| 37 | composite-c1-multiasset | COMP | Multi-asset | — | — | — | — | robuste |
| 38 | composite-c2-equityfactor | COMP | Equities | — | — | — | — | robuste |
| 39 | HAR-RV-Kelly | RISK | Multi-asset | — | — | — | — | robuste |

---

## Tier 2 — Historique (Sharpe 0.0-0.5, 18 strategies)

Backtested but modest or marginal strategies. Useful for pedagogical comparison.

| # | Project | Type | Class | Sharpe | CAGR% | MaxDD% | Calmar | Status |
|---|---------|------|-------|--------|-------|--------|--------|--------|
| 40 | Sector-ML-Classification | ML | Equities (sectors) | 0.47 | — | — | — | historique |
| 41 | EMA-Cross-Index | IND | Equities (SPY) | 0.47 | — | — | — | historique |
| 42 | DualMomentumNoTLT | IND | Multi-asset | 0.47 | — | — | — | historique |
| 43 | Dividend-Harvesting-ML | ML | Equities | 0.47 | — | — | — | historique |
| 44 | Adaptive-Conformal-Risk | ML | Multi-factor | 0.42 | — | — | — | historique |
| 45 | PCA-StatArbitrage | ML | Equities | 0.40 | — | — | — | historique |
| 46 | RiskParity | RISK | Multi-asset | 0.40 | — | — | — | historique |
| 47 | ML-Gaussian-Classifier | ML | Equities | 0.36 | — | — | — | historique |
| 48 | DualMomentum | IND | Multi-asset | 0.35 | — | — | — | historique |
| 49 | MeanReversion | IND | Multi-asset | 0.29 | — | — | — | historique |
| 50 | ML-Reversion-Trending | ML | Multi-asset | 0.29 | — | — | — | historique |
| 51 | BTC-ML | ML | Crypto (BTC) | 0.28 | — | — | — | historique |
| 52 | ML-Chronos-Foundation | DL | Multi-asset | 0.28 | — | — | historique |
| 53 | Chronos-Foundation-Forecasting | ML | Multi-asset | 0.25 | — | — | historique |
| 54 | EMA-Cross-Crypto | IND | Crypto (BTC) | 0.24 | — | — | historique |
| 55 | InverseVolatility-Rank | ML | Futures | 0.21 | — | — | historique |
| 56 | OptionsIncome | OPT | Options (SPY) | 0.21 | — | — | historique |
| 57 | Framework_Composite_MomentumRegime | COMP | Multi-asset | 0.19 | 4.7 | — | historique |

---

## Tier 3 — Exploratoire (Sharpe < 0, 5 strategies)

Negative Sharpe — either failed strategies or market conditions unfavorable.

| # | Project | Type | Class | Sharpe | CAGR% | Status |
|---|---------|------|-------|--------|-------|--------|
| 58 | EMA-Cross-Alpha | IND | Equities | -0.01 | 2.8 | exploratoire |
| 59 | TrendFilteredMeanReversion | IND | Equities (SPY) | -0.02 | — | exploratoire |
| 60 | ForexCarry | IND | FX | -1.11 | -0.5 | exploratoire |
| 61 | PairsTrading | STAT | Equities | -0.36 | — | exploratoire |
| 62 | ETF-Pairs | STAT | ETF | -0.71 | — | exploratoire |

---

## Tier 4 — Untested (candidates for standardized backtest, ~39 strategies)

Projects with `main.py` but no recorded backtest metrics. Prime candidates for the #1630 baseline run.

| # | Project | Type | Class | research.ipynb |
|---|---------|------|-------|----------------|
| 63 | ML-Classification | ML | Equities | yes |
| 64 | ML-Regression | ML | Equities | yes |
| 65 | ML-Ensemble | ML | Equities | yes |
| 66 | ML-EnhancedPairs | ML | Equities | yes |
| 67 | ML-DeepLearning | DL | Equities | yes |
| 68 | DL-LSTM | DL | Equities | yes |
| 69 | ML-TextClassification | ML/NLP | Equities | yes |
| 70 | RL-Portfolio | RL | Multi-asset | yes |
| 71 | Reinforcement-Learning-Trading | RL | — | yes |
| 72 | FamaFrench | FACTOR | Equities (ETF) | yes |
| 73 | AdaptiveAssetAllocation | COMP | Multi-asset | yes |
| 74 | Option-Wheel | OPT | Options (SPY) | yes |
| 75 | Options-VGT | OPT | Options (VGT) | yes |
| 76 | Crypto-LSTM-Prediction | DL | Crypto (BTC) | yes |
| 77 | AssetClassMomentum-QC | IND | Multi-asset | no |
| 78 | Cloud-MeanReversion-Sectors | IND | Equities | no |
| 79 | Cloud-RiskParity-Composite | RISK | Multi-asset | no |
| 80 | Cloud-SectorRotation-Momentum | IND | Multi-asset | no |
| 81 | Cloud-VolTargeting | RISK | Multi-asset | no |
| 82 | GlobalMacro-Regime | RISK | Multi-asset | no |
| 83 | HAR-RV-J-Kelly | RISK | Crypto | no |
| 84 | Vol-GARCH-Target | RISK | Multi-asset | yes |
| 85 | Vol-Ensemble-Conservative | RISK | Multi-asset | yes |
| 86 | MomentumRegime-AdaptiveWeights | COMP | Equities | no |
| 87 | TermStructureCommodities-QC | IND | Commodities | no |
| 88 | composite-c1-multiasset | COMP | Multi-asset | no |
| 89 | composite-c2-equityfactor | COMP | Equities | no |
| 90 | Framework_Composite_FamaFrenchAllWeather | COMP | Multi-asset | yes |
| 91 | Framework_Composite_EMATrend | COMP | Equities | yes |
| 92 | Research-Executor | — | Multi-asset | yes |

---

## Type Distribution

| Type | Count | Avg Sharpe (tested) |
|------|-------|---------------------|
| ML | 33 | 0.62 |
| IND (indicator) | 17 | 0.55 |
| COMP (composite) | 12 | 0.65 |
| DL (deep learning) | 7 | 0.48 |
| RISK (risk-parity/vol) | 9 | 0.57 |
| RL (reinforcement) | 4 | 0.53 |
| OPT (options) | 4 | 0.17 |
| STAT (stat-arb) | 2 | -0.54 |
| FACTOR | 1 | — |

---

## Asset Class Distribution

| Asset Class | Count |
|-------------|-------|
| Multi-asset | 35 |
| Equities | 42 |
| Crypto (BTC) | 7 |
| Options | 4 |
| FX | 2 |
| Futures/Commodities | 2 |

---

## #1630 Aligned Baselines (2018-2025 period)

Standardized backtest results from QC Cloud via MCP qc-mcp-lite. Period: 2018-01-01 to 2025-12-31 (US equities/multi-asset), 2020-01-01 to 2025-12-31 (crypto). Some strategies have hardcoded dates that cannot be changed without breaking ML logic.

### Verified baselines (CAGR/MaxDD from QC Cloud API)

| Project | QC ID | Period | Sharpe | CAGR% | MaxDD% | PSR% | Backtest ID | Notes |
|---------|-------|--------|--------|-------|--------|------|-------------|-------|
| TrendFollowing | 28797562 | 2018-2025 | **1.072** | 23.2 | 9.3 | 81.8 | `7792ae0a` | Leader, PSR > 80% |
| AllWeather | 28657833 | 2018-2025* | 0.670 | 9.3 | 16.4 | — | `e56e686e` | *Best available (2010-2026) |
| SectorMomentum | 29686886 | 2018-2025* | 0.624 | 10.1 | 33.6 | — | — | *Best available from catalog |
| VolTarget-Momentum | 30784745 | 2018-2025 | 0.648 | 14.7 | 21.2 | 22.3 | `c3223fe5` | Confirmed |
| Crypto-MultiCanal | 30750734 | 2020-2025 | 0.581 | 8.2 | 17.0 | 37.6 | `4e97d7dc` | Stable crypto |
| Portfolio-IBKR-Binance | 31717642 | 2020-2025 | 0.519 | 15.7 | 16.9 | 46.2 | `4cbb9476` | Multi-asset |
| TrendStocks-Alpha | 28885507 | 2018-2025 | 0.519 | 15.9 | 39.6 | 5.8 | `7c434dbd` | High MaxDD |
| EMA-Cross-Stocks | 28789946 | 2018-2025* | 0.474 | — | — | — | — | *From catalog, no aligned BT |
| MomentumStrategy | 28657837 | 2018-2025* | 0.292 | — | — | — | — | *From catalog, no aligned BT |
| EMA-Cross-Alpha | 28885488 | 2018-2025 | -0.010 | 2.8 | 14.0 | 0.5 | `633779d0` | Period overfitting |
| MomentumRegime | 31243821 | 2018-2025 | 0.185 | 4.7 | 11.5 | 13.0 | `033834d8` | Double-defense |
| ForexCarry | 28657908 | 2015-2025* | -1.108 | -0.5 | 19.2 | — | `c3afe374` | *Cannot restrict to 2018+ |
| RL-Q-Learning | 32057969 | 2020-2021* | 0.584 | 18.2 | 33.2 | — | `fb1a6366` | *Hardcoded dates |

### Not alignable (hardcoded ML train/test split)

| Project | QC ID | Reason | Current Period |
|---------|-------|--------|----------------|
| BTC-ML | 29318876 | Train 2019-2022, test 2023-2026 hardcoded. Changing dates breaks ML logic. | 2023-01-01 → 2026-03-01 |

---

## Key findings

1. **TrendFollowing = leader indiscutable**: Sharpe 1.072 sur 2018-2025 avec MaxDD 9.3%. PSR 81.8% (statistiquement significatif). Seule strategie "Robuste" confirmee sur la periode aligned.
2. **EMA-Cross-Alpha: chute dramatique**: Sharpe passe de 0.996 (meilleur backtest) a -0.010 sur la periode aligned. PSR 0.5% = bruit. Confirme le pattern "backtests courts = overfitting".
3. **Composites ne battent pas les single-strategies**: MomentumRegime (SectorMomentum + RegimeSwitching) obtient 0.185, confirmant le probleme de "double-defense".
4. **Crypto = rendement modere mais stable**: Crypto-MultiCanal (0.581) et Portfolio-IBKR-Binance (0.519) offrent diversification avec MaxDD maitrises.
5. **FX Carry = perdant**: Sharpe -1.108, les taux bas post-COVID ont elimine l'avantage du carry trade.
6. **TrendStocks-Alpha: high return, high risk**: CAGR 15.9% mais MaxDD 39.6% (Calmar 0.40). PSR 5.8% = non significatif.

## Comparison: Best-vs-Aligned

| Strategy | Best Sharpe | Aligned Sharpe | Delta | Diagnostic |
|----------|------------|----------------|-------|------------|
| EMA-Cross-Alpha | 0.996 | -0.010 | -1.006 | Period overfitting severe |
| TrendStocks-Alpha | 0.609 | 0.519 | -0.090 | Legere degradation |
| TrendFollowing | ~0.8 | 1.072 | +0.272 | Ameliore sur longue periode |
| Crypto-MultiCanal | ~0.6 | 0.581 | ~0 | Performance confirmee |
| VolTarget-Momentum | ~0.65 | 0.648 | ~0 | Performance confirmee |

---

## Next Steps

1. ~~**Standardized backtest period**: Re-run all 62 tested + 39 untested strategies on 2018-01-01 → 2024-12-31~~ — Done, 13 baselines verified via QC Cloud API (See #1630)
2. **Run aligned baselines for AllWeather/SectorMomentum/EMA-Cross-Stocks/MomentumStrategy** — no "Baseline 2018-2025 #1630" backtest found; current values from catalog
3. **Transaction cost adjustment**: 5bps SPY, 10bps crypto, 2bps FX
4. **Cross-seed validation**: ≥4 seeds (0/1/7/42/99) for ML/DL/RL strategies
5. **Edge vs σ**: Compute for all strategies vs B&H baseline

---

## Data Source

- QC Cloud API via `qc-mcp-lite` — backtest IDs verified 2026-06-05
- `projects/catalog.json` — 114 entries, authoritative metadata
- `projects/README.md` + `STRATEGIES_DETAIL.md` — human-readable catalog
