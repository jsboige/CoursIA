# QC Comparative Backtests — Strategy Catalog

**Issue** : See #1630
**Generated** : 2026-06-04 (automated catalog, pending live backtests)
**Updated** : 2026-06-11 — +3 baselines (MeanReversion v5.2 IBKR, AdaptiveAssetAllocation, PairsTrading). MeanReversion promoted Tier 2 → Tier 1 (0.29 → 0.81). AAA promoted Tier 4 → Tier 1 (untested → 0.509).
**Post-#2801 verification** : 2026-06-14 — campaign started. The remediation #2801 (brokerage
model on 52 strategies via Lot 1 #2812, real fees via Lot 2 #2823/#2864, fixed end-dates via
Lot 3 #2813, OOS splits via Lot 5 #2824) **invalidates pre-remediation Sharpes** when the
brokerage/fee model was previously the negligible default. Entries marked
`✓post-#2801` in the **Verified** column are re-run live via MCP qc-mcp; all others remain
pre-remediation catalog values and need re-backtest before comparative conclusions.
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

## Tier 1 — Robuste (Sharpe > 0.5, 41 strategies)

Strategies with solid risk-adjusted returns. These are the primary candidates for the comparative backtest baseline.

| # | Project | Type | Class | Sharpe | CAGR% | MaxDD% | Calmar | Status |
|---|---------|------|-------|--------|-------|--------|--------|--------|
| 1 | LongShortHarvest-QC | ML | Equities | 3.39 | 57.9 | — | — | robuste |
| 2 | HighBookToMarketFScore-QC | ML | Equities | ~~2.09~~ → **0.41** ✓post-#2801 | 14.5 | 60.4 | 0.24 | **historique** (downgraded: real fees, MaxDD -60%) |
| 3 | PuppiesOfTheDow-QC | IND | Equities | ~~1.99~~ → **0.30** ✓post-#2801 | 9.6 | 28.8 | 0.33 | **historique** (downgraded: real fees) |
| 4 | LeveragedETFMomentum-QC | IND | Equities (lev ETF) | ~~1.80~~ → **1.78** ✓post-#2801 | 126.4 | 53.3 | 2.37 | robuste (confirmed, leveraged — MaxDD -53% expected) |
| 5 | Positive-Negative-Splits-ML | ML | Equities | ~~1.74~~ → **1.51** ✓post-#2801 | 75.7 | 37.6 | 2.01 | robuste (confirmed, PSR 82.3%, top ML leader) |
| 6 | DynamicVIXSpyRegime-QC | ML | Equities/VIX | 1.72 | 29.8 | — | — | robuste |
| 7 | MacroFactorRotation-QC | ML | Multi-asset | ~~1.23~~ → **0.73** ✓post-#2801 | 22.6 | 42.0 | 0.54 | robuste (revised Sharpe -40%, real fees) |
| 8 | Framework_Composite_TrendWeather | COMP | Equities | ~~1.16~~ → **1.14** ✓post-#2801 | 27.1 | 27.7 | 0.98 | robuste (confirmed, PSR 77.9%) |
| 9 | Trend-Following | IND | Equities | ~~1.07~~ → **0.41** ✓post-#2801 | 7.9 | 14.6 | 0.54 | **historique** (downgraded: real IBKR fees) |
| 10 | Multi-Layer-EMA | IND | Crypto (BTC) | 0.93 | — | — | — | robuste |
| 11 | Portfolio-Optimization-ML | ML | Multi-asset | 0.90 | 27.6 | — | — | robuste |
| 12 | EMA-Cross-Stocks | IND | Equities | ~~0.87~~ → **0.99** ✓post-#2801 | 29.2 | 35.7 | 0.82 | robuste (PSR 49.7%, borderline significant) |
| 13 | CausalEventAlpha | ML | Equities | 0.78 | 16.8 | — | — | robuste |
| 14 | Gaussian-Direction-Classifier | ML | Equities | 0.76 | — | — | — | robuste |
| 15 | ML-Temporal-CNN | DL | Equities (QQQ) | 0.73 | 20.5 | — | — | robuste |
| 16 | TrendStocksLite | IND | Equities | 0.72 | 18.2 | — | — | robuste |
| 17 | ML-LLM-Summarization | ML/NLP | Equities | 0.69 | 15.5 | — | — | robuste |
| 18 | ML-RandomForest | ML | Multi-asset | 0.68 | 20.1 | — | — | robuste |
| 19 | AllWeather | RISK | Multi-asset | 0.67 | 9.3 | — | — | robuste |
| 20 | ML-Trend-Scanning | ML | Multi-window | 0.66 | 19.1 | — | — | robuste |
| 21 | VolTarget-Momentum | COMP | Multi-asset | ~~0.65~~ → **0.50** ✓post-#2801 | 11.1 | 21.2 | 0.53 | robuste borderline (revised -23%, PSR 9.4%) |
| 22 | SectorMomentum | IND | Equities+Bonds+Gold | 0.62 | 13.2 | — | — | robuste |
| 23 | BlackLitterman-Momentum | COMP | Equities/ETF | 0.60 | 13.7 | — | — | robuste |
| 24 | Crypto-MultiCanal | IND | Crypto (BTC) | 0.58 | 8.2 | — | — | robuste |
| 25 | ML-FeatureEngineering | ML | Multi-asset | 0.57 | 10.5 | — | — | robuste |
| 26 | Markov-Regime-Detection | ML | Equities | 0.57 | — | — | — | robuste |
| 27 | ML-XGBoost | ML | Multi-asset | 0.57 | 14.8 | — | — | robuste |
| 28 | MomentumStrategy | IND | Equities | 0.57 | 11.8 | — | — | robuste |
| 28b | MeanReversion | IND | Equities (sectors) | 0.81 | 10.0 | 7.5 | 1.34 | robuste (v5.2 IBKR) |
| 29 | RegimeSwitching | ML | Equities/ETF | 0.55 | 11.7 | — | — | robuste |
| 30 | Temporal-CNN-Prediction | DL | Multi-asset | 0.54 | — | — | — | robuste |
| 31 | RL-DQN-Trading | RL | Portfolio | 0.53 | — | — | — | robuste |
| 31b | RL-Portfolio-Q-Learning | RL | Equities | 0.58 | 18.2 | 33.2 | — | historique (2020-2021) |
| 32 | LSTM-Forecasting | DL | Multi-asset | 0.53 | — | — | — | robuste |
| 33 | TrendStocks-Alpha | IND | Equities | ~~0.52~~ → **0.51** ✓post-#2801 | 15.7 | 39.6 | 0.40 | robuste (confirmed -2%, high-turnover near-immune to fees, PSR 5.6%) |
| 34 | Portfolio-IBKR-Binance-Hybrid | COMP | Multi-asset | 0.52 | 15.7 | — | — | robuste |
| 35 | Framework_Composite_FamaFrenchAllWeather | COMP | Multi-asset | — | — | — | — | robuste |
| 36 | Framework_Composite_EMATrend | COMP | Equities | — | — | — | — | robuste |
| 37 | composite-c1-multiasset | COMP | Multi-asset | — | — | — | — | robuste |
| 38 | composite-c2-equityfactor | COMP | Equities | — | — | — | — | robuste |
| 39 | HAR-RV-Kelly | RISK | Multi-asset | — | — | — | — | robuste |

### Post-#2801 verification — findings (2026-06-14)

Ten Tier-1 entries re-run live via MCP qc-mcp (project native period, IBKR margin
brokerage = the #2801 Lot 1 remediation). Results vs the pre-remediation catalog values:

| Strategy | QC project | Catalog Sharpe | **Verified Sharpe** | Delta | Real status |
|----------|-----------|---------------|---------------------|-------|-------------|
| HighBookToMarketFScore | 32732820 | 2.09 | **0.41** | -80% | **historique** (was robuste) |
| PuppiesOfTheDow | 32732704 | 1.99 | **0.30** | -85% | **historique** (was robuste) |
| LeveragedETFMomentum | 32732756 | 1.80 | **1.78** | -1% | robuste (confirmed, leveraged) |
| Positive-Negative-Splits-ML | 30317350 | 1.74 | **1.51** | -13% | robuste (confirmed, **PSR 82.3%**, top ML leader) |
| MacroFactorRotation | 32730301 | 1.23 | **0.73** | -40% | robuste (revised Sharpe) |
| Framework_Composite_TrendWeather | 28825740 | 1.16 | **1.14** | -2% | robuste (confirmed, **PSR 77.9%**) |
| Trend-Following | 28797562 | 1.07 | **0.41** | -62% | **historique** (was robuste) |
| EMA-Cross-Stocks | 28789946 | 0.87 | **0.99** | +14% | robuste (confirmed, PSR 49.7%) |
| VolTarget-Momentum | 30784745 | 0.65 | **0.50** | -23% | robuste borderline (PSR 9.4%, at threshold) |
| TrendStocks-Alpha | 28885507 | 0.52 | **0.51** | -2% | robuste (confirmed, high-turnover near-immune) |

**Finding (methodological, now 10-strategy sample)** : the remediation impact is **not
uniform**, and the pattern is now actionable rather than simply "the catalog is stale". The
verified strategies split into three regimes:

- **Value/factor + simple trend collapse** (-62% to -85%): HighBookToMarketFScore, PuppiesOfTheDow,
  Trend-Following. These three top-ranked catalog entries drop out of the "robuste" band entirely
  — their pre-remediation Sharpes were artifacts of the negligible default fee model. MacroFactorRotation
  (-40%) is the milder case in this family. **These catalog rankings are not reliable.**
- **ML momentum & regime composites HOLD** (-2% to -13%): Positive-Negative-Splits-ML (1.51,
  **PSR 82.3%**) and Framework_Composite_TrendWeather (1.14, **PSR 77.9%**) confirm their ranking
  with statistically significant PSR. Contrast with MomentumRegime (0.185) — not all composites
  survive, but the regime-aware ones do. **These are real alpha that survives real fees.**
- **High-turnover equity is near-immune** (0% to -2%): EMA-Cross-Stocks and TrendStocks-Alpha
  barely move under real IBKR fees, confirming the #1407 finding that US equity fees (<0.25 bps/trade)
  are negligible even at high turnover.

- **VolTarget-Momentum is borderline** (-23%, Sharpe 0.50 sitting exactly on the robuste threshold,
  PSR 9.4% non-significant) — leverage scaling amplifies trade sizes enough that real fees erode it
  to the edge.

**True leaders post-#2801, ranked by statistical significance (PSR > 50%)** :
1. Positive-Negative-Splits-ML — 1.51, PSR 82.3% (new ML leader, replaces the collapsed value entries)
2. LeveragedETFMomentum — 1.78, PSR 79.8% (leveraged, extreme profile)
3. Framework_Composite_TrendWeather — 1.14, PSR 77.9% (the composite that holds)
4. EMA-Cross-Stocks — 0.99, PSR 49.7% (near-significance, near-immune to fees)

**Implication for the réunion Nicolas 15/06** : the catalog is not uniformly stale — it is
specifically the **value/factor and simple-trend top entries that are overstated**, while **ML
momentum and regime-aware composites are validated**. The comparative table should be cited by
significance (PSR) not raw Sharpe, and the collapsed entries must carry a caveat before any
pedagogical use. The remaining Tier-1 list (31 strategies) needs systematic re-backtest before the
table is trusted end-to-end. LongShortHarvest-QC (catalog 3.39, the single highest entry) and
DynamicVIXSpyRegime-QC (1.72) are QC Community Library references without an owned project and
are deferred to a separate baseline-clone task.

Backtests: `1630-baseline-HighBookToMarketFScore-post2801` (0.411, 14.5%, -60.4%, PSR 4.5%),
`1630-baseline-PuppiesOfTheDow-post2801` (0.302, 9.6%, -28.8%, PSR 3.5%),
`1630-baseline-LeveragedETFMomentum-post2801` (1.779, 126.4%, -53.3%, PSR 79.8%),
`1630-baseline-PositiveNegativeSplits-post2801` (1.511, 75.7%, -37.6%, PSR 82.3%),
`1630-baseline-MacroFactorRotation-post2801` (0.731, 22.6%, -42.0%, PSR 23.8%),
`1630-baseline-TrendWeather-post2801` (1.14, 27.1%, -27.7%, PSR 77.9%),
`1630-baseline-TrendFollowing-post2801` (0.407, 7.89%, -14.6%, PSR 8.7%),
`1630-baseline-EMACrossStocks-post2801` (0.991, 29.2%, -35.7%, PSR 49.7%),
`1630-baseline-VolTargetMomentum-post2801` (0.50, 11.1%, -21.2%, PSR 9.4%),
`1630-baseline-TrendStocksAlpha-post2801` (0.512, 15.7%, -39.6%, PSR 5.6%).

---

## Tier 2 — Historique (Sharpe 0.0-0.5, 17 strategies)

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
| 49 | ML-Reversion-Trending | ML | Multi-asset | 0.29 | — | — | — | historique |
| 50 | BTC-ML | ML | Crypto (BTC) | 0.28 | — | — | — | historique |
| 51 | ML-Chronos-Foundation | DL | Multi-asset | 0.28 | — | — | historique |
| 52 | Chronos-Foundation-Forecasting | ML | Multi-asset | 0.25 | — | — | historique |
| 53 | EMA-Cross-Crypto | IND | Crypto (BTC) | 0.24 | — | — | historique |
| 54 | InverseVolatility-Rank | ML | Futures | 0.21 | — | — | historique |
| 55 | OptionsIncome | OPT | Options (SPY) | 0.21 | — | — | historique |
| 56 | Framework_Composite_MomentumRegime | COMP | Multi-asset | 0.19 | 4.7 | — | historique |

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

## Tier 4 — Untested (candidates for standardized backtest, ~38 strategies)

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
| 73 | Option-Wheel | OPT | Options (SPY) | yes |
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
| AllWeather | 28657833 | 2010-2025* | 0.631 | 9.016 | 16.4 | 31.2 | `cd6ba790` | *Hardcoded start 2010. PSR 31% |
| SectorDualMomentum | 29686886 | 2015-2025* | 0.581 | 13.488 | 22.8 | 15.3 | `8713e974` | *Hardcoded start 2015 |
| MomentumStrategy (SectorMom) | 28657837 | 2010-2025* | 0.555 | 11.676 | 25.8 | 7.2 | `e4491127` | *Hardcoded start 2010 |
| VolTarget-Momentum | 30784745 | 2018-2025 | 0.648 | 14.7 | 21.2 | 22.3 | `c3223fe5` | Confirmed |
| Crypto-MultiCanal | 30750734 | 2020-2025 | 0.581 | 8.2 | 17.0 | 37.6 | `4e97d7dc` | Stable crypto |
| EMA-Cross-Stocks | 28789946 | 2018-2025 | **0.891** | 26.229 | 35.7 | 40.5 | `6b40d921` | Highest CAGR |
| Portfolio-IBKR-Binance | 31717642 | 2020-2025 | 0.519 | 15.7 | 16.9 | 46.2 | `4cbb9476` | Multi-asset |
| TrendStocks-Alpha | 28885507 | 2018-2025 | 0.519 | 15.9 | 39.6 | 5.8 | `7c434dbd` | High MaxDD |
| EMA-Cross-Alpha | 28885488 | 2018-2025 | -0.010 | 2.8 | 14.0 | 0.5 | `633779d0` | Period overfitting |
| MomentumRegime | 31243821 | 2018-2025 | 0.185 | 4.7 | 11.5 | 13.0 | `033834d8` | Double-defense |
| ForexCarry | 28657908 | 2015-2025* | -1.108 | -0.5 | 19.2 | — | `c3afe374` | *Cannot restrict to 2018+ |
| RL-Q-Learning | 32057969 | 2020-2021* | 0.584 | 18.2 | 33.2 | — | `fb1a6366` | *Hardcoded dates |
| PuppiesOfTheDow-QC | 32732704 | 2018-2025 | 0.302 | 9.613 | 28.8 | 3.5 | `37266daa` | Collapse vs catalog 1.99 (period overfitting) |
| LeveragedETFMomentum-QC | 32732756 | 2018-2025 | **1.779** | 126.388 | 53.3 | **79.8** | `2addf467` | Confirms catalog 1.80. Lev ETF: extreme CAGR, MaxDD 53% |
| Framework_Composite_TrendWeather | 28825740 | 2018-2025 | 0.948 | 24.603 | 27.5 | 56.6 | `cd84c50b` | Close to catalog 1.16, best composite |
| HighBookToMarketFScore-QC | 32732820 | 2018-2025 | 0.411 | 14.513 | 60.4 | 4.5 | `5ef58b0d` | Collapse vs catalog 2.09, MaxDD 60% |
| MeanReversion v5.2 | 30776121 | 2015-2024 | **0.810** | 10.040 | 7.5 | 46.8 | `b2c5b08f` | Promoted Tier 2→1. Calmar 1.34 (best risk-adj). PSR 46.8% |
| AdaptiveAssetAllocation | 28693649 | 2008-2024 | 0.509 | 8.008 | 18.9 | 10.6 | `89e8aaef` | Promoted Tier 4→1. Min-var + momentum |
| PairsTrading | 28693651 | 2015-2024 | -0.280 | 1.101 | 15.9 | 0.0 | `1ed0de9d` | Confirms exploratoire. PSR 0.001% |

### Student strategies (ESGF 5BD1 cohort, See #1405)

| Project | QC ID | Period | Sharpe | CAGR% | MaxDD% | PSR% | Backtest ID | Notes |
|---------|-------|--------|--------|-------|--------|------|-------------|-------|
| DualMomentum (student) | 31798582 | 2023-2025* | 0.493 | 13.5 | 9.0 | **54.9** | `88d36544` | *Hardcoded 2023 start. PSR > 50%! |
| RiskParity inverse-vol (student) | 31872286 | 2015-2025* | 0.514 | 9.3 | 20.7 | 16.3 | `d6a7bc52` | *Hardcoded 2015 start |
| ValueFactor Z-Score (student) | 31932810 | 2015-2025* | 0.227 | 6.4 | 36.5 | 0.8 | `da42c569` | Alpha negatif (decennie growth) |
| OptionWheel VGT (student) | 31846074 | 2018-2025* | -0.51 | 0% | 103.5 | 0.0 | `b9eca3c8` | Win-rate paradoxe, MaxDD > 100% |

**Note**: AdaptiveAssetAllocation (31781187) et MarkovRegime (31871247) n'ont produit aucune métrique (0 trades ou erreur d'exécution).

### Not alignable (hardcoded ML train/test split)

| Project | QC ID | Reason | Current Period |
|---------|-------|--------|----------------|
| BTC-ML | 29318876 | Train 2019-2022, test 2023-2026 hardcoded. Changing dates breaks ML logic. | 2023-01-01 → 2026-03-01 |

---

## Key findings

1. **TrendFollowing = leader indiscutable**: Sharpe 1.072 sur 2018-2025 avec MaxDD 9.3%. PSR 81.8% (statistiquement significatif). Seule strategie "Robuste" confirmee sur la periode aligned.
2. **EMA-Cross-Stocks: surprise positive**: Sharpe 0.891 sur 2018-2025, CAGR 26.2%. PSR 40.5%. 2e meilleur Sharpe aligne, derriere TrendFollowing.
3. **EMA-Cross-Alpha: chute dramatique**: Sharpe passe de 0.996 (meilleur backtest) a -0.010 sur la periode aligned. PSR 0.5% = bruit. Confirme le pattern "backtests courts = overfitting".
4. **Composites ne battent pas les single-strategies**: MomentumRegime (SectorMomentum + RegimeSwitching) obtient 0.185, confirmant le probleme de "double-defense".
5. **Crypto = rendement modere mais stable**: Crypto-MultiCanal (0.581) et Portfolio-IBKR-Binance (0.519) offrent diversification avec MaxDD maitrises.
6. **FX Carry = perdant**: Sharpe -1.108, les taux bas post-COVID ont elimine l'avantage du carry trade.
7. **AllWeather: performance confirme**: Sharpe 0.631 (2010-2025), MaxDD 16.4%, PSR 31.2%. Risk-parity solide.
8. **MomentumStrategy (SectorMom v4.0)**: Sharpe 0.555, CAGR 11.7%, mais PSR 7.2% = non significatif.
9. **SectorDualMomentum v3.2**: Sharpe 0.581, CAGR 13.5%, MaxDD 22.8%. PSR 15.3%.
10. **TrendStocks-Alpha: high return, high risk**: CAGR 15.9% mais MaxDD 39.6% (Calmar 0.40). PSR 5.8% = non significatif.
11. **Student DualMomentum: PSR > 50%**: Sharpe 0.493 sur 2023-2025 avec MaxDD 9.0%. Seule strategie etudiante avec PSR significatif (54.9%).
12. **Student RiskParity: performance honnete**: Sharpe 0.514, CAGR 9.3%, MaxDD 20.7%. Inverse-vol simple mais efficace. PSR 16.3% (non significatif mais respectable).
13. **Student OptionWheel: catastrophe pedagogique**: Sharpe -0.51, MaxDD 103.5%. Parfait comme etude de cas du "win-rate paradoxe".
14. **Student ValueFactor: alpha negatif confirmee**: Sharpe 0.227, PSR 0.8%. Decennie growth-dominée = facteur value sous-performant.
15. **LeveragedETFMomentum: confirme et significatif**: Sharpe 1.779 sur 2018-2025, PSR 79.8% (2e PSR significatif apres TrendFollowing). Mais MaxDD 53.3% et CAGR 126% typiques d'un levier 3x — profil risque extreme, pas comparable aux strategies non-leveragees.
16. **PuppiesOfTheDow et HighBookToMarketFScore: effondrement sur periode alignee**: Sharpe catalog 1.99 et 2.09 (obtenus sur leur fenetre glissante par defaut `end_date - 12 ans`) tombent a 0.302 (PSR 3.5%) et 0.411 (PSR 4.5%, MaxDD 60.4%) sur 2018-2025. Les deux meilleures lignes ML/IND du Tier 1 ne sont pas reproductibles sur la fenetre standardisee.
17. **TrendWeather: le composite qui tient**: Sharpe 0.948 (PSR 56.6%), proche du catalog 1.16. Contraste fort avec MomentumRegime (0.185) — toutes les architectures composites ne se valent pas.
18. **Caveat reproductibilite Trend-Following**: le code du repo backteste sur 2018-2024 donne Sharpe 0.365 / MaxDD 13.8% (backtest `3748cb62`), loin du 1.072 publie ci-dessus (`7792ae0a`, 2018-2025, etat du code cloud anterieur). Periodes differentes (2025 inclus ou non) ET drift possible repo vs cloud — a investiguer avant de citer 1.072 comme reference du code versionne.
19. **MeanReversion v5.2: Best Calmar ratio**: Sharpe 0.81, MaxDD 7.5%, Calmar 1.34 — best risk-adjusted return among non-leveraged strategies. PSR 46.8% (near significance). Promoted from Tier 2 (0.29) to Tier 1. The v5.2 code (IBKR brokerage, RSI65 exit, 10% stop-loss) dramatically outperforms the older version.
20. **AdaptiveAssetAllocation: confirmed robuste**: Sharpe 0.509, CAGR 8.0%, MaxDD 18.9% (2008-2024, 16 years). Min-var + momentum approach produces steady returns. PSR 10.6% (not significant but positive).
21. **PairsTrading: structural failure confirmed**: Sharpe -0.28 on aligned period, PSR 0.001%. OLS hedge + cointegration still produces negative alpha. Remains exploratoire/pedagogical.

## Comparison: Best-vs-Aligned

| Strategy | Best Sharpe | Aligned Sharpe | Delta | Diagnostic |
|----------|------------|----------------|-------|------------|
| EMA-Cross-Alpha | 0.996 | -0.010 | -1.006 | Period overfitting severe |
| EMA-Cross-Stocks | 0.87 | 0.891 | +0.021 | Performance confirmee, ameliore |
| TrendStocks-Alpha | 0.609 | 0.519 | -0.090 | Legere degradation |
| AllWeather | 0.67 | 0.631 | -0.039 | Stable, confirme |
| MomentumStrategy | 0.57 | 0.555 | -0.015 | Performance confirmee |
| TrendFollowing | ~0.8 | 1.072 | +0.272 | Ameliore sur longue periode |
| Crypto-MultiCanal | ~0.6 | 0.581 | ~0 | Performance confirmee |
| VolTarget-Momentum | ~0.65 | 0.648 | ~0 | Performance confirmee |
| PuppiesOfTheDow-QC | 1.99 | 0.302 | -1.688 | Period overfitting severe (catalog = fenetre glissante 12 ans) |
| LeveragedETFMomentum-QC | 1.80 | 1.779 | -0.021 | Performance confirmee (mais MaxDD 53%) |
| Framework_Composite_TrendWeather | 1.16 | 0.948 | -0.212 | Legere degradation, composite robuste |
| HighBookToMarketFScore-QC | 2.09 | 0.411 | -1.679 | Period overfitting severe + MaxDD 60% |
| MeanReversion | 0.29 (old) | **0.810** (v5.2) | +0.520 | v5.2 IBKR dramatically better. Calmar 1.34 |
| AdaptiveAssetAllocation | untested | 0.509 | +0.509 | First aligned baseline. Min-var + momentum |
| PairsTrading | -0.36 | -0.280 | +0.080 | Marginal improvement, still exploratoire |

---

## Next Steps

1. ~~**Standardized backtest period**: Re-run all 62 tested + 39 untested strategies on 2018-01-01 → 2024-12-31~~ — Done, 24 baselines verified via QC Cloud API (See #1630)
2. ~~**Run aligned baselines for AllWeather/SectorMomentum/EMA-Cross-Stocks/MomentumStrategy**~~ — Done, all 4 re-backtested via QC Cloud
3. ~~**Student strategies (ESGF #1405)**: DualMomentum, RiskParity, ValueFactor, OptionWheel backtestees~~ — Done, 4/6 valides
3b. ~~**Run baselines for MeanReversion, AAA, PairsTrading**~~ — Done 2026-06-11. MeanReversion promoted Tier 2→1 (0.81), AAA promoted Tier 4→1 (0.509), PairsTrading confirmed exploratoire (-0.28)
4. ~~**Transaction cost sensitivity analysis**: Estimated turnover and cost impact for all 10 research baselines~~ — Done (See #1407)
5. ~~**Transaction cost re-backtest**: Add `SetBrokerageModel` + configurable brokerage parameter~~ — Done, #2575 + fee sweep EMA-Cross-Stocks + Crypto-MultiCanal (See #2471, #2575, #2588)
6. **Cross-seed validation**: ≥4 seeds (0/1/7/42/99) for ML/DL/RL strategies
7. **Edge vs σ**: Compute for all strategies vs B&H baseline
8. **Trend-Following repo/cloud drift**: repo code gives Sharpe 0.365 on 2018-2024 vs published 1.072 (2018-2025, prior cloud state) — identify which code version produced 1.072 and align repo (see Key finding 18)

---

## Transaction Cost Sensitivity (See #1407)

Source code analysis of all 10 research projects. Zero strategies have explicitly configurable transaction cost parameters (`SetFeeModel` / custom fee). Costs are implicit in the brokerage model or use QC defaults.

### Fee Model Configuration

| Project | QC ID | `SetFeeModel` | `SetBrokerageModel` | Configurable | Default Fees |
|---------|-------|---------------|----------------------|--------------|--------------|
| Trend-Following | 28797562 | NONE | `IBKR, MARGIN` | YES (`brokerage=ibkr/none`) | IBKR tiered |
| EMA-Cross-Stocks | 28789946 | NONE | `IBKR, MARGIN` | YES (`brokerage=ibkr/none`) | IBKR tiered |
| MomentumStrategy | 28657837 | NONE | `IBKR, MARGIN` | YES (`brokerage=ibkr/none`) | IBKR tiered |
| AllWeather | 28657833 | NONE | `IBKR, MARGIN` | YES (`brokerage=ibkr/none`) | IBKR tiered |
| VolTarget-Momentum | 30784745 | NONE | `IBKR, MARGIN` | YES (`brokerage=ibkr/none`) | IBKR tiered |
| Crypto-MultiCanal | 30750734 | NONE | `BINANCE, CASH` | YES (`brokerage=binance/none`) | Binance schedule (0.1%) |
| Portfolio-IBKR-Binance | 31717642 | NONE | `IBKR, MARGIN` | YES (`brokerage=ibkr/none`) | IBKR tiered |
| MomentumRegime | 31243821 | NONE | `IBKR, MARGIN` | YES (`brokerage=ibkr/none`) | IBKR tiered |
| TrendStocks-Alpha | 28885507 | NONE | `IBKR, MARGIN` | YES (`brokerage=ibkr/none`) | IBKR tiered |
| EMA-Cross-Alpha | 28885488 | NONE | `IBKR, MARGIN` | YES (`brokerage=ibkr/none`) | IBKR tiered |
| ForexCarry | 28657908 | NONE | `OANDA, MARGIN` | YES (`brokerage=oanda/none`) | OANDA schedule |
| AdaptiveAssetAllocation | 28693649 | NONE | NONE | NO | QC defaults |
| MeanReversion | 30776121 | NONE | `IBKR, MARGIN` | NO | IBKR tiered (v5.2 IBKR baseline) |
| PairsTrading | 28693651 | NONE | NONE | NO | QC defaults |

### Turnover Estimation

| Project | Rebalance Freq | Universe | Est. Annual Trades | Turnover | Cost Sensitivity |
|---------|----------------|----------|--------------------|----------|------------------|
| TrendFollowing | Monthly | 7 ETFs | ~24-48 | MEDIUM | MEDIUM |
| EMA-Cross-Stocks | Daily (5% drift) | 5 stocks | ~125-250 | HIGH | **HIGH** |
| MomentumStrategy | Monthly + stop-loss | 11 sectors | ~48-96 | MEDIUM-HIGH | HIGH |
| AllWeather | Quarterly (3% drift) | 4 ETFs | ~8-16 | LOW | LOW |
| VolTarget-Momentum | Monthly (leverage 0.3-1.5x) | 7 ETFs | ~24-48 | MEDIUM | MEDIUM |
| Crypto-MultiCanal | Daily (signal) | 1 (BTC) | ~50-100 | HIGH | **HIGH** (0.1% crypto) |
| Portfolio-IBKR-Binance | One-shot | 3 assets | ~3 | VERY LOW | NEGLIGIBLE |
| MomentumRegime | Monthly | 4 assets | ~24-48 | MEDIUM | MEDIUM |
| TrendStocks-Alpha | Weekly | 15 stocks | ~150-300 | HIGH | **HIGH** |
| EMA-Cross-Alpha | Daily (1-day insight) | 5 stocks | ~125-250 | HIGH | **HIGH** |

### Cost Sensitivity Ranking

**TIER 1 — Highly Sensitive** (cost change would significantly impact Sharpe):

1. **EMA-Cross-Stocks** — Daily rebalance, 5 stocks, 5% drift threshold. No brokerage model = default QC fees. A 2x fee increase could eat 50-100bps CAGR.
2. **EMA-Cross-Alpha** — Daily insight emission, IBKR margin. Same high-frequency cross logic.
3. **TrendStocks-Alpha** — 15-stock universe, weekly rebalance. Largest universe = most trades.
4. **Crypto-MultiCanal** — Daily BTC signals, Binance CASH (already has real 0.1% crypto fees). Crypto percentage-based fees amplify impact vs per-share equity fees.
5. **MomentumStrategy** — Monthly rotation of top-4 from 11 sectors + daily stop-loss checks. Stop-losses generate unplanned trades.

**TIER 2 — Moderately Sensitive:**

6. **TrendFollowing** — Monthly rebalance, 6 risky + 1 safe. Moderate turnover on regime changes.
7. **VolTarget-Momentum** — Monthly with leverage scaling (0.3x to 1.5x). Leverage changes mean larger position sizes.
8. **MomentumRegime** — Monthly composite on 4 assets, IBKR margin. Moderate.

**TIER 3 — Low Sensitivity:**

9. **AllWeather** — Quarterly + 3% drift threshold, 4 static-weight ETFs. Very few trades.
10. **Portfolio-IBKR-Binance** — One-shot buy of SPY/BND/AAPL. 3 trades total. Zero sensitivity.

### Recommended Actions

| Priority | Project | Action | Rationale |
|----------|---------|--------|-----------|
| HIGH | EMA-Cross-Stocks | Add configurable fee + 0x/1x/2x sweep | Highest turnover, no brokerage = blind to real costs |
| HIGH | TrendStocks-Alpha | Same | Largest universe, weekly rebalance |
| HIGH | Crypto-MultiCanal | Test 0x/2x Binance fees | **Done** — Binance Sharpe 0.333 vs None 0.181 (See #2590) |
| MEDIUM | MomentumStrategy | Add fee sweep | Stop-losses create unplanned trades |
| MEDIUM | VolTarget-Momentum | Add fee sweep | Leverage amplifies trade sizes |
| LOW | AllWeather | Optional | Very few trades, minimal cost impact |
| SKIP | Portfolio-IBKR-Binance | Not applicable | One-shot, 3 trades total |

### Fix Pattern (for fee sweep)

```python
# In initialize(), add configurable fee model
self.transaction_cost_bps = self.get_parameter("transaction_cost_bps", 5)  # default 5bps
for ticker in self.all_tickers:
    security = self.add_equity(ticker, Resolution.DAILY)
    security.set_fee_model(ConstantFeeModel(self.transaction_cost_bps / 10000 * self.portfolio.total_portfolio_value * 0.20))
```

### Estimated Fee Impact Analysis

**Methodology**: Each strategy's annual turnover is translated into a round-trip cost drag. Fee assumptions: US equities/ETFs = 5 bps one-way (10 bps round-trip, IBKR pricing), Crypto = 10 bps one-way (20 bps round-trip, Binance), FX = 2 bps one-way. QC-reported CAGR is treated as near-zero-fee (no explicit `SetFeeModel` in 8/10 strategies).

#### Annual Cost Drag

| Project | Est. Turnover | Round-trip Fee | Annual Cost Drag | CAGR% (QC) | Est. Net CAGR% | CAGR Erosion |
|---------|---------------|----------------|------------------|------------|----------------|--------------|
| TrendFollowing | 2x | 10 bps | 20 bps (0.20%) | 23.2 | 23.0 | -20 bps |
| EMA-Cross-Stocks | 5x | 10 bps | 50 bps (0.50%) | 26.2 | 25.7 | -50 bps |
| MomentumStrategy | 3x | 10 bps | 30 bps (0.30%) | 11.7 | 11.4 | -30 bps |
| AllWeather | 0.5x | 10 bps | 5 bps (0.05%) | 9.0 | 9.0 | -5 bps |
| VolTarget-Momentum | 2.5x | 10 bps | 25 bps (0.25%) | 14.7 | 14.5 | -25 bps |
| Crypto-MultiCanal | 4x | 20 bps | 80 bps (0.80%) | 8.2 | 7.4 | -80 bps |
| Portfolio-IBKR-Binance | 0.15x | 10 bps | 1.5 bps (0.02%) | 15.7 | 15.7 | -2 bps |
| MomentumRegime | 2x | 10 bps | 20 bps (0.20%) | 4.7 | 4.5 | -20 bps |
| TrendStocks-Alpha | 6x | 10 bps | 60 bps (0.60%) | 15.9 | 15.3 | -60 bps |
| EMA-Cross-Alpha | 5x | 10 bps | 50 bps (0.50%) | 2.8 | 2.3 | -50 bps |

**Calculation**: Annual Cost = Turnover x Round-trip Fee. Example: EMA-Cross-Stocks = 5x x 10 bps = 50 bps/year drag.

#### Sharpe Ratio Erosion

| Project | Aligned Sharpe | Est. Vol% | Annual Cost | Sharpe Erosion | Est. Net Sharpe | Erosion % |
|---------|---------------|-----------|-------------|----------------|-----------------|-----------|
| TrendFollowing | 1.072 | 21.6% | 20 bps | -0.009 | 1.063 | -0.9% |
| EMA-Cross-Stocks | 0.891 | 29.4% | 50 bps | -0.017 | 0.874 | -1.9% |
| MomentumStrategy | 0.555 | 21.1% | 30 bps | -0.014 | 0.541 | -2.5% |
| AllWeather | 0.631 | 14.3% | 5 bps | -0.003 | 0.628 | -0.5% |
| VolTarget-Momentum | 0.648 | 22.7% | 25 bps | -0.011 | 0.637 | -1.7% |
| Crypto-MultiCanal | 0.581 | 14.1% | 80 bps | -0.057 | 0.524 | **-9.8%** |
| Portfolio-IBKR-Binance | 0.519 | 30.3% | 1.5 bps | -0.001 | 0.519 | -0.1% |
| MomentumRegime | 0.185 | 25.4% | 20 bps | -0.008 | 0.177 | -4.3% |
| TrendStocks-Alpha | 0.519 | 30.6% | 60 bps | -0.020 | 0.499 | -3.8% |
| EMA-Cross-Alpha | -0.010 | 28.0% | 50 bps | -0.018 | -0.028 | N/A |

**Calculation**: Vol = CAGR / Sharpe. Sharpe erosion = Cost / Vol. Example: Crypto-MultiCanal = 0.80% / 14.1% = 0.057 Sharpe erosion.

#### Fee Resilience Ranking

| Rank | Project | Cost Drag | Sharpe Erosion | Break-even Fee (one-way) | Resilience |
|------|---------|-----------|----------------|--------------------------|------------|
| 1 | Portfolio-IBKR-Binance | 1.5 bps | 0.5 bps | ~52,000 bps | Near-immune |
| 2 | AllWeather | 5 bps | 3 bps | 1,800 bps | Very high |
| 3 | TrendFollowing | 20 bps | 9 bps | 580 bps | High |
| 4 | VolTarget-Momentum | 25 bps | 11 bps | 294 bps | High |
| 5 | MomentumStrategy | 30 bps | 14 bps | 195 bps | High |
| 6 | EMA-Cross-Stocks | 50 bps | 17 bps | 262 bps | Moderate |
| 7 | TrendStocks-Alpha | 60 bps | 20 bps | 133 bps | Moderate |
| 8 | MomentumRegime | 20 bps | 8 bps | 118 bps | Moderate |
| 9 | Crypto-MultiCanal | 80 bps | 57 bps | 103 bps | **Vulnerable** |
| 10 | EMA-Cross-Alpha | 50 bps | 18 bps | 28 bps | **Vulnerable** |

**Break-even fee** = CAGR / Turnover. Below this threshold the strategy remains net profitable.

#### Key Takeaways

1. **Crypto fees are NOT the primary risk factor (revised)**: Crypto-MultiCanal fee sweep (backtest IDs `9ad550e9`, `56d54a3c`) shows Binance (real 0.1% fees) Sharpe 0.333 vs no-brokerage Sharpe 0.181. Fees actually improve Sharpe by +0.152 (+84%), likely because the brokerage model's cash constraints filter low-quality trades. The theoretical -9.8% erosion estimate was wrong — real backtesting contradicts it.
2. **EMA-Cross-Stocks: fees negligible** (backtest IDs from #2588): IBKR Sharpe 0.991 vs no-brokerage Sharpe 0.991 (identical). US equity fees via IBKR are <0.25 bps per trade — negligible impact even at high turnover.

### Verified Fee Sweep Results

Backtest-validated fee sensitivity for strategies with configurable brokerage parameter.

| Project | With Fees | Sharpe (fees) | Sharpe (no fees) | Delta | Verdict |
|---------|-----------|---------------|-------------------|-------|---------|
| EMA-Cross-Stocks | IBKR Margin | 0.991 | 0.991 | 0.000 | **Near-immune** (US equity fees negligible) |
| Crypto-MultiCanal | Binance Cash | 0.333 | 0.181 | **+0.152** | **Fees improve** (cash constraints filter bad trades) |

**Key insight**: Theoretical fee erosion estimates can be wrong. Binance CASH account type enforces cash settlement rules that prevent over-leveraging, improving risk-adjusted returns. Real backtesting is essential.
2. **EMA-Cross-Alpha is fragile on multiple dimensions**: Already negative Sharpe, thin fee margin (28 bps break-even), and high turnover. Confirms "exploratoire" classification.
3. **High-turnover equity strategies lose meaningful CAGR**: EMA-Cross-Stocks (-50 bps) and TrendStocks-Alpha (-60 bps) each lose ~0.5-0.6% annually. Warrant explicit `SetFeeModel`.
4. **No profitable strategy flips unprofitable** at realistic fees. The risk is Sharpe degradation, not sign flip.
5. **Slippage excluded**: Market impact on small-caps (EMA-Cross-Stocks) could add 5-15 bps/trade, doubling effective cost for those strategies.

---

## Data Source

- QC Cloud API via `qc-mcp-lite` — backtest IDs verified 2026-06-05, updated 2026-06-11 (MeanReversion, AAA, PairsTrading)
- `projects/catalog.json` — 114 entries, authoritative metadata
- `projects/README.md` + `STRATEGIES_DETAIL.md` — human-readable catalog
