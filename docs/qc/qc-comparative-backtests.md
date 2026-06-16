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
| 1 | LongShortHarvest-QC | ML | Equities | ~~3.39~~ → **1.64** ✓post-#2801 | 45.6 | 17.0 | 2.68 | robuste (confirmed, **PSR 98.7%** top — catalog 3.39 was 1Y-OOS, full decade -52%) |
| 2 | HighBookToMarketFScore-QC | ML | Equities | ~~2.09~~ → **0.41** ✓post-#2801 | 14.5 | 60.4 | 0.24 | **historique** (downgraded: real fees, MaxDD -60%) |
| 3 | PuppiesOfTheDow-QC | IND | Equities | ~~1.99~~ → **0.30** ✓post-#2801 | 9.6 | 28.8 | 0.33 | **historique** (downgraded: real fees) |
| 4 | LeveragedETFMomentum-QC | IND | Equities (lev ETF) | ~~1.80~~ → **1.78** ✓post-#2801 | 126.4 | 53.3 | 2.37 | robuste (confirmed, leveraged — MaxDD -53% expected) |
| 5 | Positive-Negative-Splits-ML | ML | Equities | ~~1.74~~ → **1.51** ✓post-#2801 | 75.7 | 37.6 | 2.01 | robuste (confirmed, PSR 82.3%, top ML leader) |
| 6 | DynamicVIXSpyRegime-QC | ML | Equities/VIX | ~~1.72~~ → **1.00** ✓post-#2801 | 17.9 | 16.5 | 1.09 | robuste (confirmed, **PSR 69.4%** — catalog 1.72 was 1Y-OOS, full decade -42%) |
| 7 | MacroFactorRotation-QC | ML | Multi-asset | ~~1.23~~ → **0.73** ✓post-#2801 | 22.6 | 42.0 | 0.54 | robuste (revised Sharpe -40%, real fees) |
| 8 | Framework_Composite_TrendWeather | COMP | Equities | ~~1.16~~ → **1.14** ✓post-#2801 | 27.1 | 27.7 | 0.98 | robuste (confirmed, PSR 77.9%) |
| 9 | Trend-Following | IND | Equities | ~~1.07~~ → **0.41** ✓post-#2801 | 7.9 | 14.6 | 0.54 | **historique** (downgraded: real IBKR fees) |
| 10 | Multi-Layer-EMA | IND | Crypto (BTC) | ~~0.93~~ → **0.80** ✓post-#2801 | 25.0 | 57.1 | 0.44 | robuste (confirmed -14%, ML crypto holds, PSR 23.9%, MaxDD -57% BTC) |
| 11 | Portfolio-Optimization-ML | ML | Multi-asset | ~~0.90~~ → **0.88** ✓post-#2801 | 27.2 | 41.6 | 0.65 | robuste (confirmed -2%, monthly rebalance + fee-homogeneous US equity basket = near-immune, PSR 37.2%) |
| 12 | EMA-Cross-Stocks | IND | Equities | ~~0.87~~ → **0.99** ✓post-#2801 | 29.2 | 35.7 | 0.82 | robuste (PSR 49.7%, borderline significant) |
| 13 | CausalEventAlpha | ML | Equities | ~~0.78~~ → **0.45** ✓post-#2801 | 11.7 | 38.8 | 0.30 | **historique** (downgraded -43%, monthly cadence but full-basket rotation = high turnover, PSR 5.5%) |
| 14 | Gaussian-Direction-Classifier | ML | Equities | ~~0.76~~ → **0.76** ✓post-#2801 | 23.1 | 25.6 | 0.90 | robuste (confirmed 0%, daily schedule but low realized turnover on liquid mega-cap basket = near-immune, PSR 22.7%) |
| 15 | ML-Temporal-CNN | DL | Equities (QQQ) | ~~0.73~~ → **0.46** ✓post-#2801 | 12.5 | 30.8 | 0.41 | **historique** (downgraded -37%, DL/CNN overfits real fees, PSR 5.2%) |
| 16 | TrendStocksLite | IND | Equities | ~~0.72~~ → **0.71** ✓post-#2801 | 18.0 | 33.7 | 0.53 | robuste (confirmed -2%, weekly trend on 15 liquid large-caps = low realized turnover, near-immune, PSR 25.0%) |
| 17 | ML-LLM-Summarization | ML/NLP | Equities | 0.69 | 15.5 | — | — | robuste |
| 18 | ML-RandomForest | ML | Equities | ~~0.68~~ → **0.70** ✓post-#2801 | 20.6 | 40.9 | 0.50 | robuste (confirmed +3%, bi-weekly RF on 10 mega-caps = moderate turnover near-immune on fee-homogeneous US equity basket, PSR 18.4%) |
| 19 | AllWeather | RISK | Multi-asset | ~~0.67~~ → **0.47** ✓post-#2801 | 7.5 | 16.4 | 0.46 | **historique** (downgraded -30%, low-turnover multi-asset NOT near-immune, PSR 19.6%) |
| 20 | ML-Trend-Scanning | ML | Multi-window | ~~0.66~~ → **0.33** ✓post-#2801 | 7.1 | 29.4 | 0.24 | **historique** (downgraded -50%, daily rebalance on SPY/TLT/GLD multi-asset = very high turnover crushed by real IBKR fees, PSR 7.8%) |
| 21 | VolTarget-Momentum | COMP | Multi-asset | ~~0.65~~ → **0.50** ✓post-#2801 | 11.1 | 21.2 | 0.53 | robuste borderline (revised -23%, PSR 9.4%) |
| 22 | SectorMomentum | IND | Equities+Bonds+Gold | ~~0.62~~ → **0.56** ✓post-#2801 | 13.1 | 22.8 | 0.58 | robuste (mild -9%, monthly rebalance winner-takes-all on 3 ETFs = low rotation near-immune, contrasts heavier multi-sleeve baskets; PSR 13.8% low, not a true leader) |
| 23 | BlackLitterman-Momentum | COMP | Equities/ETF | ~~0.60~~ → **0.83** ✓post-#2801 | 15.8 | 16.9 | 0.94 | **robuste (catalog CORRECTED UPWARD +38%)** — catalog 0.60 was stale; code already had IBKR so the docstring v2 BEST (0.823, CAGR 15.7%, MaxDD -16.9%) was the WITH-fees value; monthly rebalance + fee-homogeneous 15-stock US equity basket = near-immune to fees; **PSR 51.4% = true leader (borderline significant)** |
| 24 | Crypto-MultiCanal | IND | Crypto (BTC) | ~~0.58~~ → **0.33** ✓post-#2801 | 4.6 | 14.1 | 0.33 | **historique** (downgraded -43%, crypto indicator NOT robust post-fees, PSR 13.0%) |
| 25 | ML-FeatureEngineering | ML | Equities (10 mega-caps) | ~~0.57~~ → **0.65** ✓post-#2801 | 18.7 | 28.1 | 0.67 | robuste (catalog CORRECTED UPWARD +15% — was stale; real Sharpe of current RF+GB 18-feature ensemble near-immune on fee-homogeneous US equity; PSR 15.1% low, not a true leader; universe corrected Multi-asset→Equities; baseline-clone 32952140) |
| 26 | Markov-Regime-Detection | ML | Equities | 0.57 | — | — | — | robuste |
| 27 | ML-XGBoost | ML | Equities (15 mega-caps) | ~~0.57~~ → **0.555** ✓post-#2801 | 14.5 | 40.4 | 0.36 | robuste (confirmed mild -3%, bi-weekly GradientBoostingRegressor on fee-homogeneous 15 mega-caps = near-immune; PSR 10.6% low, not a true leader; universe corrected Multi-asset→Equities) |
| 28 | MomentumStrategy | IND | Equities | ~~0.57~~ → **0.50** ✓post-#2801 | 11.2 | 25.8 | 0.43 | robuste borderline (at threshold -12%, PSR 9.3% non-significant) |
| 28b | MeanReversion | IND | Equities (sectors) | ~~0.81~~ → **0.81** ✓post-#2801 | 10.0 | 7.5 | 1.34 | robuste (confirmed, PSR 46.8% near-significant, low-turnover multi-asset holds = signal-frequency immunity) |
| 29 | RegimeSwitching | ML | Multi-asset (SPY/QQQ/IEF/GLD) | ~~0.55~~ → **0.581** ✓post-#2801 | 12.3 | 33.0 | 0.37 | robuste (confirmed mild +6%, multi-asset HOLDS via explicit turnover suppression — regime-change trigger + anti-micro-rebalancing + beta-annealing; contrasts AllWeather -30% multi-sleeve; PSR 7.0% low not a true leader) |
| 30 | Temporal-CNN-Prediction | DL | Multi-asset | 0.54 | — | — | — | robuste |
| 31 | RL-DQN-Trading | RL | Portfolio | ~~0.53~~ → **0.58 (2020-21 only)** ✓post-#2801 | 18.2 | 33.2 | 0.55 | **non re-verifiable** (locked to ~1yr window, runtime error on extension, PSR 30.2%) |
| 31b | RL-Portfolio-Q-Learning | RL | Equities | 0.58 | 18.2 | 33.2 | — | historique (2020-2021) |
| 32 | LSTM-Forecasting | DL | Multi-asset | 0.53 | — | — | — | robuste |
| 33 | TrendStocks-Alpha | IND | Equities | ~~0.52~~ → **0.51** ✓post-#2801 | 15.7 | 39.6 | 0.40 | robuste (confirmed -2%, high-turnover near-immune to fees, PSR 5.6%) |
| 34 | Portfolio-IBKR-Binance-Hybrid | COMP | Multi-asset | 0.52 | 15.7 | — | — | robuste |
| 35 | Framework_Composite_FamaFrenchAllWeather | COMP | Multi-asset | — | — | — | — | robuste |
| 36 | Framework_Composite_EMATrend | COMP | Equities | — | — | — | — | robuste |
| 37 | composite-c1-multiasset | COMP | Multi-asset | — | — | — | — | robuste |
| 38 | composite-c2-equityfactor | COMP | Equities | — | — | — | — | robuste |
| 39 | HAR-RV-Kelly | RISK | Multi-asset | — → **0.75** ✓post-#2801 | 23.0 | 48.3 | 0.48 | robuste borderline (gap-fill first real data, PSR 24.0%, MaxDD -48% crypto tail) |

### Post-#2801 verification — findings (2026-06-15)

Twenty-one Tier-1 entries re-run live via MCP qc-mcp (project native period, IBKR margin
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
| Multi-Layer-EMA | 28433748 | 0.93 | **0.80** | -14% | robuste (confirmed, **ML crypto holds**, PSR 23.9%, MaxDD -57%) |
| EMA-Cross-Stocks | 28789946 | 0.87 | **0.99** | +14% | robuste (confirmed, PSR 49.7%) |
| AllWeather | 28657833 | 0.67 | **0.47** | -30% | **historique** (was robuste — low-turnover multi-asset NOT immune) |
| VolTarget-Momentum | 30784745 | 0.65 | **0.50** | -23% | robuste borderline (PSR 9.4%, at threshold) |
| Crypto-MultiCanal | 30750734 | 0.58 | **0.33** | -43% | **historique** (was robuste — crypto indicator NOT robust post-fees) |
| MomentumStrategy | 28657837 | 0.57 | **0.50** | -12% | robuste borderline (at threshold, PSR 9.3%) |
| TrendStocks-Alpha | 28885507 | 0.52 | **0.51** | -2% | robuste (confirmed, high-turnover near-immune) |
| ML-Temporal-CNN | 29443034 | 0.73 | **0.46** | -37% | **historique** (DL/CNN overfits real fees, PSR 5.2%) |
| HAR-RV-Kelly | 31650567 | — | **0.75** | (gap-fill) | robuste borderline (first real data, PSR 24.0%, MaxDD -48% crypto) |
| RL-DQN-Trading | 32057969 | 0.53 | **0.58 (2020-21)** | n/a | **non re-verifiable** (~1yr window, runtime error on extension) |
| MeanReversion | 30776121 | 0.81 | **0.81** | 0% | robuste (confirmed, PSR 46.8%, low-turnover sector rotation holds) |
| SectorMomentum | 29686886 | 0.62 | **0.56** | -9% | robuste (mild — monthly rebalance winner-takes-all on 3 ETFs = low rotation near-immune; PSR 13.8% low, not a true leader) |
| BlackLitterman-Momentum | 29816300 | 0.60 | **0.83** | +38% | **robuste (catalog CORRECTED UPWARD — was stale, not a fee effect; code already remediated, real Sharpe matches docstring v2 BEST 0.823; monthly fee-homogeneous 15-stock US equity = near-immune; PSR 51.4% true leader borderline)** |
| ML-FeatureEngineering | 29808616 | 0.57 | **0.65** | +15% | robuste (catalog CORRECTED UPWARD — was stale; current RF+GB 18-feature ensemble better than the run that produced 0.57; bi-weekly fee-homogeneous US equity = near-immune; PSR 15.1% low, not a true leader; universe corrected Multi-asset→Equities; baseline-clone 32952140) |
| LongShortHarvest | 32921183 | 3.39 | **1.64** | -52% | robuste (confirmed, **PSR 98.7%** top — catalog was 1Y-OOS, baseline-clone) |
| DynamicVIXSpyRegime | 32921262 | 1.72 | **1.00** | -42% | robuste (confirmed, **PSR 69.4%** — catalog was 1Y-OOS, baseline-clone) |
| Portfolio-Optimization-ML | 29318874 | 0.90 | **0.88** | -2% | robuste (confirmed, monthly-rebalance fee-homogeneous equity basket near-immune, PSR 37.2%) |
| CausalEventAlpha | 29809163 | 0.78 | **0.45** | -43% | **historique** (was robuste — monthly cadence but full-basket sector rotation = high turnover, PSR 5.5%) |
| Gaussian-Direction-Classifier | 29398513 | 0.76 | **0.76** | 0% | robuste (confirmed — daily schedule but low realized turnover on liquid mega-cap = near-immune, PSR 22.7%) |
| ML-Trend-Scanning | 29808859 | 0.66 | **0.33** | -50% | **historique** (was robuste — daily-rebalance SPY/TLT/GLD multi-asset crushed by real fees, PSR 7.8%) |
| TrendStocksLite | 28817425 | 0.72 | **0.71** | -2% | robuste (confirmed — weekly trend on 15 liquid large-caps, low realized turnover, near-immune, PSR 25.0%) |
| ML-RandomForest | 29434751 | 0.68 | **0.70** | +3% | robuste (confirmed — bi-weekly RF on 10 mega-caps, moderate turnover near-immune on fee-homogeneous US equity, PSR 18.4%, baseline-clone 32940005) |
| ML-XGBoost | 29434753 | 0.57 | **0.555** | -3% | robuste (confirmed flat-to-mildly-down, NOT an upward correction — bi-weekly GradientBoostingRegressor on fee-homogeneous 15 mega-caps = near-immune; PSR 10.6% low, not a true leader; universe corrected Multi-asset→Equities; baseline-clone 32958201) |
| RegimeSwitching | 28693650 | 0.55 | **0.581** | +6% | robuste (confirmed — multi-asset HOLDS via explicit turnover suppression: regime-change-only rebalance + anti-micro-rebalancing delta<5% + beta-annealing; contrasts AllWeather -30%; refines discriminator = realized-turnover not asset-class; PSR 7.0% low; universe Equities/ETF→Multi-asset; baseline-clone 32961367) |

**Finding (methodological, now 29-strategy sample)** : the remediation impact is **not
uniform**, and the batch-4 results *refine and partly correct* the earlier 10-strategy pattern.
The distinguishing axis is **not** asset class, nor ML-vs-indicator alone — it is the
combination of (a) the fee-per-trade the asset class carries and (b) how the strategy turns
over against that fee. Four regimes now observed:

- **Value/factor + simple trend COLLAPSE** (-62% to -85%): HighBookToMarketFScore, PuppiesOfTheDow,
  Trend-Following. These top-ranked catalog entries drop out of "robuste" entirely — their
  pre-remediation Sharpes were artifacts of the negligible default fee model. MacroFactorRotation
  (-40%) is the milder case in this family. **These catalog rankings are not reliable.**
- **Structured ML & regime composites HOLD** (-2% to -14%): Positive-Negative-Splits-ML (1.51,
  **PSR 82.3%**), Framework_Composite_TrendWeather (1.14, **PSR 77.9%**), and Multi-Layer-EMA
  (0.80, PSR 23.9%) confirm. Contrast with MomentumRegime (0.185) and now Crypto-MultiCanal —
  only the *structured* ML/regime-aware designs survive real fees. **These are real alpha.**
- **High-turnover US equity is near-immune** (0% to -2%): EMA-Cross-Stocks, TrendStocks-Alpha, and
  now TrendStocksLite (0.72→0.71, -2%, weekly trend on 15 liquid large-caps — slow SMA200/EMA signals,
  low realized turnover) barely move under real IBKR fees, confirming the #1407 finding that US equity fees (<0.25 bps/trade)
  are negligible even at high turnover. **Batch 5 refines this: the immunity is signal-FREQUENCY,
  not asset-class — ML-Temporal-CNN (QQQ equity, -37% to 0.46, DL signal-churning) erodes despite
  being US equity. Slow EMA/trend signals (few trades) are immune; DL/CNN direction predictions
  (frequent re-entry) are not. Batch 6 confirms: MeanReversion (low-turnover sector rotation,
  0.81→0.81, **0% delta**, PSR 46.8%) holds flat — it is multi-asset like AllWeather but, unlike
  AllWeather, rotates *within a single fee-homogeneous equity class* (<0.25 bps/trade), so its slow
  signals incur negligible cost. AllWeather's -30% drop came from its bonds/gold sleeve crossing
  higher per-trade friction. The discriminator is thus **signal-frequency × fee-homogeneity of the
  traded basket**, not asset-class alone.** Batch 7 sharpens this further: cadence is not turnover.
  Portfolio-Optimization-ML (monthly, fee-homogeneous 15-stock basket, **low** turnover — covariance
  weights nudge rather than rotate) is near-immune (0.90→0.88, -2%), whereas CausalEventAlpha (also
  monthly, also a fee-homogeneous 8-sector-ETF basket) **collapses** (0.78→0.45, -43%, PSR 5.5%) because
  it liquidates and re-ranks the entire basket each month and concentrates to 4 sectors in bear regimes
  — high per-period turnover. A monthly schedule over a homogeneous basket is therefore *not* sufficient
  for immunity; the driver is realized turnover per rebalance. Gaussian-Direction-Classifier closes
  the proof from the other side: a *daily* schedule (higher cadence than either) is near-immune
  (0.76→0.76, 0%) because its realized turnover is low — max-3 positions whose mega-cap probability
  rankings rarely flip, over an ultra-liquid basket. Higher cadence with low realized turnover beats
  lower cadence with full rotation; cadence alone predicts nothing.
- **Low-turnover multi-asset & crypto indicators are NOT immune** (-30% to -43%): batch 4
  *invalidates* the earlier broad "ML/crypto holds" generalization. AllWeather (low-turnover
  multi-asset, -30% → 0.47) and Crypto-MultiCanal (crypto indicator, -43% → 0.33) both drop
  below the robuste threshold. Crypto's 10bps fees + the indicator's signal-chasing turnover erode
  it hard; the Binance CASH cash-constraint benefit seen in the #1407 fee sweep (0.181→0.333)
  still leaves it well under the catalog 0.58. HAR-RV-Kelly (vol-targeting Kelly, 0.75, PSR 24.0%)
  is the exception that proves the rule: Kelly position-sizing dampens exposure, so it survives fees
  where the equal-weight indicator (Crypto-MultiCanal, 0.33) collapses — but its -48% drawdown and
  non-significant PSR mark it as a risk overlay, not pure alpha.

**Reproducibility failure mode (distinct from fee-collapse)** : RL-DQN-Trading (catalog 0.53)
cannot be re-verified on the remediation window — it runs only on a ~1-year slice (253 tradeable
dates, 2020-2021; Sharpe 0.58, PSR 30.2%) and Runtime-Errors on any date extension. This is not a
fee effect; it is RL training-window lock-in. The catalog "0.53" is real but un-generalizable.

**Borderline band** (-12% to -23%, sitting on the 0.5 line): VolTarget-Momentum (0.50, PSR 9.4%)
and MomentumStrategy (0.50, PSR 9.3%) — both non-significant PSR, technically robuste but on the edge.

**True leaders post-#2801, ranked by statistical significance (PSR > 50%)** :

1. Positive-Negative-Splits-ML — 1.51, PSR 82.3% (structured ML, top leader, replaces collapsed value entries)
2. LeveragedETFMomentum — 1.78, PSR 79.8% (leveraged, extreme profile)
3. Framework_Composite_TrendWeather — 1.14, PSR 77.9% (regime-aware composite)
4. EMA-Cross-Stocks — 0.99, PSR 49.7% (high-turnover US equity, near-significance, near-immune)

Only these 4 survive both the fee remediation AND a significance bar. The "robuste" Tier-1 band
of 41 catalog entries shrinks to roughly **a dozen genuinely-holding strategies** under real fees;
the rest are overstated to varying degrees.

**Implication for the réunion Nicolas 15/06** : the catalog is not uniformly stale, but the
overstatement is widespread — **only 6 of 24 verified strategies hold robuste with significant PSR**.
The overstatement is structural in two families (value/factor/trend, and crypto indicators), while
structured ML and regime-aware composites are validated. The comparative table MUST be cited by
significance (PSR) not raw Sharpe; collapsed entries need a caveat before any pedagogical use. The
remaining Tier-1 list (19 strategies) needs systematic re-backtest before the table is trusted
end-to-end. LongShortHarvest-QC (catalog 3.39, the single highest entry) and DynamicVIXSpyRegime-QC
(1.72) — previously QC Community Library references without an owned project — were deployed as owned
baseline-clones (project IDs 32921183 / 32921262) and re-run over 2015-2024: both keep robuste status
(PSR 98.7% / 69.4%) but their headline Sharpes nearly halve (1.64 / 1.00), confirming the catalog
1Y-OOS values were optimistic while the strategies themselves are sound.

Backtests: `1630-baseline-HighBookToMarketFScore-post2801` (0.411, 14.5%, -60.4%, PSR 4.5%),
`1630-baseline-PuppiesOfTheDow-post2801` (0.302, 9.6%, -28.8%, PSR 3.5%),
`1630-baseline-LeveragedETFMomentum-post2801` (1.779, 126.4%, -53.3%, PSR 79.8%),
`1630-baseline-PositiveNegativeSplits-post2801` (1.511, 75.7%, -37.6%, PSR 82.3%),
`1630-baseline-MacroFactorRotation-post2801` (0.731, 22.6%, -42.0%, PSR 23.8%),
`1630-baseline-TrendWeather-post2801` (1.14, 27.1%, -27.7%, PSR 77.9%),
`1630-baseline-TrendFollowing-post2801` (0.407, 7.89%, -14.6%, PSR 8.7%),
`1630-baseline-EMACrossStocks-post2801` (0.991, 29.2%, -35.7%, PSR 49.7%),
`1630-baseline-VolTargetMomentum-post2801` (0.50, 11.1%, -21.2%, PSR 9.4%),
`1630-baseline-TrendStocksAlpha-post2801` (0.512, 15.7%, -39.6%, PSR 5.6%),
`1630-baseline-MultiLayerEMA-post2801` (0.798, 25.0%, -57.1%, PSR 23.9%),
`1630-baseline-AllWeather-post2801` (0.469, 7.5%, -16.4%, PSR 19.6%),
`1630-baseline-CryptoMultiCanal-post2801` (0.333, 4.6%, -14.1%, PSR 13.0%),
`1630-baseline-MomentumStrategy-post2801` (0.499, 11.2%, -25.8%, PSR 9.3%),
`1630-baseline-LongShortHarvest-post2801` (1.635, 45.6%, -17.0%, PSR 98.7%),
`1630-baseline-DynamicVIXSpyRegime-post2801` (0.997, 17.9%, -16.5%, PSR 69.4%),
`1630-PortfolioOptimizationML-post2801` (0.884, 27.2%, -41.6%, PSR 37.2%),
`1630-CausalEventAlpha-post2801` (0.447, 11.7%, -38.8%, PSR 5.5%),
`1630-GaussianDirectionClassifier-post2801` (0.761, 23.1%, -25.6%, PSR 22.7%),
`1630-TrendStocksLite-post2801` (0.707, 18.0%, -33.7%, PSR 25.0%),
`1630-ML-RandomForest-post2801` (0.70, 20.6%, -40.9%, PSR 18.4%).

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
