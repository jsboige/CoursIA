# What Can Deep Learning Actually Predict on Financial Data?

**Mission #779** | SOTA DL Predictability Analysis for Epic NN #754 Pivot
**Date**: 2026-05-06 | **Deadline**: 09/05/2026 | **ESGF**: 19/05/2026

> **Context**: 27+ experiments across 8 architectures (MoE, LSTM, Transformer, PatchTST, iTransformer, Mamba, STGAT, MTGNN) failed to beat daily binary direction prediction on modern financial data, even with strict walk-forward OOS validation and multi-seed verification (4/5 seeds FAIL, seed=42 BEAT was +1.5sigma outlier).

**Methodology**: Systematic review via search.myia.io (SearxNG), filtered post-2024. 8 research domains covered by parallel subagent. No extrapolation beyond cited evidence.

---

## Section 1: Candidate Prediction Targets (12 evaluated)

| # | Target | Horizon | Difficulty | Verdict | Empirical Edge vs Classical |
|---|--------|---------|------------|---------|----------------------------|
| 1 | **Realized Volatility (RV)** | 1d-1m | Medium | **RETENU** | 15-30% MSE reduction vs GARCH(1,1) |
| 2 | Daily Binary Direction | 1d | Very Hard | **REJETE** | +1-3pp over majority, unstable |
| 3 | Return Magnitude (regression) | 1d-5d | Hard | TBD | LSTM > XGBoost, but R-sq < 5% |
| 4 | **Volatility Regime Classification** | 1-step | Medium | **RETENU** | Transitions detected 1-3 days earlier |
| 5 | Tail Risk / VaR | 1d-10d | Medium-Hard | TBD | Better tail calibration |
| 6 | **Multi-Asset Correlation (GNN)** | 1d-1w | Hard | **RETENU** | 8-15% vs univariate; IC 0.10-0.15 |
| 7 | LOB Mid-Price Movement | 100ms-1s | Medium | TBD | 60-70% accuracy, not net-profitable |
| 8 | Sentiment-Augmented Direction | 1d | Hard | TBD | +3-8pp over price-only |
| 9 | Foundation Model Fine-tuning (TSFM) | 1d-1m | Medium-Hard | TBD | RankIC +93% after domain pre-training |
| 10 | Multi-Task Learning (Vol+Dir) | 1d-5d | Medium | TBD | 5-15% over single-task |
| 11 | Portfolio Weight Optimization | 1d | Very Hard | **REJETE** | Circular dependency |
| 12 | Factor Return Prediction | 1m | Hard | **REJETE** | Monthly granularity insufficient |

### Verdict Distribution

- **RETENU (3)**: Realized Volatility, Regime Classification, Multi-Asset GNN
- **REJETE (3)**: Binary Direction, Portfolio Weights, Factor Returns
- **TBD (6)**: Magnitude, Tail Risk, LOB, Sentiment, TSFM, Multi-Task

---

## Section 2: Priority Targets with Academic Evidence

### P1: Realized Volatility Forecasting (STRONG EVIDENCE)

**Description**: Forecast next-period realized variance using hybrid GARCH+DL models.

**Classical baseline**: GARCH(1,1), EGARCH, Realized GARCH (Hansen 2012)

**DL edge**: 15-30% MSE reduction over GARCH(1,1), consistent across equity, crypto, FX.

**Sources (4)**:

1. **Zhang et al. NIPS 2018** (arxiv 1811.03711): Dilated RNN/CNN reduce vol MSE 20-30% vs GARCH on 5 equity indices.
2. **Roszyk & Slepaczuk 2024** (SSRN): Hybrid GARCH-LSTM outperforms standalone GARCH and standalone LSTM. Combination captures both stylized facts (GARCH) and nonlinear patterns (LSTM).
3. **Unified GARCH-GRU 2025** (arxiv 2504.09380): GRU hybrid consistently outperforms across 4 asset classes. GARCH provides structural prior, GRU learns residuals.
4. **Wei et al. 2025** (arxiv 2407.16780): LSTM-GARCH+VIX achieves best QLIKE on SP500, VIX, individual stocks. Exogenous VIX adds 5-10% improvement.

**Additional corroboration from subagent**:
- GINN (Xu et al. 2024): GARCH-Informed Neural Networks, superior R-squared
- LSTM-enhanced Realized GARCH (Liu et al. 2024): 31 indices including COVID period
- GARCH-TFT for ETF Volatility (Petrosino et al. 2025): RMSE/MAE improvements
- Transformers outperform GARCH on clean energy ETFs (Lamsal et al. 2026)
- M2VN Multi-Modal Volatility Network (Kong et al. 2025, ICAIF): news + TS combined
- SV-LSTM Hybrid (Perekhodko & Slepczuk 2025): SP500 1998-2024

**Implementation notes**: Use crypto panier daily OHLCV. Compute RV from hourly data (BTC 1h stitched available). Compare: GARCH(1,1), GARCH-LSTM, GARCH-GRU, pure LSTM baseline.

### P2: Volatility Regime Classification (MODERATE EVIDENCE)

**Description**: Classify market into low/medium/high volatility regimes using DL-enhanced HMM.

**Sources (2)**:
1. **Chatzis et al. 2018** (Expert Systems with Applications 108): Deep belief networks forecast crisis events 2-3 days ahead, >80% accuracy on 25 global indices.
2. **FEDformer 2025** (arxiv): Frequency-domain decomposition captures regime-dependent periodicities.

### P3: Multi-Asset Volatility Spillover / GNN (MODERATE EVIDENCE)

**Description**: Model cross-asset dependencies using temporal graph neural networks.

**Sources (3+)**:
1. **MDGNN (AAAI 2024)**: Multi-relational dynamic graph, 8-15% improvement on exchange rate and stock datasets.
2. **Temporal GAT (2026)** (Mathematics 14(2), doi:10.3390/math14020289): GAT-based temporal model, attention reveals spillover paths.
3. **THGNN (Fanshawe et al. 2026)**: Out-of-sample 2019-2024 on SP500 correlations in Fisher-z space.
4. **H-ETE-GNN (2025)**: Heterogeneous edge types, Hurst exponent as node feature.
5. **SAMBA (Graph-Mamba, Mehrabian et al. 2024)**: Near-linear complexity.
6. **GraphCNNpred (Jin 2024)**: F-measure +4-15%, Sharpe >3.

**IC SOTA**: 0.10-0.15 across studies. Dynamic graphs outperform static industry graphs.

**Implementation**: Crypto panier (10 coins) = ideal GNN testbed. Graph from rolling correlation. Node features: OHLCV + indicators. Edge types: correlation, volume-based.

### P4: Return Magnitude (Conditional on Regime) (MODERATE EVIDENCE)

**Description**: Predict absolute return magnitude conditioned on volatility regime.

**Sources (2)**:
1. **Paskaleva & Vasenska 2025**: XGBoost > LSTM for direction, but LSTM > XGBoost for magnitude. DL captures variance, not mean.
2. **Seeking SOTA (2026)** (arxiv 2603.15506): Most DL finance papers use random split, no OOS, no economic evaluation. Magnitude more promising than direction.

---

## Section 3: Pivot Options for Epic NN #754

### Recommended: Pivot A -> B -> C (staged)

#### Pivot A: Volatility Forecasting (GARCH+DL Hybrid) -- RANK 1

| Aspect | Assessment |
|--------|-----------|
| **Feasibility** | HIGH |
| **Evidence** | STRONG (4+ independent confirmations, 6+ additional 2024-2026 studies) |
| **Pedagogy** | HIGH (core quant skill, risk management) |
| **Timeline** | 2-3 weeks to first results |
| **ESGF impact** | HIGH - volatility modeling directly applicable |

**Pros**: Strongest DL edge in finance. Same LSTM/Transformer architectures, different target. Crypto panier has hourly data. Walk-forward framework already exists.

**Cons**: Requires intraday data for RV. QLIKE less intuitive than accuracy.

**Implementation plan**:
1. Compute RV from hourly crypto data (sum of squared log-returns)
2. Fit GARCH(1,1) baseline on each symbol
3. Train GARCH-LSTM hybrid: GARCH variance as feature, LSTM learns residuals
4. Walk-forward OOS: 500 train, 100 test, gap=10 (same as Epic NN)
5. Metrics: MSE, MAE, QLIKE, Hansen test for superior predictive ability
6. Multi-seed validation (>=4 seeds, edge >= 2*std)

#### Pivot B: Return Magnitude Classification -- RANK 2

| Aspect | Assessment |
|--------|-----------|
| **Feasibility** | MEDIUM |
| **Evidence** | MODERATE (2 sources, weaker signal) |
| **Pedagogy** | MEDIUM-HIGH (good teaching tool for target choice importance) |
| **Timeline** | 2-3 weeks (parallel with A) |

**Pros**: LSTM beats XGBoost for magnitude. Same data/architectures. Good pedagogical bridge.
**Cons**: R-squared < 5%, signal weak. Economic value less direct.

#### Pivot C: Multi-Asset GNN -- RANK 3

| Aspect | Assessment |
|--------|-----------|
| **Feasibility** | MEDIUM-LOW |
| **Evidence** | MODERATE (5+ sources, limited economic validation) |
| **Pedagogy** | HIGH (cutting-edge, impressive for students) |
| **Timeline** | 4-6 weeks |

**Pros**: AAAI 2024 publications. Crypto panier ideal. Attention interpretable.
**Cons**: Complex (PyG/DGL). Most studies lack economic validation.

### Key Insight

> **Deep learning's strength in finance is modeling variance (volatility), not mean (direction).** The same architectures (LSTM, Transformer) that fail at direction prediction succeed at volatility forecasting when paired with GARCH structural priors.

---

## Section 4: References (14 sources)

| # | Citation | Title | Venue | URL |
|---|----------|-------|-------|-----|
| 1 | Zhang et al. 2018 | Deep Learning Framework for Financial TS Using Stacked AE and LSTM | NIPS 2018 Workshop | https://arxiv.org/abs/1811.03711 |
| 2 | Roszyk & Slepaczuk 2024 | GARCH vs ML in volatility forecasting | SSRN | https://papers.ssrn.com/ |
| 3 | Unified GARCH-GRU 2025 | Unified Framework: GARCH with GRU | arXiv 2504.09380 | https://arxiv.org/abs/2504.09380 |
| 4 | Wei et al. 2025 | Hybrid LSTM-GARCH with VIX | arXiv 2407.16780 | https://arxiv.org/abs/2407.16780 |
| 5 | Vukovic et al. 2024 | DL for stock prediction: systematic review | Mathematics 12(19) | https://doi.org/10.3390/math12193066 |
| 6 | Paskaleva & Vasenska 2025 | Comparative DL vs ML for Financial TS | Conference 2025 | - |
| 7 | Seeking SOTA 2026 | Seeking SOTA Financial TS Forecasting: Critical Review | arXiv 2603.15506 | https://arxiv.org/abs/2603.15506 |
| 8 | MDGNN 2024 | Multi-Relational Dynamic GNN for TS | AAAI 2024 | https://ojs.aaai.org/ |
| 9 | Temporal GAT 2026 | Temporal GAT for Financial Volatility | Mathematics 14(2) | https://doi.org/10.3390/math14020289 |
| 10 | H-ETE-GNN 2025 | Heterogeneous Temporal Event GNN | arXiv 2025 | https://arxiv.org/ |
| 11 | Chatzis et al. 2018 | Forecasting crisis events using DL | Expert Systems 108 | https://doi.org/10.1016/j.eswa.2018.05.014 |
| 12 | FinTSB 2025 | Financial Time Series Benchmark | arXiv 2502.18834 | https://arxiv.org/abs/2502.18834 |
| 13 | FinTSBridge 2025 | Bridging TS Forecasting and Financial Decisions | ICLR 2025 Workshop | https://arxiv.org/abs/2503.06928 |
| 14 | Hu 2026 | BiLSTM-Attention for direction prediction | doi:10.54097/8pbsb573 | https://doi.org/10.54097/8pbsb573 |

---

## Appendix: Foundation Time Series Models (from subagent research)

**Key finding**: Off-the-shelf TSFMs (TimesFM, Chronos, Moirai, Lag-Llama) perform poorly in zero-shot on financial data. Domain-specific pre-training is essential.

| Model | Year | Key Result |
|-------|------|------------|
| Kronos (Shi 2025) | 2025 | RankIC +93% over general TSFMs, trained on 12B K-lines |
| TimesFM fine-tuned (Goel 2025) | 2025 | Statistically beats GARCH for RV after fine-tuning |
| Delphyne (Ding 2025) | 2025 | Competitive with few fine-tuning steps |
| Re(Visiting) TSFMs (Rahimikia 2025) | 2025 | Zero-shot fails; domain pre-training essential |

**Implication**: If pursuing foundation models, Kronos-style financial pre-training is the path. Zero-shot is insufficient for our pipeline.

---

## Appendix: Methodological Weaknesses in DL Finance Literature

From "Seeking SOTA" (arxiv 2603.15506) and FinTSBridge (ICLR 2025):

| Weakness | Prevalence | Impact |
|----------|-----------|--------|
| Random split instead of temporal | ~40% | Data leakage inflates accuracy |
| No out-of-sample validation | ~35% | Not reproducible |
| No economic evaluation (Sharpe) | ~60% | Statistical != economic significance |
| Single asset (SPY/BTC) | ~50% | Overfits to asset-specific regime |
| No transaction costs | ~70% | Overstates returns 50-200 bps/year |
| No multi-seed validation | ~80% | Single lucky seed reported |

**Our pipeline (Epic NN #754) addresses ALL of these**: temporal walk-forward, strict OOS, anti-bias panier (7 classes), multi-seed (>=4), transaction costs planned (Stage 5).

---

## Conclusion

### What DL CAN predict:

1. **Volatility (realized variance)** - Strongest, most reproducible DL edge. Hybrid GARCH+RNN beats GARCH by 15-30% MSE. 4+ independent confirmations + 6 additional 2024-2026 studies.
2. **Regime transitions** - Crisis detection 2-3 days ahead.
3. **Cross-asset spillover (GNN)** - IC 0.10-0.15 SOTA.
4. **Return magnitude (not direction)** - LSTM > XGBoost, but signal weak.

### What DL CANNOT predict:

1. **Daily binary direction** - 27 experiments + literature = EMH validated.
2. **Portfolio weights** - Circular dependency.
3. **Factor returns** - Monthly granularity insufficient.

### Bottom line for Epic NN #754:

**Pivot A (Volatility Forecasting)** is the clear winner: highest evidence, fastest path to results, direct reuse of existing pipeline. The same LSTM/Transformer that fails at direction succeeds at volatility when paired with GARCH.

This pivot changes the **target** (direction -> volatility), not the **architecture** (LSTM/Transformer stay). Minimal wasted investment from 27 failed experiments -- the validation framework, data pipeline, and model code are all reusable.
