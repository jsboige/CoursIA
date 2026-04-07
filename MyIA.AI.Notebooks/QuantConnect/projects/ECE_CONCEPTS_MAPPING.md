# ECE Student Concepts - QC Strategies Mapping

**Issue**: #238 - Integrate ECE student project concepts into QC trading strategies pool
**Source**: ECE Ing4 Projet 2 soutenances (March 30-31, 2026), 27+ student projects across 3 groups

---

## Integration Status

| # | Concept | Student | Group | Priority | Status | QC Project |
|---|---------|---------|-------|----------|--------|------------|
| 1 | HMM + K-Means Voting Regime Detection | Brusset | Gr01 H.4 | HIGH | DONE | `HMM-KMeans-Voting/` |
| 2 | 23-Feature ML Stock Selection | Balssa | Gr01 H.1 | HIGH | PENDING | - |
| 3 | Causal ML Event Alpha by Sector | ErwanSi | Gr03 G.1 | HIGH | PENDING | - |
| 4 | Causal Forward-Filter + Feature Engineering | Maisonnave | Gr01 H.4b | HIGH | PENDING | - |
| 5 | Black-Litterman + Momentum Views | 4 groups | Mixed | MEDIUM | PENDING | - |
| 6 | Adaptive Conformal Inference Risk Overlay | El Bakkali | Gr02 | MEDIUM | PENDING | - |
| 7 | Dynamic Delta/Skew Options Logic | Asseli | Gr01 H.5 | MEDIUM | PENDING | - |
| 8 | RL Environment Design Improvements | Rebot | Gr03 | MEDIUM | PENDING | - |

---

## 1. HMM + K-Means Voting Regime Detection (DONE)

**Student**: Brusset (Gr01 H.4)
**QC Cloud Source**: Project #29049549 (ECE_School org)
**Local Project**: `projects/HMM-KMeans-Voting/`

### Core Concepts

- **Gaussian HMM (3 states)**: Full Baum-Welch EM implementation from scratch (forward-backward algorithm + xi + gamma posteriors + Viterbi decoding), pure numpy
- **K-Means Clustering**: Pure numpy with multi-initialization (5 restarts, inertia-based selection)
- **Voting Ensemble**: HMM and K-Means independently classify regime, then vote. Priority to bear when they disagree
- **Crisis Circuit Breaker**: 5-day annualized volatility > 25% forces bear allocation, overrides models
- **MAD Winsorization**: Median Absolute Deviation based outlier clipping (constant 1.4826, 4-MAD threshold)
- **Feature Engineering**: returns, vol20, mom60, vol_ratio, z-score normalized

### Backtest Results (2010-2024, $100k, IB Margin)

| Metric | HMM-KMeans-Voting | RegimeSwitching (benchmark) | Markov-Regime-Detection |
|--------|-------------------|----------------------------|------------------------|
| Sharpe | 0.488 | 0.553 | 0.408 |
| CAGR | 6.99% | - | - |
| MaxDD | 23.8% | - | - |
| Net Profit | 157.5% | - | - |
| Trades | 2382 | - | - |
| Win Rate | 60% | - | - |
| Alpha | 0.02 | - | - |
| Beta | 0.188 | - | - |
| PSR | 6.904 | - | - |

### Reusable Components

| Component | Location | Reusability |
|-----------|----------|-------------|
| `KMeans` class | main.py:7-48 | Drop-in sklearn alternative for QC (no external dep) |
| `GaussianHMM` class | main.py:51-163 | Full Baum-Welch + Viterbi, reusable for any regime strategy |
| MAD Winsorization | main.py:248-251 | General-purpose outlier handling |
| Crisis Circuit Breaker | main.py:352-382 | Applicable to any regime/volatility strategy |
| `_label_states()` | main.py:258-268 | Automatic state-to-regime labeling (by vol/return) |

### Comparison with Existing Strategies

| Aspect | RegimeSwitching | Markov-Regime-Detection | HMM-KMeans-Voting |
|--------|----------------|------------------------|-------------------|
| Regime model | Single HMM | Single Markov | Dual (HMM + K-Means vote) |
| Crisis detection | None | None | Vol-based circuit breaker |
| Outlier handling | None | None | MAD winsorization |
| NumPy-only | Partial | Partial | Full (no sklearn dep) |
| Universe | SPY+TLT | SPY | SPY+TLT+IEF+GLD+DJP |

### Pedagogical Value

- Demonstrates ensemble methods in quantitative finance
- Shows how to implement HMM from scratch (educational for ECE students)
- Illustrates crisis management and risk overlays
- Clean PEP8 code suitable as course example

---

## 2. 23-Feature ML Stock Selection (PENDING)

**Student**: Balssa (Gr01 H.1)
**QC Cloud Source**: Project #29392270 "Adaptable Tan Chinchilla" (ECE_School org, 45 backtests)

### Concept

23 technical features for ML-based stock selection with RF + GB ensemble, top 50 US universe, walk-forward OOS validation (6 x 5yr periods).

### Key Features to Harvest

| Feature | Type | In Our ML Strategies? |
|---------|------|-----------------------|
| volume_trend | Volume | NO - novel |
| adx_norm | Trend | NO - novel |
| volatility_60d | Volatility | Partially (vol20 only) |
| bb_width | Volatility | NO - novel |
| momentum_60d | Momentum | YES (similar) |
| return_10d | Returns | YES |
| pb_norm | Fundamental | NO - novel |
| atr_norm | Volatility | NO - novel |

### Integration Plan

1. Extract 23-feature list from QC Cloud project #29392270
2. Test novel features individually against ML-RandomForest v3 (Sharpe 0.682)
3. Test feature combinations with walk-forward methodology
4. Update ML-FeatureEngineering if features improve performance

### Target Strategies

- `ML-RandomForest/` (Sharpe 0.682 v3)
- `ML-FeatureEngineering/` (shared feature module)
- `Sector-ML-Classification/` (Sharpe 0.473)

---

## 3. Causal ML Event Alpha by Sector (PENDING)

**Student**: ErwanSi (Gr03 G.1)
**Source**: Gr03 repo, 3782 lines Python

### Concept

Double Machine Learning (EconML) pipeline: OLS -> DML -> CausalForest -> DoWhy, quantifying sector-specific CATE (Conditional Average Treatment Effect) of earnings surprises.

### Key Insight

Technology has 4x the earnings sensitivity of Utilities (CATE 0.035 vs 0.008). This heterogeneous treatment effect by sector can inform event-driven position sizing.

### Integration Plan

1. Design "Causal Event Alpha" strategy spec
2. Start with simpler estimation (rolling regression by sector) as first pass
3. Full DML pipeline if sklearn + econml available on QC
4. Overweight Tech around earnings (high CATE), underweight Utilities (low CATE)

### Novelty

We have NO causal ML strategy. This is a genuinely novel approach in our pool.

---

## 4. Causal Forward-Filter + Feature Engineering (PENDING)

**Student**: Maisonnave (Gr01 H.4b)
**Source**: Gr01 repo, 5912 lines Python, VAE-HMM architecture

### Concept

Custom forward-filter for causal regime prediction (no look-ahead bias). 420 lines of feature engineering. Anti-micro-rebalancing threshold. Beta-annealing.

### Key Components

| Component | Description | Value |
|-----------|-------------|-------|
| Causal forward-filter | Prevents look-ahead in regime detection | Critical for live trading |
| 420-line feature pipeline | Technical + statistical features | Comprehensive feature catalog |
| Anti-micro-rebalancing | Threshold to avoid tiny rebalances | Reduces transaction costs |
| Beta-annealing | Gradual regime transition | Smoother allocation changes |

### Integration Plan

1. Backport causal forward-filter into `RegimeSwitching/` and `Markov-Regime-Detection/`
2. Extract feature engineering as shared utility module
3. Apply anti-micro-rebalancing threshold to all regime strategies

### Target Strategies

- `RegimeSwitching/` (Sharpe 0.553)
- `Markov-Regime-Detection/` (Sharpe 0.408)
- `HMM-KMeans-Voting/` (Sharpe 0.488)

---

## 5-8. Medium Priority Concepts (Deferred)

### 5. Black-Litterman + Momentum Views

Four student groups implemented BL variants. Best elements: He & Litterman Omega calibration (ilhan/Farhan), multi-window momentum views with sigmoid confidence (Tour/Monteiro), sector constraints. Would complement Portfolio-Optimization-ML (Sharpe 0.896).

### 6. Adaptive Conformal Inference Risk Overlay

ACI (Gibbs-Candes 2021) for dynamic confidence intervals with online alpha adjustment. Novel risk management applicable as overlay to any strategy.

### 7. Dynamic Delta/Skew Options Logic

IV percentile-based delta selection + 25-delta skew adjustment for Wheel strategy. More sophisticated than our Option-Wheel (fixed OTM 5%, VIX filter).

### 8. RL Environment Design Improvements

Custom Gymnasium env with tanh+sigmoid+L1 action->weight mapping, explicit transaction costs + short borrow, walk-forward 10 windows. Better than RL-DQN-Trading env design.

---

## Methodology

Each integration follows this process:

1. **Extract**: Pull concept from student QC Cloud project or repo
2. **Clean**: PEP8 naming, remove emojis, add docstrings, pure numpy where possible
3. **Benchmark**: Backtest against existing strategies in same category (2010-2024)
4. **Compare**: Document performance delta vs benchmarks
5. **Integrate**: Add to `projects/` directory with clear attribution
6. **Document**: Update this mapping and project README

## Attribution

All student concepts include attribution in the strategy docstring:
```
Source: ECE student project (StudentName, Group), adapted for ESGF pool.
Issue #238 - Integrate ECE student concepts into QC strategies.
```
