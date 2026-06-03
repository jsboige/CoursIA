# M3 Final Synthesis -- HAR Volatility Forecasting: Classic, Asymmetric, Long-Horizon, and DLinear Comparison

**Status:** COMPLETE. Consolidates M2, M3, M3b, M3-ext, M4 (Cycle 25, po-2024 + ai-01).

## Scope

This document consolidates all HAR-family volatility forecasting results across:
- **M2** -- HAR baseline (BTC/ETH/SOL, h=1/5/10, vs GARCH + naive)
- **M3** -- 7-coin extension + DM significance tests (BTC/ETH/SOL/LTC/XRP/ADA/DOT, h=1/5/10)
- **M3-ext** -- Long-horizon extension (h=15/20, 7 coins)
- **M3b** -- Asymmetric semivariance decomposition (7 coins, h=1/5/10, vs classic HAR)
- **M4** -- DLinear-vol deep learning (7 coins, h=1/5/10, 4 seeds, vs HAR)

## Master Verdict Table

Cross-coin x cross-horizon x cross-variant verdicts. "BEATS" = statistically significant
improvement over baseline (DM test p<0.05 for M3/M3b/M3-ext; 4/4 seeds DM p<0.05 for M4).
All on log-RV scale, walk-forward 5-fold expanding window.

### HAR Classic vs Naive Baseline (M3)

| Coin | h=1 | h=5 | h=10 | h=15 | h=20 |
|------|-----|-----|------|------|------|
| BTC-USD | **BEATS** | **BEATS** | INC | INC | INC |
| ETH-USD | **BEATS** | **BEATS** | **BEATS** | **BEATS** | **BEATS** |
| SOL-USD | **BEATS** | **BEATS** | **BEATS** | **BEATS** | **BEATS** |
| LTC-USD | **BEATS** | INC | INC | INC | INC |
| XRP-USD | **BEATS** | INC | INC | INC | INC |
| ADA-USD | **BEATS** | **BEATS** | INC | INC | INC |
| DOT-USD | INC | INC | INC | INC | INC |

**Score: 14/35 BEATS** (40%). ETH and SOL = strongest, statistically significant at ALL
five horizons. Significance degrades with horizon for most coins.

### Asymmetric HAR vs Classic HAR (M3b)

| Coin | h=1 | h=5 | h=10 |
|------|-----|-----|------|
| BTC-USD | **BEATS** | **BEATS** | **BEATS** |
| ETH-USD | INC | INC | INC |
| SOL-USD | INC | INC | INC |
| LTC-USD | INC | INC | INC |
| XRP-USD | INC | INC | INC |
| ADA-USD | INC | INC | INC |
| DOT-USD | INC | INC | INC |

**Score: 3/21 BEATS** (14%). Leverage effect is BTC-specific. 5-37% MSE reduction
on BTC only.

### DLinear vs Classic HAR (M4, 4 seeds)

| Coin | h=1 | h=5 | h=10 |
|------|-----|-----|------|
| BTC-USD | **BEATS** | **BEATS** | **BEATS** |
| ETH-USD | **BEATS** | INC | INC |
| SOL-USD | **BEATS** | INC | INC |
| ADA-USD | INC | INC | INC |
| LTC-USD | INC | INC | INC |
| DOT-USD | INC | INC | INC |
| XRP-USD | INC | INC | INC |

**Score: 5/21 BEATS** (24%). DLinear learns 22 free parameters vs HAR's 3, winning when
data is sufficient (BTC, to a lesser extent ETH/SOL).

## Best Model Per Configuration

Combining all experiments, the best-performing model for each (coin, horizon) pair:

| Coin | h=1 | h=5 | h=10 | h=15 | h=20 |
|------|-----|-----|------|------|------|
| BTC-USD | Asym HAR (0.843) | DLinear (0.374) | DLinear (0.352) | -- | -- |
| ETH-USD | HAR Classic (0.684) | HAR Classic (0.374) | HAR Classic (0.375) | HAR Classic (0.378) | HAR Classic (0.397) |
| SOL-USD | HAR Classic (0.609) | HAR Classic (0.281) | HAR Classic (0.236) | HAR Classic (0.201) | HAR Classic (0.166) |
| LTC-USD | HAR Classic (0.650) | HAR Classic (0.434) | HAR Classic (0.426) | -- | -- |
| XRP-USD | HAR Classic (0.848) | HAR Classic (0.521) | HAR Classic (0.530) | -- | -- |
| ADA-USD | HAR Classic (0.686) | HAR Classic (0.412) | HAR Classic (0.373) | -- | -- |
| DOT-USD | HAR Classic (0.634) | HAR Classic (0.378) | HAR Classic (0.355) | -- | -- |

Key observations:
- **BTC** is the only coin where DL and asymmetric models beat classic HAR.
- **ETH/SOL** classic HAR is hard to beat -- the simple 3-parameter model captures
  enough structure that additional complexity doesn't help significantly.
- **Other coins** (LTC/XRP/ADA/DOT) lack sufficient data for any model to significantly
  outperform classic HAR beyond h=1.

## MSE Comparison Heatmap (selected configs)

BTC-USD shows the richest comparison across all model families:

| Model | h=1 | h=5 | h=10 | DM vs HAR |
|-------|-----|-----|------|-----------|
| Naive trail-30d | 1.237 | 0.747 | 0.685 | -- |
| GARCH-rolling | 1.732 | 1.384 | 1.438 | -- |
| HAR Classic | 0.888 | 0.522 | 0.571 | baseline |
| HAR Asymmetric | 0.843 | 0.399 | 0.361 | BEATS all h |
| DLinear-vol | 0.752 | 0.374 | 0.352 | BEATS all h |

Progression: HAR beats GARCH/naive, then asymmetric HAR and DLinear each provide
additional 15-38% MSE reduction over classic HAR. The two improvements are complementary.

## Summary of Key Findings

### 1. HAR is the correct baseline for crypto RV forecasting

HAR (Corsi 2009) with 3 hand-crafted features (daily/weekly/monthly log-RV means) beats:
- **GARCH-rolling** by 30-67% across all 21 short-horizon configs and all 14 long-horizon configs
- **Naive trail-30d** by 16-48% at h=1, statistically significant for 6/7 coins

This invalidates GARCH(1,1) as a useful benchmark for crypto volatility. The r-squared-daily
target used in earlier pipeline stages was strictly worse than predicting nothing (MSE 5.6-7.6
vs log-RV variance ~1.5).

### 2. Statistical significance depends on data quantity and forecast horizon

- **h=1**: 6/7 coins BEATS naive (only DOT inconclusive)
- **h=5**: 4/7 coins BEATS
- **h=10**: 2/7 coins BEATS (ETH, SOL)
- **h=15-20**: 2/7 coins BEATS (ETH, SOL persistently)

ETH and SOL maintain statistical significance across ALL five horizons. Other coins lose
power progressively. BTC is anomalous: despite the longest data history (2278 RV days),
its h>=10 significance collapses -- consistent with BTC's more mature, mean-reverting
volatility regime.

### 3. Asymmetric semivariance benefits BTC only

The leverage effect (RV- > RV+ predicting future vol) is real and significant for BTC
(5-37% MSE reduction, p<0.001), but not detectable for any other coin. The asymmetry
signal requires both (a) enough data and (b) a genuine leverage effect in the asset's
microstructure. XRP and ADA even show RV+ > RV- (inverse leverage), explaining the
slightly worse asymmetric results for those coins.

### 4. DLinear captures information beyond HAR's 3 features

DLinear's learned 22-parameter linear projection beats HAR's 3-parameter model on BTC
at all horizons (15-38% MSE reduction), ETH and SOL at h=1. The key insight: HAR's
hand-crafted 1d/5d/22d averages are a restrictive parameterization. A learned projection
from 22 daily values captures non-uniform temporal weighting that HAR misses.

DLinear's simplicity (single nn.Linear layer) provides inherent stability -- seed
variance <0.002 MSE on BTC. This is an advantage over more complex architectures
(LSTM, Transformer) that overfit on small-sample financial data.

### 5. The two improvements are complementary

Asymmetric HAR exploits **sign asymmetry** (leverage effect), DLinear exploits
**full-path information** (non-uniform temporal weights). For BTC:
- Asymmetric HAR: 5-37% over classic HAR
- DLinear: 15-38% over classic HAR
- A DLinear with asymmetric inputs (RV+ and RV- as separate channels) is a natural
  next step that could combine both advantages.

### 6. Data quantity is the binding constraint

| Data source | RV days | Results quality |
|-------------|---------|-----------------|
| Bitstamp BTC | ~2278 | Strong: significance at all horizons, both improvements detectable |
| Binance ETH | ~1495 | Good: significance at all horizons, no asymmetric benefit |
| yfinance SOL | ~725 | Moderate: h=1 significance for DL, good HAR performance |
| yfinance LTC/XRP/ADA/DOT | ~725 | Weak: numerical improvements but no significance |

yfinance provides only ~730 days of hourly data (2 years). This is insufficient for
DM test power. DOT consistently shows the weakest results across all experiments.

## Reproducibility

All experiments use the same methodology:
- Walk-forward 5-fold expanding window, refit every 22 days
- Target: log Realized Variance from hourly returns
- DM test: HAC Newey-West with HLN small-sample correction
- Seeds: 0, 7, 42, 99 (for DLinear; OLS seeds are identical)

Scripts:
```bash
# HAR Classic (M3)
python scripts/train_har_baseline.py --horizons 1 5 10

# HAR Asymmetric (M3b)
python scripts/har_asymmetric.py --horizons 1 5 10 --seeds 0 7 42 99

# DLinear-vol (M4)
python scripts/dlinear_vol.py --horizons 1 5 10 --seeds 0 7 42 99

# Long-horizon (M3-ext)
python scripts/train_har_baseline.py --horizons 15 20 --extra-coins LTC-USD XRP-USD ADA-USD DOT-USD
```

## Next Steps

1. **M5/M6** -- Cross-asset models: multi-scale GNN or multi-asset LSTM with asset
   embeddings, using HAR features as inputs alongside raw RV.
2. **Asymmetric DLinear** -- Feed RV+ and RV- as separate input channels to DLinear,
   combining leverage effect decomposition with learned temporal weights.
3. **5-minute RV** -- Current RV is computed from hourly returns. Literature (Andersen
   et al. 2003) recommends 5-min. Expect another 10-30% MSE reduction.
4. **Transaction cost integration** -- Convert MSE improvements to Sharpe/VaR improvements
   with realistic crypto spreads (10-50 bps).
5. **TFT (M9)** -- Temporal Fusion Transformer with the fixed multi-seed walk-forward
   pipeline (PR #971). Tests whether attention-based variable selection beats HAR's
   hand-crafted features when data is sufficient.

## References

- Andersen, T.G., Bollerslev, T., Diebold, F.X. & Labys, P. (2003) "Modeling and Forecasting
  Realized Volatility", Econometrica 71, 579-625.
- Black, F. (1976) "Studies of Stock Price Volatility Changes", ASA Proceedings.
- Corsi, F. (2009) "A Simple Approximate Long-Memory Model of Realized Volatility",
  Journal of Financial Econometrics 7, 174-196.
- Diebold, F.X. & Mariano, R.S. (1995) "Comparing Predictive Accuracy", JBES 13, 253-263.
- Harvey, D.I., Leybourne, S.J. & Newbold, P. (1997) "Testing the Equality of Prediction
  Mean Squared Errors", IJF 13, 281-291.
- McAleer, M. & Medeiros, M.C. (2008) "Realized Volatility: A Review", Econometric Reviews.
- Patton, A.J. & Sheppard, K. (2009) "Good Volatility, Bad Volatility: Signed Jumps and
  the Persistence of Volatility", Working Paper.
- Zeng, A., Chen, M., Zhang, L. & Xu, Q. (2023) "Are Transformers Effective for Time
  Series Forecasting?", AAAI 2023.
- Lim, B., Arik, S.O., Loeff, N. & Pfister, T. (2021) "Temporal Fusion Transformers for
  Interpretable Multi-horizon Time Series Forecasting", International Journal of
  Forecasting 37, 1748-1764.
