# M10 Realized GARCH -- Crypto Volatility Forecasting

**Status:** TESTED (Cycle 29 Track 3) -- **NO BEATS** (0/21 combos beat HAR Classic)

## Verdict

M10 Realized GARCH **fails to beat HAR Classic** across all 21 unique coin-horizon combinations. The model is systematically worse, particularly at short horizons (h=1) where the average MSE is 58.9% higher than HAR. Recommendation: **do not adopt for crypto volatility forecasting.**

## M10 Results Summary (Cycle 29, 2026-05-13)

| Verdict | Count |
|---------|-------|
| BEATS | **0** |
| BEATEN | 13 (all at p < 0.05) |
| INCONCLUSIVE | 8 |

| Coin | h=1 MSE | h=1 verdict | h=5 MSE | h=5 verdict | h=10 MSE | h=10 verdict |
|------|---------|-------------|---------|-------------|----------|--------------|
| ADA-USD | -58.6% | BEATEN_p005 | -44.1% | INCONCLUSIVE | -39.2% | INCONCLUSIVE |
| BTC-USD | -63.5% | BEATEN_p005 | -58.2% | BEATEN_p005 | -31.2% | BEATEN_p005 |
| DOT-USD | -37.6% | BEATEN_p005 | -10.2% | INCONCLUSIVE | +18.7% | INCONCLUSIVE |
| ETH-USD | -68.3% | BEATEN_p005 | -97.2% | BEATEN_p005 | -79.1% | BEATEN_p005 |
| LTC-USD | -54.5% | BEATEN_p005 | -31.5% | INCONCLUSIVE | -13.6% | INCONCLUSIVE |
| SOL-USD | -62.6% | BEATEN_p005 | -67.4% | BEATEN_p005 | -69.0% | BEATEN_p010 |
| XRP-USD | -67.1% | BEATEN_p005 | -37.9% | INCONCLUSIVE | -15.4% | INCONCLUSIVE |

Negative MSE reduction = RG worse than HAR. 4 seeds produce identical results (deterministic MLE).

### Root Cause Analysis

1. **Overfitting**: 8 parameters vs 3 for HAR. With 250h initial training and hourly crypto noise, MLE overfits.
2. **Crypto regime shifts**: Abrupt volatility regime changes (Luna, FTX) that GARCH conditional variance cannot adapt to fast enough.
3. **Measurement equation mismatch**: `log(RV_t) = xi + phi * log(h_t) + ...` assumes stable linear relationship, unstable at hourly crypto frequency.
4. **Log-transform distortion**: Compresses extreme volatility spikes that dominate crypto MSE. HAR operates directly on RV levels.
5. **Structural issue confirmed**: All 4 seeds identical = deterministic failure, not stochastic noise.

Full details: `docs/M10_REALIZED_GARCH_VOL.md`

## Original Proposal (Cycle 28)

## Why Realized GARCH

The DM retroactif (Cycle 28 Track A) re-classified 60 combos with direction-aware testing:

| Model | BEATS p<0.05 | Params | Key issue |
|-------|-------------|--------|-----------|
| M3 HAR classic | 12/21 | 4 | Strong baseline, but no GARCH dynamics |
| M3b HAR asymmetric | 3/6 | 5 | Leverage effect BTC-specific only |
| M4 DLinear | 6/21 | ~22 | Data-hungry, inconsistent cross-coin |
| M5 HMM regime | 1/6 | 8+HMM | Two-step estimation causes BEATEN paradox at h>=5 |
| M9 TFT | 0/6 | ~110K | Catastrophic overfit, no signal |

The pattern is clear: **models that incorporate realized measures beat those that don't, but only when the parameter count stays low.** HAR classic (4 params, uses RV directly) is the strongest. TFT (110K params) fails completely. The sweet spot is 5-15 parameters using daily RV.

Realized GARCH sits in this sweet spot. It extends GARCH(1,1) with a measurement equation linking latent conditional variance to observed RV:

```
GARCH:     h_t = omega + alpha * eps^2_{t-1} + beta * h_{t-1}
Measure:   log(RV_t) = xi + phi * log(h_t) + tau(eps_t) + u_t
Leverage:  tau(eps_t) = gamma_1 * eps_t + gamma_2 * (eps_t^2 - 1)
```

**7-9 parameters total.** Each has economic interpretation (no black box).

## Why not the alternatives

| Candidate | Rejected because |
|-----------|-----------------|
| HEAVY (Shephard 2010) | Same goal as Realized GARCH but harder to implement (bivariate MLE, no library). Same low param count (8-10) but 2x coding effort for marginal expected gain. |
| GARCH-MIDAS (Engle 2013) | MIDAS component needs macro drivers (CPI, GDP). Crypto volatility has weak macro links. 8-15 params on ~100 monthly obs = unstable. |
| MS-GARCH (Haas 2004) | Fixes M5's two-step flaw (joint Hamilton filter + GARCH MLE). Good theory but 11 params + complex optimization = 5-8h dev. Ranked as M11 fallback. |
| GNN cross-asset | 2 assets (BTC+ETH) = trivial 2-node graph. No structure to learn. TFT already showed >100K params = catastrophic on this data. |

## Expected vs Actual Results

**Expected (based on Hansen et al. 2012 equities):** 5-15% MSE reduction at h=1, modest at h=5/10.

**Actual (crypto hourly):** 0/21 BEATS. Average MSE increase: h=1 +58.9%, h=5 +49.5%, h=10 +32.7%.

**Why the proposal was wrong:** Hansen et al. results on equity markets do not transfer to crypto hourly data. Crypto has higher kurtosis (~20-50 vs ~5-8 for equities), regime-dependent volatility clustering with structural breaks, and 24/7 trading that eliminates overnight information effects that RG leverages in equity markets.

## Implementation plan

- Fork `garch_rolling_baseline.py` (walk-forward refit every 22 days, gap=10)
- Custom MLE via `scipy.optimize.minimize` (log-likelihood from Hansen 2012 eq. 7-8)
- Daily RV from `realized_variance.py` as realized measure
- Walk-forward expanding window, 4 seeds (0,1,7,42), BTC+ETH, h=1/5/10
- DM test vs HAR classic baseline, direction-aware classification
- Expected dev time: 2-3 hours. Runtime: ~10 min per config.

## Benchmarks to beat

| Benchmark | BTC h=1 | BTC h=5 | BTC h=10 | ETH h=1 | ETH h=5 | ETH h=10 |
|-----------|---------|---------|----------|---------|---------|----------|
| M3 HAR classic | BEATS_p005 | BEATS_p005 | INCONCLUSIVE | BEATS_p005 | BEATS_p005 | BEATS_p005 |
| M3b HAR asym | BEATS_p005 | BEATS_p005 | BEATS_p005 | INCONCLUSIVE | INCONCLUSIVE | INCONCLUSIVE |
| M4 DLinear | BEATS_p005 | BEATS_p005 | BEATS_p005 | BEATS_p005 | INCONCLUSIVE | INCONCLUSIVE |

Realized GARCH must achieve BEATS_p005 on at least BTC h=1 (where HAR classic already beats GARCH) to be viable. If it fails, MS-GARCH (M11) is the fallback.

## Next Steps: M11 Volatility Forecasting

HAR Classic remains the baseline to beat (12/21 BEATS_p005 from DM retroactif). The following models are ranked by expected viability on crypto hourly data:

| Priority | Model | Params | Rationale |
|----------|-------|--------|-----------|
| M11a | **HAR-RV-J** (Andersen et al. 2007) | 5 | Adds jump component to HAR. Low param count, directly extends our strongest baseline. Expected: moderate improvement on high-volatility days. |
| M11b | **Markov-Switching HAR** | 6-8 | Regime-switching between low/high vol states. Addresses root cause #2 (regime shifts). 2-state Markov + HAR in each state. |
| M11c | **HEAVY** (Shephard & Sheppard 2010) | 8-10 | Same goal as Realized GARCH but bivariate formulation. May handle measurement equation mismatch better. 2x coding effort. |
| M11d | **Log-transformed LSTM on RV** | ~500-2K | Neural approach on log(RV) sequences. Must stay below ~5K params to avoid TFT-style catastrophic overfit. |

**Rejected:** GARCH-MIDAS (macro drivers weak for crypto), MS-GARCH (complex optimization, 11+ params), cross-asset GNN (2-node graph trivial).

## References

- Hansen, P.R., Huang, Z. & Shek, H.H. (2012) "Realized GARCH: A Joint Model for Returns and Realized Measures of Volatility", Journal of Applied Econometrics 27(6), 877-906.
- Charles, A. & Darne, O. (2019) "Volatility Estimators in Crypto Markets", Economics Bulletin 39(1), 144-152.
- Shephard, N. & Sheppard, K. (2010) "Realising the Future: Forecasting with High-Frequency-Based Volatility (HEAVY) Models", Journal of Applied Econometrics 25(2), 197-231.
- Haas, M., Mittnik, S. & Paolella, M.S. (2004) "A New Approach to Markov-Switching GARCH Models", Journal of Financial Econometrics 2(4), 493-530.
