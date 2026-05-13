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

## M12 HAR-RV-J — Andersen-Bollerslev-Diebold (2007) Jump Decomposition

**Status:** BEATS (Cycle 31) -- p=7.9e-7, 64/84 (76.2%), med delta-Sharpe +0.0032

### Verdict

M12 HAR-RV-J BEATS HAR Classic on Sharpe (p=7.9e-7, 76.2% win rate). However:
1. **MSE is consistently WORSE**: +8.1% (h=1), +38.0% (h=5), +58.7% (h=10)
2. **h=5 is dead**: 12/28 (42.9%) win rate, actually below 50%
3. **Edge at h=1 and h=10 only**: 24/28 (85.7%) and 28/28 (100%)
4. **Magnitude small**: delta-Sharpe +0.0032 (vs M11 delta-Sharpe +0.313 vs buy-hold)

The MSE-Sharpe disconnect is the key finding: jump decomposition helps Kelly position sizing but hurts raw forecast accuracy.

### Model
HAR-RV-J extends HAR Classic (3 regressors) to 6 regressors by decomposing RV into continuous (BPV) and jump components:

- RV_t = BPV_t + J_t, where J_t = max(RV_t - mu * BPV_t, 0), mu = 0.6 (Huang-Tauchen)
- Regression: log(RV_{t+h}) = b0 + b_d*log(RV_d) + b_w*log(RV_w) + b_m*log(RV_m) + b_dj*J_d + b_wj*J_w + b_mj*J_m

### Setup
- Walk-forward 5-fold expanding OLS, 7 coins x 3 horizons (h=1,5,10) x 4 seeds = 84 combos
- Kelly cap=1.0 (M11i confirmed cap=3.0 killed by Calmar)
- Fee=50bps, mu_window=60d
- Comparison: HAR-RV-J Sharpe vs HAR Classic Sharpe (same Kelly framework)

### Per-Coin Summary

| Coin | Win% | Med delta-Sharpe | Med MSE change |
|------|------|-------------------|----------------|
| BTC-USD | 100% (12/12) | +0.0032 | +5.2% |
| ETH-USD | 66.7% (8/12) | +0.0076 | +7.0% |
| SOL-USD | 66.7% (8/12) | +0.0295 | +38.0% |
| LTC-USD | 100% (12/12) | +0.0060 | +174.7% |
| XRP-USD | 66.7% (8/12) | +0.0019 | +0.2% |
| ADA-USD | 66.7% (8/12) | +0.0964 | +69.7% |
| DOT-USD | 66.7% (8/12) | +0.0017 | +110.7% |

Full details: `docs/M12_HAR_RV_J.md`

### Reference
Andersen, T.G., Bollerslev, T. & Diebold, F.X. (2007) "Roughing It Up: Including Jump Components in the Measurement, Modeling, and Forecasting of Return Volatility", Review of Economics and Statistics 89(4):701-720.

## M11 Results Summary

### M11a-c: Sharpe testing (M11c), DM significance (M11c)
- HAR Kelly mu=60d BEATS buy_hold at fee≤50bps (sign-test p=0.001-0.045)
- Edge dies at 100bps (p=0.155)
- Per-combo LW2008 p<0.05: 5/35 at 10bps, 0/35 at 100bps

### M11f: Transaction cost sweep
- Break-even frontier at ~50bps (p=0.045)
- Median delta-Sharpe: +0.313 at 5bps → +0.226 at 50bps → +0.044 at 100bps

### M11g: Fee-aware Kelly (no-trade band)
- NULL result. Threshold band does NOT shift break-even.
- Median delta-Sharpe unchanged ±0.005 across all threshold × fee cells.

### M11h: Kelly cap relaxed (cap=3.0)
- Cap=3.0 pushes break-even frontier from ~50bps to ~100bps (p=0.088)
- Median delta-Sharpe triples at 100bps: +0.044 → +0.087

### M11i: Max-DD analysis
- **NULL CONDITIONAL**: cap=3.0 Sharpe edge does NOT survive Calmar risk-adjustment.
- DD penalty 35/35 (p=0.000). DD increases 1.5× from cap=1.0 to cap=3.0.
- Calmar drops +0.44 → +0.19 at 100bps.
- Per-coin: MODERATE concentration (4/7 winners: BTC, XRP, ADA, DOT). ETH/SOL structurally hostile.

## Next Steps: Post-M12 Volatility Forecasting

M12 HAR-RV-J BEATS HAR Classic (p=7.9e-7) but with MSE degradation. M10 RG NO BEATS, M11i kills cap=3.0 leverage. Next: regime-switching (M13) or bivariate (M14).

| Priority | Model | Params | Status | Rationale |
|----------|-------|--------|--------|-----------|
| M12 | **HAR-RV-J** (Andersen et al. 2007) | 7 | BEATS (p=7.9e-7) | MSE worse but Sharpe better. h=5 dead zone. |
| M13 | **Markov-Switching HAR** | 6-8 | PROPOSED | Regime-switching between low/high vol states. Addresses crypto regime shifts. |
| M14 | **HEAVY** (Shephard & Sheppard 2010) | 8-10 | PROPOSED | Bivariate formulation. May handle measurement equation mismatch better. |
| M15 | **Log-transformed LSTM on RV** | ~500-2K | PROPOSED | Neural approach on log(RV) sequences. Must stay below ~5K params. |

**Rejected:** GARCH-MIDAS (macro drivers weak for crypto), MS-GARCH (complex optimization, 11+ params), cross-asset GNN (2-node graph trivial).

## Comparative Table (all models)

| Model | Params | Sharpe vs HAR | Calmar | Max-DD | Verdict |
|-------|--------|---------------|--------|--------|---------|
| M3 HAR classic | 4 | baseline | baseline | baseline | Strong baseline |
| M3b HAR asymmetric | 5 | mixed | - | - | BTC-specific leverage only |
| M4 DLinear | ~22 | 6/21 BEATS | - | - | Data-hungry, inconsistent |
| M5 HMM regime | 8+HMM | 1/6 BEATS | - | - | Two-step estimation flaw |
| M9 TFT | ~110K | 0/6 BEATS | - | - | Catastrophic overfit |
| M10 Realized GARCH | 7-9 | 0/21 BEATS | - | - | NO BEATS (MSE +59%) |
| M11 HAR Kelly (cap=1.0) | 4 | BEATS BH @50bps | +0.44 | 62.5% | Edge at fee≤50bps |
| M11 HAR Kelly (cap=3.0) | 4 | BEATS BH @100bps | +0.19 | 90.5% | NULL CONDITIONAL (Calmar kills) |
| M12 HAR-RV-J | 7 | 64/84 BEATS (p=7.9e-7) | - | - | BEATS but MSE worse, h=5 dead |

## References

- Hansen, P.R., Huang, Z. & Shek, H.H. (2012) "Realized GARCH: A Joint Model for Returns and Realized Measures of Volatility", Journal of Applied Econometrics 27(6), 877-906.
- Charles, A. & Darne, O. (2019) "Volatility Estimators in Crypto Markets", Economics Bulletin 39(1), 144-152.
- Shephard, N. & Sheppard, K. (2010) "Realising the Future: Forecasting with High-Frequency-Based Volatility (HEAVY) Models", Journal of Applied Econometrics 25(2), 197-231.
- Haas, M., Mittnik, S. & Paolella, M.S. (2004) "A New Approach to Markov-Switching GARCH Models", Journal of Financial Econometrics 2(4), 493-530.
