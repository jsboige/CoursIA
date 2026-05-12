# M10 Proposal -- Realized GARCH for Crypto Volatility Forecasting

**Status:** PROPOSED (Cycle 28 Track B)

## Recommendation

**Realized GARCH (Hansen, Huang, Shek 2012)** as M10, with Markov-Switching GARCH as fallback M11.

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

## Expected results

Based on Hansen et al. (2012) equities + Charles & Darne (2019) crypto:

- **h=1:** 5-15% MSE reduction vs HAR classic. Realized measure + GARCH dynamics should improve on HAR's linear lag structure.
- **h=5/10:** Modest or no improvement. GARCH dynamics dominate at longer horizons, converging to unconditional variance (same as HAR).
- **BTC vs ETH:** BTC should benefit more (more data, stronger GARCH persistence). ETH ~1500 obs may be tight for MLE convergence.

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

## References

- Hansen, P.R., Huang, Z. & Shek, H.H. (2012) "Realized GARCH: A Joint Model for Returns and Realized Measures of Volatility", Journal of Applied Econometrics 27(6), 877-906.
- Charles, A. & Darne, O. (2019) "Volatility Estimators in Crypto Markets", Economics Bulletin 39(1), 144-152.
- Shephard, N. & Sheppard, K. (2010) "Realising the Future: Forecasting with High-Frequency-Based Volatility (HEAVY) Models", Journal of Applied Econometrics 25(2), 197-231.
- Haas, M., Mittnik, S. & Paolella, M.S. (2004) "A New Approach to Markov-Switching GARCH Models", Journal of Financial Econometrics 2(4), 493-530.
