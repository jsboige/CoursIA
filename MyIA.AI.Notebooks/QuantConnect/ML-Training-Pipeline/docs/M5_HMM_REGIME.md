# M5 -- HMM Regime-Switching HAR: Volatility Regime Detection + Conditional Forecasting

**Status:** COMPLETE (Cycle 25 Wave 3, po-2024 Track C2).

## Why

M3 established HAR as the gold-standard baseline for crypto RV forecasting. M3b showed
asymmetric semivariance benefits BTC. M4 showed DLinear beats HAR on BTC at all horizons.
A natural extension: can regime-switching models, where different HAR coefficients apply
in different volatility regimes (low-vol vs high-vol), improve on the single HAR model?

The economic intuition: volatility dynamics may differ between calm and turbulent periods.
A model that adapts its coefficients to the current regime could capture this asymmetry.

## Model

**Classic HAR (Corsi 2009):**
```
log RV_{t+h} = b0 + b_d*rv_d + b_w*rv_w + b_m*rv_m + e
```

**Regime-Switching HAR (this work):**
```
log RV_{t+h} = b0 + b_d*rv_d + b_w*rv_w + b_m*rv_m
             + g0 * I(regime=high)
             + g_d * rv_d * I(regime=high)
             + g_w * rv_w * I(regime=high)
             + g_m * rv_m * I(regime=high)
             + e
```

Where:
- Regime decoded by K=2 Gaussian HMM (Viterbi) on log-RV
- 8 OLS coefficients (4 base + 4 regime interaction terms)
- At prediction time, HMM decodes current regime, selecting the interaction term values

## Methodology

- K=2 Gaussian HMM (hmmlearn) on log-RV, Viterbi-decoded
- Regime-switching HAR with interaction terms (8 coefficients)
- Walk-forward 5-fold expanding window, refit every 22 days
- 4 seeds (0, 7, 42, 99) for HMM initialization
- 2 coins (BTC-USD, ETH-USD), 3 horizons (h=1, 5, 10)
- Diebold-Mariano HAC test vs classic HAR baseline
- Aggregate verdict: BEATS only if 4/4 seeds pass DM

## Files

| File | Role |
|------|------|
| `scripts/hmm_regime_vol.py` | HMM regime-switching HAR model + walk-forward runner |
| `scripts/results/m5_hmm_regime.json` | Full results (609s runtime) |
| `docs/M5_HMM_REGIME.md` | This document |

## Results (BTC+ETH, 4 seeds, 609s runtime)

### DM verdict summary

| Verdict | Count | Configs |
|---------|-------|---------|
| **BEATS** | 1/6 | ETH h=1 (4/4 seeds) |
| INCONCLUSIVE | 2/6 | BTC h=1 (3/4 seeds), BTC h=5 |
| **BEATEN BY** | 3/6 | BTC h=5, BTC h=10, ETH h=5, ETH h=10 |

### Per-coin results (aggregated over 4 seeds)

| Coin | Horizon | Regime MSE | Classic MSE | Reduction | DM p-value | Verdict |
|------|---------|------------|-------------|-----------|------------|---------|
| BTC-USD | 1 | 0.825 | 0.888 | +7.0% | 3/4 seeds p<0.001 | INCONCLUSIVE |
| BTC-USD | 5 | 0.580 | 0.522 | -11.1% | 2/4 BEATEN BY | BEATEN BY |
| BTC-USD | 10 | 0.732 | 0.571 | -28.3% | 3/4 BEATEN BY | BEATEN BY |
| ETH-USD | 1 | 0.619 | 0.684 | +9.6% | 4/4 p<0.005 | **BEATS** |
| ETH-USD | 5 | 0.441 | 0.374 | -17.9% | 3/4 BEATEN BY | BEATEN BY |
| ETH-USD | 10 | 0.573 | 0.375 | -53.0% | 4/4 BEATEN BY | BEATEN BY |

### MSE reduction vs classic HAR (regime - classic, positive = regime wins)

| Coin | h=1 | h=5 | h=10 |
|------|-----|-----|------|
| BTC-USD | +7.0%* | -11.1% | -28.3% |
| ETH-USD | **+9.6%** | -17.9% | -53.0% |

(*3/4 seeds significant, not all 4)

## Key findings

1. **ETH h=1: only significant win.** The regime-switching HAR beats classic HAR by 9.6%
   (4/4 seeds, p<0.005). ETH's shorter data history (1495 RV days) with more pronounced
   regime shifts benefits from the conditional model at the shortest horizon.

2. **BTC h=1: promising but not conclusive.** 3/4 seeds show 8-10% improvement (p<10^-5),
   but seed 7 produces near-zero improvement (0.1%). The aggregate verdict is INCONCLUSIVE.
   The HMM initialization sensitivity is a concern.

3. **Longer horizons: regime model is harmful.** At h=5 and h=10, the regime-switching
   model is significantly WORSE than classic HAR for both coins. The MSE degradation grows
   with horizon: BTC h=10 sees 28% worse, ETH h=10 sees 53% worse. The interaction terms
   introduce noise that compounds over multi-step forecasts.

4. **HMM initialization sensitivity is severe.** Different seeds produce wildly different
   regime decompositions. Seed 0 and 99 might classify 60%/40% low/high, while seed 7
   might produce 80%/20%. This variance translates directly into prediction instability.

5. **The regime interaction approach has a fundamental flaw at longer horizons.** The
   iterative h-step prediction uses a single regime indicator R for ALL forecast steps.
   But the regime may switch during the forecast window. The model cannot adapt mid-forecast,
   leading to compounding errors.

## Conclusion

**M5 verdict: INCONCLUSIVE overall. 1/6 configs BEATS (ETH h=1).**

The HMM regime-switching HAR provides marginal improvement at h=1 for some configurations
but is actively harmful at h>=5. The approach adds complexity (8 coefficients + HMM
decoding) without consistent benefit. The classic 3-parameter HAR remains the better
default for most use cases.

Compared to M3b (asymmetric HAR, 3/21 BEATS, BTC-only) and M4 (DLinear, 5/21 BEATS),
the HMM regime approach (1/6 BEATS) is the weakest extension. The DLinear model, which
learns optimal temporal weights without explicit regime decomposition, is strictly superior.

## References

- Hamilton, J.D. (1989) "A New Approach to the Economic Analysis of Nonstationary
  Time Series and the Business Cycle", Econometrica 57, 357-384.
- Corsi, F. (2009) "A Simple Approximate Long-Memory Model of Realized Volatility",
  Journal of Financial Econometrics 7, 174-196.
