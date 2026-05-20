# M14 HEAVY -- Shephard & Sheppard (2010) Bivariate Volatility Model

**Status:** NO BEATS (Cycle 33) -- 48/84 (57.1%, p=0.1149)

## Verdict

M14 HEAVY **fails to beat HAR Classic** Kelly. Win rate 57.1% (above 50% but below significance), p=0.1149 (not significant at 0.05). Median delta-Sharpe +0.0187. MSE catastrophically worse (+111.3% median).

**Recommendation**: Do not adopt HEAVY for crypto volatility forecasting. The bivariate formulation does not overcome the measurement equation mismatch that also doomed M10 Realized GARCH. Pivot to M15 LSTM.

## Results Summary (Cycle 33, 2026-05-13)

| Metric | Value |
|--------|-------|
| Verdict | NO BEATS |
| Sign-test p-value | 0.1149 |
| Win rate (HEAVY > HAR) | 48/84 (57.1%) |
| Median delta-Sharpe | +0.0187 |
| Median MSE change | +111.3% |
| Combos | 84 (7 coins x 3 horizons x 4 seeds) |
| Runtime | 672s |

### Per-Coin Summary

| Coin | Win% | Med delta-Sharpe | Med MSE change |
|------|------|-------------------|----------------|
| BTC-USD | 8/12 (66.7%) | +0.0020 | +175.8% |
| ETH-USD | 0/12 (0%) | -0.1517 | +285.5% |
| SOL-USD | 4/12 (33.3%) | -0.0199 | +95.5% |
| LTC-USD | 8/12 (66.7%) | +0.0644 | +122.5% |
| XRP-USD | 8/12 (66.7%) | +0.0187 | +147.1% |
| ADA-USD | 12/12 (100%) | +0.4754 | +135.4% |
| DOT-USD | 8/12 (66.7%) | +0.0233 | +46.4% |

ETH is a complete failure (0/12, delta-Sharpe -0.15). ADA is the only coin with 100% win rate, but MSE is +135.4%.

### Per-Horizon Summary

| Horizon | Win% | Med delta-Sharpe |
|---------|------|-------------------|
| h=1 | 4/28 (14.3%) | -0.0214 |
| h=5 | 24/28 (85.7%) | +0.0493 |
| h=10 | 20/28 (71.4%) | +0.0406 |

h=1 is strongly negative (14.3%), consistent with M10 Realized GARCH's failure at short horizons. h=5 shows the highest win rate (85.7%) but does not reach significance because ETH drags the overall test down.

## Model

HEAVY (High-frEquency-bAsed VolatilitY) -- Shephard & Sheppard (2010):
```
HEAVY-r (returns equation):
    r_t^2 = omega_r + alpha_r * r_{t-1}^2 + beta_r * RV_{t-1}

HEAVY-RV (realized measure equation):
    RV_t = omega_RV + alpha_RV * RM_{t-1} + beta_RV * RV_{t-1}

where RM_{t-1} = realized measure (daily RV from intraday returns)
```

6 parameters: omega_r, alpha_r, beta_r, omega_RV, alpha_RV, beta_RV.
Estimated jointly via QML (Gaussian quasi-likelihood on both equations).
scipy.optimize.minimize with L-BFGS-B, multi-start (5 attempts).

Forecast for horizon h: iterative AR(1) on RV equation:
```
E[RV_{t+h}] = omega_RV + phi * E[RV_{t+h-1}]
where phi = alpha_RV + beta_RV
```

## Setup

- 7 coins: BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD
- 3 horizons: h=1, 5, 10
- 4 seeds: 0, 1, 7, 42
- Total: 84 combos
- Comparison: HEAVY Kelly vs HAR Classic Kelly (sign-test on paired Sharpe)
- Data: yfinance hourly (2024-05-14 to 2026-05-13)
- Walk-forward 5-fold expanding, refit every 22 days
- Kelly cap=1.0, fee=50bps, mu_window=60d

## Why HEAVY Fails

1. **Same measurement mismatch as M10 Realized GARCH**: The HEAVY-RV equation assumes RV_t follows a stable AR(1)-like process driven by lagged RV. Crypto hourly RV has extreme kurtosis and regime-dependent dynamics that violate this stationarity assumption.

2. **MSE blowup across the board**: Median MSE +111.3% vs HAR. The bivariate formulation doubles the parameter count (6 vs 3 for HAR) but introduces more estimation noise on rolling windows of ~200-400 daily observations.

3. **ETH structural failure**: ETH 0/12 with delta-Sharpe -0.1517 suggests the model's conditional variance dynamics are particularly mismatched with ETH's volatility process (possibly due to ETH's higher correlation with DeFi/news events).

4. **h=1 catastrophic**: 4/28 (14.3%) at h=1 mirrors M10 Realized GARCH's failure. Short-horizon crypto volatility is dominated by jump dynamics that neither GARCH-type nor HEAVY models capture.

5. **Deterministic across seeds**: All 4 seeds produce identical results (deterministic QML MLE), confirming this is a structural failure, not stochastic noise.

6. **h=5/h=10 wins are misleading**: Win rates at h=5 (85.7%) and h=10 (71.4%) look promising but come with MSE +46-176%. The Kelly framework converts noisier forecasts into position sizing "edge" that is unlikely to survive out-of-sample.

## Caveats (G.2 Honesty)

1. **QML estimation only**: Maximum likelihood with Gaussian quasi-likelihood. Non-Gaussian innovations (heavy tails in crypto) may bias parameter estimates.

2. **Single model specification**: Only tested the basic HEAVY(1,1) specification. Adding leverage terms or asymmetric effects could improve results, but M10 Realized GARCH already showed leverage doesn't help in crypto.

3. **ADA 100% wins suspect**: ADA shows 100% win rate with delta-Sharpe +0.475 but MSE +135.4%. This mirrors the M13 MS-HAR pattern where altcoin "wins" come from Kelly amplification of noisy forecasts, not better volatility prediction.

4. **h=5/h=10 p=0.1149**: Close to significance but not below 0.05. Even if borderline significant, the MSE cost (+111%) makes adoption unjustifiable.

5. **4 seeds identical**: No cross-seed variance means we cannot assess estimation stability. The QML solution is unique per data window.

## Comparison with Prior Models

| Model | Params | BEATS | Key finding |
|-------|--------|-------|-------------|
| M11 HAR Kelly (cap=1.0) | 4 | BEATS BH @50bps | Sharpe +0.313 vs buy-hold |
| M12 HAR-RV-J | 7 | BEATS (p=7.9e-7) | Jump-augmented RV |
| M11j Multi-Asset Kelly | ~10 | 0/36 vs single BTC | NO BEATS (delta=-1.05) |
| M13 MS-HAR | 11 | 39/84 (46.4%, p=0.7774) | NO BEATS, MSE +995% |
| M14 HEAVY | 6 | 48/84 (57.1%, p=0.1149) | NO BEATS, MSE +111% |

HEAVY improves over MS-HAR (57.1% vs 46.4%) but still fails significance. Both bivariate (HEAVY) and regime-switching (MS-HAR) approaches fail against simple HAR.

## Files

- `scripts/m14_heavy.py`: Main sweep script
- `results/m14_heavy/results.json`: Full results (84 combos)
- `results/m14_heavy/m14_heavy_results.csv`: CSV export

## Reference

Shephard, N. & Sheppard, K. (2010) "Realising the Future: Forecasting with High-Frequency-Based Volatility (HEAVY) Models", Journal of Applied Econometrics 25(2), 197-231.
