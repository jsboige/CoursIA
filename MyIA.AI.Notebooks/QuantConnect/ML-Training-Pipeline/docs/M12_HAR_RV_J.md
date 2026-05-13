# M12 HAR-RV-J -- Andersen-Bollerslev-Diebold (2007) Jump Decomposition

**Status:** BEATS (Cycle 31) -- p=7.9e-7, win_rate=76.2%, but MSE degradation and h=5 weakness

## Verdict

M12 HAR-RV-J **BEATS** HAR Classic on Sharpe via Kelly position sizing (sign-test p=7.9e-7, 64/84 combos). However, the edge is nuanced:

1. **MSE is consistently WORSE** for HAR-RV-J: median MSE increase of +8.1% (h=1), +38.0% (h=5), +58.7% (h=10). The model produces less accurate volatility forecasts than HAR Classic.
2. **h=5 is a dead zone**: only 12/28 combos (42.9%) beat HAR at h=5 -- actually below 50%. The overall BEATS verdict is carried by h=1 (24/28, 85.7%) and h=10 (28/28, 100%).
3. **Magnitude is small**: median delta-Sharpe +0.0032 across all combos. For context, M11 HAR+Kelly vs buy-hold had delta-Sharpe +0.313 at 5bps.
4. **MSE-Sharpe disconnect**: Jump decomposition helps Kelly allocate better but hurts raw forecast accuracy. The jump signal adds value for position sizing, not for point forecasting.

**Recommendation**: Adopt HAR-RV-J as an alternative to HAR Classic for Kelly-based strategies at h=1 and h=10 horizons. Do NOT use for h=5 or for applications requiring raw MSE accuracy.

## Results Summary (Cycle 31, 2026-05-13)

| Metric | Value |
|--------|-------|
| Verdict | BEATS |
| Sign-test p-value | 7.9e-7 |
| Win rate | 64/84 (76.2%) |
| Median delta-Sharpe | +0.0032 |
| Combos | 84 (7 coins x 3 horizons x 4 seeds) |
| Runtime | 431s |

### Per-Horizon Breakdown

| Horizon | Beats | Win% | Med delta-Sharpe | Med MSE change |
|---------|-------|------|-------------------|----------------|
| h=1 | 24/28 | 85.7% | +0.0017 | +8.1% (worse) |
| h=5 | 12/28 | 42.9% | -0.0076 | +38.0% (worse) |
| h=10 | 28/28 | 100% | +0.0060 | +58.7% (worse) |

h=5 is the weak spot. HAR-RV-J actively hurts at h=5 for 5/7 coins.

### Per-Coin Breakdown

| Coin | Beats | Win% | p-value | Med delta-Sharpe | Med MSE change |
|------|-------|------|---------|-------------------|----------------|
| BTC-USD | 12/12 | 100% | 0.0002 | +0.0032 | +5.2% |
| ETH-USD | 8/12 | 66.7% | 0.194 | +0.0076 | +7.0% |
| SOL-USD | 8/12 | 66.7% | 0.194 | +0.0295 | +38.0% |
| LTC-USD | 12/12 | 100% | 0.0002 | +0.0060 | +174.7% |
| XRP-USD | 8/12 | 66.7% | 0.194 | +0.0019 | +0.2% |
| ADA-USD | 8/12 | 66.7% | 0.194 | +0.0964 | +69.7% |
| DOT-USD | 8/12 | 66.7% | 0.194 | +0.0017 | +110.7% |

Edge concentration: 7/7 coins have win_rate > 50%. BTC and LTC are 100% consistent. Other coins are borderline individually (p=0.194) but collectively strong.

### Per-Horizon Per-Coin Detail

| Coin | h=1 beats | h=1 dSharpe | h=5 beats | h=5 dSharpe | h=10 beats | h=10 dSharpe |
|------|-----------|-------------|-----------|-------------|------------|--------------|
| BTC-USD | 4/4 | +0.0005 | 4/4 | +0.0033 | 4/4 | +0.0032 |
| ETH-USD | 0/4 | -0.0093 | 4/4 | +0.0076 | 4/4 | +0.0153 |
| SOL-USD | 4/4 | +0.0295 | 0/4 | -0.0422 | 4/4 | +0.2238 |
| LTC-USD | 4/4 | +0.0009 | 4/4 | +0.0207 | 4/4 | +0.0060 |
| XRP-USD | 4/4 | +0.0249 | 0/4 | -0.0155 | 4/4 | +0.0019 |
| ADA-USD | 4/4 | +0.1282 | 0/4 | -0.0076 | 4/4 | +0.0964 |
| DOT-USD | 4/4 | +0.0017 | 0/4 | -0.0086 | 4/4 | +0.0023 |

h=5 failures: ETH (borderline at 4/4 beats but positive), SOL/XRP/ADA/DOT all 0/4 at h=5.

## Model

HAR-RV-J extends HAR Classic (3 regressors + intercept = 4 params) to 6 regressors + intercept = 7 params:

```
RV_t = BPV_t + J_t, where J_t = max(RV_t - mu * BPV_t, 0), mu = 0.6 (Huang-Tauchen)
log(RV_{t+h}) = b0 + b_d*log(RV_d) + b_w*log(RV_w) + b_m*log(RV_m) + b_dj*J_d + b_wj*J_w + b_mj*J_m
```

- RV regressors: log-transformed daily, weekly (5d), monthly (22d) averages
- Jump regressors: raw (not log) daily, weekly, monthly averages
- OLS estimation, walk-forward 5-fold expanding window, refit every 22 days

## Setup

- 7 coins: BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD
- 3 horizons: h=1, 5, 10
- 4 seeds: 0, 1, 7, 42
- Kelly cap=1.0 (M11i confirmed cap=3.0 killed by Calmar/DD)
- Fee=50bps, mu_window=60d
- BPV from `realized_variance.py` (already implemented)
- Walk-forward 5-fold, refit_every=22

## Why MSE Gets Worse But Sharpe Gets Better

The jump component captures a second signal orthogonal to the HAR RV components. This extra signal:

1. **Degrades MSE**: Jumps are noisy at crypto hourly frequency. The OLS coefficients on jump terms absorb noise, increasing forecast variance.
2. **Improves Kelly**: The jump signal captures tail-risk information that helps Kelly size positions. When jump component is high, Kelly correctly reduces exposure (or increases it if jump signal is favorable for forecast direction).

This MSE-Sharpe disconnect is the key finding. It suggests that for trading applications, jump decomposition adds value even when it degrades point-forecast accuracy.

## Caveats (G.2 Honesty)

1. **MSE degradation is real**: +8.1% to +58.7% across horizons. HAR-RV-J is a WORSE volatility forecaster than HAR Classic by standard metrics.
2. **h=5 is dead**: 42.9% win rate. The jump signal is uninformative at intermediate horizons for crypto.
3. **Small magnitude**: delta-Sharpe +0.0032 is statistically significant but economically small.
4. **BTC/LTC dominate**: Only BTC (12/12) and LTC (12/12) are individually significant. Other coins are borderline.
5. **MSE-Sharpe disconnect needs explanation**: The model helps Kelly but hurts forecasts. If the Sharpe edge is coming from Kelly exploiting a spurious signal, it may not generalize OOS.

## Comparison with Prior Models

| Model | Params | BEATS HAR | Key finding |
|-------|--------|-----------|-------------|
| M3 HAR classic | 4 | baseline | Strong baseline, 12/21 DM BEATS |
| M3b HAR asymmetric | 5 | mixed | BTC-specific leverage only |
| M4 DLinear | ~22 | 6/21 | Data-hungry, inconsistent |
| M5 HMM regime | 8+HMM | 1/6 | Two-step estimation flaw |
| M9 TFT | ~110K | 0/6 | Catastrophic overfit |
| M10 Realized GARCH | 7-9 | 0/21 | NO BEATS (MSE +59%) |
| M11 HAR Kelly cap=1.0 | 4 | BEATS BH @50bps | Calmar +0.44, DD 62.5% |
| **M12 HAR-RV-J** | **7** | **64/84 (76%)** | **BEATS but MSE worse** |

M12 is the first model since M11 to beat HAR Classic on Sharpe. M10 (Realized GARCH) failed completely. M12 succeeds where M10 failed because it stays in the HAR framework (OLS, not MLE) and only adds jump regressors rather than replacing the whole model.

## Files

- `scripts/m12_har_rv_j.py`: Main sweep script
- `scripts/m12_per_coin_attribution.py`: Per-coin attribution
- `results/m12_har_rv_j/results.json`: Full results (84 combos)
- `results/m12_har_rv_j/m12_har_rv_j_results.csv`: CSV export
- `results/m12_har_rv_j/m12_per_coin_attribution.csv`: Per-coin breakdown
- `results/m12_har_rv_j/m12_per_coin_results.json`: Per-coin JSON

## Reference

Andersen, T.G., Bollerslev, T. & Diebold, F.X. (2007) "Roughing It Up: Including Jump Components in the Measurement, Modeling, and Forecasting of Return Volatility", Review of Economics and Statistics 89(4):701-720.
