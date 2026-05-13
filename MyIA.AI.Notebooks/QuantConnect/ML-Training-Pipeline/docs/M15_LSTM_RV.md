# M15: Log-LSTM RV

**Model:** LSTM (Hochreiter & Schmidhuber 1997) applied to log-realized variance.
**Date:** 2026-05-13
**Script:** `scripts/m15_lstm_rv.py`

## Architecture

```
Input:  sliding window W=22 days x 3 features [log(RV), returns, sign(returns)]
Model:  LSTM(hidden=H, 1 layer) + FC(H, 1)
Target: log(RV_{t+h}), h in {1, 5, 10}
Loss:   MSE on log-RV
Decode: exp(pred) -> RV level, then log(RV) for Kelly comparison
```

Two capacities tested:
- **hidden=64**: ~17,729 params
- **hidden=32**: ~4,733 params (in progress)

## Methodology

- Walk-forward 5-fold expanding window, refit every 22 days
- Early stopping (patience=10, max epochs=100)
- Expanding normalization (mean/std from training fold only)
- 7 coins (BTC, ETH, SOL, LTC, XRP, ADA, DOT) x 3 horizons (h=1,5,10) x 4 seeds (0,1,7,42) = 84 combos
- Kelly cap=1.0, fee=50bps, mu_window=60
- Sign-test: binomial one-sided, BEATS if p<0.05 AND win_rate >= 60%

## Results: hidden=64 (~17.7K params)

**VERDICT: NO BEATS** (45/84, p=0.2928, win_rate=53.6%)

| Metric | Value |
|--------|-------|
| LSTM beats HAR | 45/84 (53.6%) |
| p-value (sign-test) | 0.2928 |
| Median delta-Sharpe (LSTM - HAR) | +0.0029 |
| Median MSE change | +7.8% (LSTM worse) |

### Per-coin results (hidden=64)

| Coin | Median delta-Sharpe | MSE change | Beats |
|------|-------------------|------------|-------|
| BTC-USD | +0.0069 | -13.1% | 9/12 |
| ETH-USD | -0.0293 | +8.8% | 4/12 |
| SOL-USD | -0.0190 | +8.6% | 4/12 |
| LTC-USD | -0.0142 | +12.3% | 2/12 |
| XRP-USD | +0.0026 | +12.0% | 6/12 |
| ADA-USD | +0.0687 | +7.7% | 8/12 |
| DOT-USD | +0.0247 | +4.6% | 12/12 |

### Per-horizon results (hidden=64)

| Horizon | Median delta-Sharpe | Beats |
|---------|-------------------|-------|
| h=1 | -0.0031 | 13/28 |
| h=5 | +0.0040 | 16/28 |
| h=10 | +0.0075 | 16/28 |

### Notable observations

1. **BTC-USD**: Only coin with meaningful MSE reduction (-13.1%) and strong beat rate (9/12). LSTM captures BTC volatility structure better than HAR.
2. **DOT-USD**: Perfect beat rate (12/12) but modest delta-Sharpe (+0.0247) and MSE actually worse (+4.6%).
3. **Longer horizons (h=5, h=10)**: LSTM performs relatively better than at h=1, suggesting the sequential model captures multi-step dynamics that HAR's fixed lag structure misses.
4. **Overfitting signal**: 17.7K params on ~1825 daily obs with expanding window. Median MSE +7.8% suggests the LSTM overfits on most coins. BTC is the exception where data is more abundant and volatility structure more persistent.

## Comparison with M-series

| Model | Verdict | Win rate | p-value | Notes |
|-------|---------|----------|---------|-------|
| M2 HAR Classic | **Baseline** | -- | -- | Sharpe +0.313 vs BH |
| M10 Realized GARCH | NO BEATS | -- | -- | MSE +62% |
| M12 HAR-RV-J | **BEATS** | -- | p=7.9e-7 | Jump-augmented |
| M13 MS-HAR | NO BEATS | 39/84 | p=0.7774 | Markov-Switching |
| M14 HEAVY | NO BEATS | 48/84 | p=0.1149 | Bivariate |
| **M15 LSTM h=64** | **NO BEATS** | **45/84** | **p=0.2928** | Neural, overfitting risk |
| M15 LSTM h=32 | *In progress* | -- | -- | ~4.7K params |

## Conclusion

LSTM hidden=64 does NOT beat HAR Classic for crypto volatility forecasting across the full 7-coin panel. The model shows promise on BTC (MSE -13%) and DOT (12/12 beats) but overfits on most other coins (median MSE +7.8%). The hidden=32 variant will test whether a smaller model avoids this overfitting.

Runtime: ~4.8 hours (17206s) for 84 combos on RTX 3070 Laptop GPU.
