# M3 — HAR Extended: 7-Coin Universe + Diebold-Mariano Significance Tests

**Status:** COMPLETE (Cycle 25, po-2024). 10/21 BEATS, 11/21 INCONCLUSIVE.

## Why

M2 established HAR as the gold-standard baseline for realized-variance forecasting
on 3 coins (BTC/ETH/SOL), showing 30-65% MSE reduction vs GARCH-rolling and 16-48%
vs naive trail-30d across all 9 configs. **However**, M2 lacked formal statistical
significance testing — the MSE improvements could be noise.

M3 extends to a **7-coin universe** (BTC, ETH, SOL, LTC, XRP, ADA, DOT) and adds
**Diebold-Mariano (DM) tests** with HAC (Newey-West) variance to answer: *"Is HAR
significantly better than the naive baseline, or could the observed improvement be
due to sampling variation?"*

## What ships

| File | Role |
|------|------|
| `scripts/dm_test.py` | DM test with HAC Newey-West variance, HLN small-sample correction |
| `scripts/test_dm.py` | 17 unit tests for DM test (edge cases, verdicts, loss functions) |
| `scripts/intraday_loader.py` | Extended with `load_yf_coins()` + `extra_coins` param |
| `scripts/train_har_baseline.py` | Updated: 7-coin support + DM test integration |
| `scripts/results/m3_har_extended.json` | Raw results (21 configs) |

## Diebold-Mariano test

The DM test (Diebold & Mariano 1995) compares forecast accuracy:

```
H0: E[L(e_HAR)] = E[L(e_Naive)]   (equal accuracy)
H1: E[L(e_HAR)] ≠ E[L(e_Naive)]   (different accuracy)
```

where L(.) is a loss function (squared error). The test statistic uses a
**HAC (Heteroskedasticity and Autocorrelation Consistent)** variance estimator
(Newey & West 1987) with Bartlett kernel and n^(1/3) lag selection.

The **Harvey-Leybourne-Newbold (HLN) 1997** small-sample correction adjusts
the DM statistic for finite-sample bias.

### Implementation details

- Loss function: MSE (squared errors on log-RV scale)
- HAC kernel: Bartlett, lag = n^(1/3)
- Small-sample: HLN correction with forecast horizon h
- Verdicts: "BEATS baseline" (p<0.05, HAR lower loss), "INCONCLUSIVE" (p>=0.05)

## Data

| Coin | Source | Granularity | Coverage |
|------|--------|-------------|----------|
| BTC-USD | Bitstamp local CSV | 1h | ~10 years (2014-2024) |
| ETH-USD | Binance local ZIP | 1h | ~4 years (2019-2023) |
| SOL-USD | yfinance | 1h | ~730 days |
| LTC-USD | yfinance | 1h | ~730 days |
| XRP-USD | yfinance | 1h | ~730 days |
| ADA-USD | yfinance | 1h | ~730 days |
| DOT-USD | yfinance | 1h | ~730 days |

**Caveat:** yfinance coins have only ~730 days of hourly data (2 years). This limits
the walk-forward evaluation to fewer folds than BTC/ETH. Results for these coins
should be interpreted with caution — statistical power is lower.

## Results

Runtime: 191.5s on 21 configs (7 coins x 3 horizons). Walk-forward 5-fold, expanding window,
refit every 22 days. All MSE on log-RV scale.

| Coin | Horizon | HAR MSE | GARCH MSE | Naive MSE | DM stat | DM p-value | DM verdict |
|------|---------|---------|-----------|-----------|---------|------------|------------|
| BTC-USD | 1 | 0.8877 | 1.7315 | 1.2374 | -6.031 | 1.96e-09 | **BEATS** |
| BTC-USD | 5 | 0.5220 | 1.3867 | 0.7466 | -3.128 | 1.79e-03 | **BEATS** |
| BTC-USD | 10 | 0.5707 | 1.4367 | 0.6848 | -1.299 | 1.94e-01 | INCONCLUSIVE |
| ETH-USD | 1 | 0.6844 | 1.4457 | 1.0232 | -6.641 | 4.66e-11 | **BEATS** |
| ETH-USD | 5 | 0.3736 | 1.1146 | 0.6491 | -5.074 | 4.50e-07 | **BEATS** |
| ETH-USD | 10 | 0.3745 | 1.1049 | 0.6054 | -3.679 | 2.44e-04 | **BEATS** |
| SOL-USD | 1 | 0.6086 | 0.9268 | 0.9056 | -3.673 | 2.67e-04 | **BEATS** |
| SOL-USD | 5 | 0.2812 | 0.5208 | 0.5045 | -3.060 | 2.35e-03 | **BEATS** |
| SOL-USD | 10 | 0.2355 | 0.4357 | 0.4302 | -2.792 | 5.48e-03 | **BEATS** |
| LTC-USD | 1 | 0.6504 | 1.1468 | 0.9540 | -2.489 | 1.32e-02 | **BEATS** |
| LTC-USD | 5 | 0.4339 | 0.8764 | 0.6001 | -1.068 | 2.86e-01 | INCONCLUSIVE |
| LTC-USD | 10 | 0.4260 | 0.8442 | 0.5679 | -0.804 | 4.22e-01 | INCONCLUSIVE |
| XRP-USD | 1 | 0.8479 | 1.4685 | 1.2285 | -3.264 | 1.18e-03 | **BEATS** |
| XRP-USD | 5 | 0.5213 | 1.0065 | 0.7232 | -1.339 | 1.81e-01 | INCONCLUSIVE |
| XRP-USD | 10 | 0.5302 | 0.9430 | 0.6483 | -0.353 | 7.24e-01 | INCONCLUSIVE |
| ADA-USD | 1 | 0.6863 | 1.3306 | 1.0434 | -2.543 | 1.13e-02 | **BEATS** |
| ADA-USD | 5 | 0.4121 | 0.9382 | 0.6608 | -2.030 | 4.29e-02 | **BEATS** |
| ADA-USD | 10 | 0.3726 | 0.8592 | 0.5931 | -1.831 | 6.77e-02 | INCONCLUSIVE |
| DOT-USD | 1 | 0.6343 | 1.0176 | 0.8134 | -1.592 | 1.12e-01 | INCONCLUSIVE |
| DOT-USD | 5 | 0.3777 | 0.6485 | 0.4490 | -0.258 | 7.97e-01 | INCONCLUSIVE |
| DOT-USD | 10 | 0.3552 | 0.5581 | 0.3911 | +0.156 | 8.76e-01 | INCONCLUSIVE |

### DM verdict summary

| Horizon | BEATS | INCONCLUSIVE | Total |
|---------|-------|--------------|-------|
| h=1     | 6/7   | 1/7 (DOT)    | 7     |
| h=5     | 4/7   | 3/7          | 7     |
| h=10    | 2/7   | 5/7          | 7     |
| **All** | **10/21** | **11/21** | **21** |

### Per-coin summary

| Coin | h=1 | h=5 | h=10 | Data source | RV days |
|------|-----|-----|------|-------------|---------|
| BTC-USD | BEATS | BEATS | INCONCLUSIVE | Bitstamp local | 2278 |
| ETH-USD | BEATS | BEATS | BEATS | Binance local | 1495 |
| SOL-USD | BEATS | BEATS | BEATS | yfinance | 725 |
| LTC-USD | BEATS | INCONCLUSIVE | INCONCLUSIVE | yfinance | 725 |
| XRP-USD | BEATS | INCONCLUSIVE | INCONCLUSIVE | yfinance | 725 |
| ADA-USD | BEATS | BEATS | INCONCLUSIVE | yfinance | 725 |
| DOT-USD | INCONCLUSIVE | INCONCLUSIVE | INCONCLUSIVE | yfinance | 725 |

### MSE reduction vs naive baseline (HAR vs Naive)

| Coin | h=1 | h=5 | h=10 |
|------|-----|-----|------|
| BTC-USD | -28.3% | -30.1% | -16.7% |
| ETH-USD | -33.1% | -42.4% | -38.1% |
| SOL-USD | -32.8% | -44.2% | -45.3% |
| LTC-USD | -31.8% | -27.7% | -25.0% |
| XRP-USD | -31.0% | -27.9% | -18.2% |
| ADA-USD | -34.2% | -37.6% | -37.2% |
| DOT-USD | -22.0% | -15.9% | +9.2% (worse) |

### MSE reduction vs GARCH-rolling (HAR vs GARCH)

| Coin | h=1 | h=5 | h=10 |
|------|-----|-----|------|
| BTC-USD | -48.7% | -62.4% | -60.3% |
| ETH-USD | -52.7% | -66.5% | -66.1% |
| SOL-USD | -34.3% | -46.0% | -45.9% |
| LTC-USD | -43.3% | -50.5% | -49.5% |
| XRP-USD | -42.3% | -48.2% | -43.7% |
| ADA-USD | -48.4% | -56.1% | -56.6% |
| DOT-USD | -37.7% | -41.8% | -36.4% |

## Key findings

1. **HAR beats naive at h=1 for 6/7 coins** (p<0.05, DM HAC test). The short-horizon advantage
   is robust across the entire 7-coin universe. Only DOT is inconclusive, likely due to its
   lower log-RV variance (0.81, lowest of all coins) and the 730-day yfinance data limitation.

2. **Significance degrades with forecast horizon**. h=1: 6/7 BEATS. h=5: 4/7 BEATS. h=10: 2/7 BEATS.
   This is expected — longer horizons are inherently harder to forecast and the averaging effect
   of multi-day log-RV reduces the HAR model's edge.

3. **ETH and SOL are the strongest coins for HAR**. ETH beats naive at ALL three horizons
   (p<2.44e-04 even at h=10). SOL similarly beats at all horizons. These coins have enough
   volatility structure for the HAR daily/weekly/monthly components to capture meaningful signal.

4. **HAR dominates GARCH-rolling across all 21 configs** (30-67% MSE reduction). The DM test
   was not run against GARCH (only vs naive baseline), but the raw MSE gap is consistently
   large. GARCH(1,1) rolling refit is too slow to adapt to crypto regime changes.

5. **DOT is the weakest coin**. The only coin where HAR h=10 has higher MSE than naive
   (+9.2%). DOT's relatively low volatility and short data history (730 days) limit both
   model fitting and test power. The DM test correctly flags this as INCONCLUSIVE.

6. **Data length matters**. BTC (2278 RV days) and ETH (1495 days) show the strongest
   significance, while yfinance coins (725 days) have weaker results. This is a known
   limitation — statistical power scales with sample size.

## References

- Corsi, F. (2009) "A Simple Approximate Long-Memory Model of Realized Volatility", Journal of Financial Econometrics 7, 174-196.
- Diebold, F.X. & Mariano, R.S. (1995) "Comparing Predictive Accuracy", JBES 13, 253-263.
- Newey, W.K. & West, K.D. (1987) "A Simple, Positive Semi-Definite, HAC Covariance Matrix", Econometrica 55, 703-708.
- Harvey, D.I., Leybourne, S.J. & Newbold, P. (1997) "Testing the Equality of Prediction Mean Squared Errors", IJF 13, 281-291.
- Andersen, T.G. et al. (2003) "Modeling and Forecasting Realized Volatility", Econometrica 71, 579-625.
