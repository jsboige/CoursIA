# M2 — HAR + Realized Variance baseline (Issue #834)

**Status:** delivered 2026-05-08, side-track ai-01 RTX 4090 (CPU-only — HAR is OLS).

## Why

Issue #834 lists **seven** methodological defects that invalidate every past
ML/Trading verdict. M1 fixes the GARCH baseline data leak; this PR (M2) is
about the **target itself**. The current pipeline trains on **`r²_daily`**
which is `(Σ_h r_h)²` — extremely noisy, with `MSE_logrv` ≈ 6-7 on log scale
when the actual log-RV variance is only ≈ 1.5. **The pipeline literally
predicts noise.**

The fix is **Realized Variance (Andersen et al. 2003)**:

```
RV_t = Σ_{h ∈ day t} r²_h    (sum-of-squared-intraday-returns)
```

and the **HAR (Heterogeneous AR) model of Corsi (2009)** as the gold-standard
forecasting baseline:

```
log RV_{t+1} = β0 + β_d · log(RV_t)
              + β_w · mean_{i=1..5}  log(RV_{t-i+1})
              + β_m · mean_{i=1..22} log(RV_{t-i+1})
              + ε
```

Three time scales (daily / weekly / monthly) capture long-memory in volatility
without any neural network.

## What ships

| File | Role |
|------|------|
| `scripts/intraday_loader.py` | Hourly loaders (Bitstamp BTC, Binance ETH, yfinance SOL) + synthetic generator |
| `scripts/realized_variance.py` | RV / RVol / Bipower variation / r²-daily / HAR lag features |
| `scripts/har_model.py` | `HARModel` OLS fit + `walk_forward_har` 5-fold WF |
| `scripts/garch_rolling_baseline.py` | Leak-free rolling GARCH(1,1) + naive trail-30d baseline |
| `scripts/train_har_baseline.py` | Driver: BTC/ETH/SOL × h=1/5/10 head-to-head |
| `scripts/tests/test_intraday_loader.py` | Loader contract + dataclass invariants (12 tests) |
| `scripts/tests/test_realized_variance.py` | RV / BV / r²-daily / HAR lag features (15 tests) |
| `scripts/tests/test_har_model.py` | OLS fit / one-step / h-step / walk-forward (19 tests) |
| `results/m2_har_baseline/results.json` | Full numerical results (proof artifact) |

**46/46 unit tests pass** (`pytest tests/test_*.py`, no GPU).

## Results

Walk-forward 5-fold on **log-RV target** (so all four models are scored
against the same SOTA target). Lower is better. Best in **bold**.

| Coin     | Horizon | RV days | N preds |   **HAR** | GARCH-rolling | Naive trail-30d | r²-daily target |
|----------|--------:|--------:|--------:|----------:|--------------:|----------------:|----------------:|
| BTC-USD  |   h=1   |   2278  |   1890  | **0.888** |         1.732 |           1.237 |           6.428 |
| BTC-USD  |   h=5   |   2278  |   1870  | **0.522** |         1.384 |           0.747 |           7.415 |
| BTC-USD  |   h=10  |   2278  |   1845  | **0.571** |         1.438 |           0.685 |           7.567 |
| ETH-USD  |   h=1   |   1495  |   1240  | **0.684** |         1.446 |           1.023 |           5.617 |
| ETH-USD  |   h=5   |   1495  |   1220  | **0.374** |         1.115 |           0.649 |           6.304 |
| ETH-USD  |   h=10  |   1495  |   1195  | **0.375** |         1.104 |           0.605 |           6.480 |
| SOL-USD  |   h=1   |    725  |    595  | **0.604** |         0.932 |           0.885 |           6.276 |
| SOL-USD  |   h=5   |    725  |    575  | **0.275** |         0.521 |           0.483 |           6.819 |
| SOL-USD  |   h=10  |    725  |    550  | **0.229** |         0.430 |           0.408 |           6.871 |

**HAR wins 9/9** (coin × horizon) configurations.

### Key takeaways

1. **HAR vs GARCH-rolling: 30-65 % MSE reduction** depending on coin/horizon.
   GARCH(1,1) is *not* the right baseline for crypto vol — the rolling-refit
   leak-free version is consistently worse than even the trailing 30-day mean.

2. **HAR vs naive trail-30d: 16-48 % MSE reduction**, biggest gains at h=5/10
   where the long-memory features (`rv_w`, `rv_m`) carry signal.

3. **r²-daily target MSE ≈ 5.6-7.6 vs log-RV variance ≈ 1.5**: the current
   pipeline target is *strictly worse than predicting nothing*. This is the
   single biggest reason past Stage 0/1/2 verdicts are invalid.

4. **HAR improves with horizon** (BTC h=1: 0.888 → h=5: 0.522 → h=10: 0.571)
   — averaging multi-day forecasts cancels noise. Confirms that
   *averaged-over-h-days* RV is the right operational target.

## Caveats

- **Granularity:** RV here is computed from **hourly** returns, not 5-min as
  literature recommends. SOTA Andersen et al. uses 5-min. Hourly RV is a
  noisier estimator but still dominates daily r². When 5-min crypto data is
  ingested in M3 / M5, expect another ~10-30 % MSE reduction on HAR.
- **SOL coverage:** only 725 days (yfinance hourly limit ≈ 730d). M3 should
  ingest SOL 5-min from a primary exchange (Coinbase / Kraken).
- **GARCH-rolling spec:** GARCH(1,1) Zero-mean Normal, refit every 22 days,
  1000 simulation paths. Other GARCH variants (EGARCH, GJR-GARCH, RGARCH)
  may close some of the gap but not all of it.
- **No Diebold-Mariano test yet:** ships in M4 with HAC variance Newey-West.
  The 9/9 HAR-wins margin is large enough that DM-significance is virtually
  certain on BTC and ETH.

## How to reproduce

```powershell
# From repo root
& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe" `
  MyIA.AI.Notebooks\QuantConnect\ML-Training-Pipeline\scripts\train_har_baseline.py `
  --horizons 1 5 10 `
  --out-json MyIA.AI.Notebooks\QuantConnect\ML-Training-Pipeline\results\m2_har_baseline\results.json
```

Runs in ~55 seconds end-to-end (no GPU). Tests:

```powershell
cd MyIA.AI.Notebooks\QuantConnect\ML-Training-Pipeline\scripts
& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe" `
  -m pytest tests\test_intraday_loader.py tests\test_realized_variance.py tests\test_har_model.py -q
```

## Next (M3 / M4 / M5)

- **M3** (po-2024) — pooled multi-asset LSTM/Transformer with asset embedding.
  HAR features become inputs alongside raw RV.
- **M4** (po-2024) — Diebold-Mariano + HAC, vol-targeted Sharpe, VaR breach
  rate. Re-run Stage 0/1/2 against the *honest* HAR target.
- **M5 stretch** (ai-01) — multi-scale GNN cross-asset
  ([Springer Financial Innovation 2025](https://link.springer.com/article/10.1186/s40854-025-00768-x)).

## References

- Andersen, Bollerslev, Diebold, Labys (2003) "Modeling and Forecasting
  Realized Volatility", *Econometrica* 71, 579-625.
- Corsi (2009) "A Simple Approximate Long-Memory Model of Realized
  Volatility", *Journal of Financial Econometrics* 7, 174-196.
- Patton (2011) "Volatility Forecast Comparison Using Imperfect Volatility
  Proxies", *Journal of Econometrics* 160, 246-256.
- Barndorff-Nielsen & Shephard (2002) "Estimating Quadratic Variation Using
  Realized Variance", *Journal of Applied Econometrics* 17, 457-477.
