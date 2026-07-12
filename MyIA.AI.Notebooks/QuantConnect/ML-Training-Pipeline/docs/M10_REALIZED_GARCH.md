# M10: Realized GARCH (Hansen 2012)

**Model:** Realized GARCH — joint model of returns and realized variance via a
measurement equation (Hansen, Huang & Shek 2012).
**Date:** 2026-05-14
**Script:** `scripts/train_realized_garch.py`

## Architecture

Realized GARCH couples a GARCH recursion on the conditional variance `h_t` with
a *measurement equation* linking the realized variance to `h_t`:

```
h_t   = omega + alpha * r_{t-1}^2 + beta * h_{t-1}        (GARCH recursion)
log RV_t = xi + phi * log h_t + tau(z_t) + u_t           (measurement equation)
```

7-9 parameters (omega, alpha, beta, xi, phi, sigma_u, gamma1, gamma2), fitted by
QML. The h-step forecast is the average forecast log-RV over the next `horizon`
days, directly comparable to HAR Classic's target.

## Walk-forward bug fix (this PR)

The first M10 sweep was **invalid** — and so was the degenerate 2.4 s run before
it (`m10_realized_garch.json`, 0.0 % mse_red everywhere). Two distinct bugs in
`run_one_combo` / `walk_forward_realized_garch` made the Diebold-Mariano test
meaningless:

**Bug 1 — mismatched target.** The Realized GARCH target was
`log_rv[i+gap : i+gap+horizon]` with `gap=10`, while the GARCH forecast itself
was an `horizon`-step forecast anchored at day `i`. The forecast predicted
`[i, i+horizon)` but was scored against `[i+10, i+10+horizon)` — forecast and
target were never paired. HAR Classic, the baseline, has no such gap
(`log_rv[i : i+horizon]`).

**Bug 2 — position-based truncation.** The two error series were bare numpy
arrays truncated to a common length by **position**:

```python
# BUGGED: truncate by position, not by date
min_len = min(len(rg_aligned), len(har_errors))
rg_err_aligned = rg_result["errors"][:min_len]
har_err_aligned = har_errors[:min_len]
```

Realized GARCH errors come from an expanding window starting at index 250; HAR
errors come from a 5-fold split covering a different date range. Truncating both
to `[:min_len]` compared the RG error on an early date against the HAR error on
whatever its first fold's first date happened to be. The DM test ran on
**misaligned calendar dates** — which is why the bugged sweep reported
mse_red of -30 % to -98 %: artifacts, not a verdict.

**Fix.** The Realized GARCH target is now `log_rv[i : i+horizon]` — identical to
HAR's. Errors are returned as a **date-indexed `pd.Series`**, and the two models
are aligned on their common forecast dates before the DM test:

```python
aligned = pd.concat([rg_err, har_err], axis=1, sort=True).dropna()
rg_err_aligned = aligned["rg_error"].to_numpy()
har_err_aligned = aligned["har_error"].to_numpy()
```

HAR also runs on the *same* `rv.loc[common]` series, so both models consume
identical data and only the walk-forward windowing differs (RG expanding from
`train_size`, HAR 5-fold). The aligned overlap is genuine — `n_aligned` ranges
430-1890 across combos, never the degenerate truncation of the old code.

## Methodology

- Realized GARCH: expanding window from `train_size=250`, refit every 22 days,
  QML fit. HAR Classic: 5-fold expanding window, refit every 22 days.
- Target: mean log-RV over `[i, i+horizon)`, **identical** for both models.
- Errors aligned by **date** (common forecast dates), then Diebold-Mariano test.
- 7 coins (ADA, BTC, DOT, ETH, LTC, SOL, XRP) x 3 horizons (h=1,5,10)
  x 4 seeds (0,1,7,42) = 84 combos.
- DM win = Realized GARCH MSE significantly below HAR Classic at the combo level.

## Results

**VERDICT: NO BEATS — Realized GARCH is decisively BEATEN by HAR Classic.**

| Metric | Value |
|--------|-------|
| Combo verdicts | **0 BEATS** / 15 BEATEN / 6 INCONCLUSIVE (of 21) |
| Per-seed DM wins vs HAR | **0 / 84** |
| Per-seed DM losses (BEATEN) | 60 / 84 |
| DM significant (p<0.05) | 56 / 84 |
| Median DM stat | +2.50 (positive = RG worse) |
| Median mse_red | **-22.9 %** (RG MSE ~23 % above HAR) |
| mse_red range | -130.2 % to +12.0 % |
| Runtime | 1034 s, 84 combos |

### Per-coin (verdicts of 12)

| Coin | BEATS | BEATEN | INCONCLUSIVE | Note |
|------|-------|--------|--------------|------|
| ADA-USD | 0 | 12 | 0 | Worst — mse_red down to -130 % at h=10 |
| ETH-USD | 0 | 12 | 0 | BEATEN at all horizons |
| LTC-USD | 0 | 12 | 0 | BEATEN at all horizons |
| SOL-USD | 0 | 8 | 4 | h=1 inconclusive, h=5/10 beaten |
| XRP-USD | 0 | 8 | 4 | h=1 inconclusive, h=5/10 beaten |
| BTC-USD | 0 | 4 | 8 | Closest to HAR — never beats, ties at long h |
| DOT-USD | 0 | 4 | 8 | Mostly inconclusive, never beats |

### Per-horizon (of 28)

| Horizon | BEATS | BEATEN | INCONCLUSIVE |
|---------|-------|--------|--------------|
| h=1 | 0 | 16 | 12 |
| h=5 | 0 | 24 | 4 |
| h=10 | 0 | 20 | 8 |

### Observations

1. **Not a single BEATS, anywhere.** 0/84 per-seed, 0/21 per-combo. This is the
   cleanest NO BEATS in the M-series — there is no horizon, no coin, no seed
   where Realized GARCH significantly beats HAR Classic.
2. **HAR wins decisively at longer horizons.** h=5 is the worst for RG (24/28
   BEATEN). The GARCH recursion's iterated multi-step forecast accumulates error
   that HAR's heterogeneous lag structure absorbs better.
3. **BTC is the only near-tie.** BTC h=5/h=10 are INCONCLUSIVE with a small
   *positive* mse_red (+2.6 %, +12.0 %) — Realized GARCH's measurement equation
   does capture something at BTC long horizons, but it never reaches DM
   significance. This is the familiar "BTC is special" pattern (M15/M16/M17),
   and as in those models it does not generalise to the panel.
4. **The result is believable.** A median mse_red of -22.9 % with HAR winning
   is exactly what the realized-volatility literature predicts: HAR is the
   gold-standard daily-RV baseline and outperforms GARCH-family models on most
   equity / FX / crypto datasets. The bugged sweep's -88 % was noise; -22.9 %
   from a date-aligned DM test is the honest figure.

## Comparison with M-series

| Model | Verdict | DM/Win rate | Notes |
|-------|---------|-------------|-------|
| M2 HAR Classic | **Baseline** | -- | Gold-standard daily-RV forecaster |
| **M10 Realized GARCH** | **NO BEATS** | **0/84** | Decisively BEATEN, median mse_red -22.9 % |
| M12 HAR-RV-J | **BEATS** | p=7.9e-7, 64/84 | Jump-augmented — only cluster-wide BEATS |
| M13 MS-HAR | NO BEATS | 39/84 | Markov-Switching |
| M14 HEAVY | NO BEATS | 48/84 | Bivariate, MSE +111 % |
| M15 LSTM h=32 | BEATS | p=0.0188, 52/84 | Neural, narrow edge |
| M15 LSTM h=64/128 | NO BEATS | 45/84, 38/84 | Overfitting at higher capacity |
| M16 HAR-Asym | NO BEATS (cluster) | BTC 3/3 only | Asymmetric semivariance |
| M17 HAR-LJ-Asym | NO BEATS | 28/84 (33.3%) | Jump+semivariance composite |

## Conclusion

Realized GARCH does **NOT** beat HAR Classic — not on any coin, horizon, or
seed. With a median MSE 22.9 % above HAR and 60/84 combos significantly BEATEN,
M10 is the most decisive NO BEATS of the M-series.

This reinforces the M-series verdict: **M12 HAR-RV-J remains the only
cluster-wide BEATS**. Adding GARCH-style conditional-variance dynamics on top of
realized variance does not help — HAR's simple heterogeneous lag structure
already captures the persistence, and the GARCH recursion only adds iterated
multi-step error. Parsimony wins, again.

The corrected sweep supersedes both the degenerate 2.4 s run
(`m10_realized_garch.json`) and the earlier alignment-bugged sweep whose
-30 %/-98 % mse_red figures were artifacts of a DM test run on misaligned dates.

Runtime: 1034 s for 84 combos (local, ai-01 GPU 2 host).
