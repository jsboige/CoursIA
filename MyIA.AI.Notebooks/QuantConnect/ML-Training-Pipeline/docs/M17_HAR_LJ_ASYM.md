# M17: HAR-LJ-Asym (Jump + Semivariance Composite)

**Model:** HAR with combined jump decomposition (Andersen, Bollerslev & Diebold 2007)
and asymmetric semivariance decomposition (Andersen, Bollerslev, Diebold & Patton 2007).
**Date:** 2026-05-14
**Script:** `scripts/har_lj_asym.py`

## Architecture

```
log RV_{t+h} = b0 + b1·log(RV-_t) + b2·log(RV+_t)
                  + b3·log(RV_C_t) + b4·log(RV_J_t)
                  + b5·mean(log RV_{t-5..t-1})
                  + b6·mean(log RV_{t-22..t-6}) + e
```

6 regressors + intercept:
- **RV-** = downside semivariance (negative intraday returns squared)
- **RV+** = upside semivariance (positive intraday returns squared)
- **RV_C** = continuous component = max(RV_t - J_t, 0) via bipower variation
- **RV_J** = jump component = max(RV_t - mu·BPV_t, 0), mu = 0.6 (Huang-Tauchen)
- **RV_w**, **RV_m** = weekly (5d) / monthly (22d) HAR lag means

M17 fuses the two augmentations that each beat HAR individually in literature:
M12 (jump split, the only cluster-wide BEATS in the M-series) and M16 (asymmetric
semivariance, BTC-standalone BEATS only).

## Horizon bug fix (this PR)

The first M17 sweep reported "DM 60/60 BEATS" — a false positive caused by a
target-construction bug in `walk_forward_lj_asym()`:

```python
# BUGGED: contemporaneous target — `horizon` was a no-op
y_all = merged["log_rv"].values
```

The model was **nowcasting** RV_t, not forecasting RV_{t+h}. MSE was identical
across h=1/5/10, and the "60 BEATS" were 20 genuine h=1 results plus 40
duplicates. Fixed to a forward h-step average target, aligned with
`walk_forward_har`'s `target_window`:

```python
target_fwd = merged["log_rv"].rolling(horizon).mean().shift(-horizon)
valid = target_fwd.notna().values
X_all = merged[feature_cols].values[valid]
y_all = target_fwd.values[valid]
```

`COINS` was also realigned to the M-series panel (LTC/DOT instead of BNB/DOGE,
which `_load_panel` does not provide).

## Methodology

- Walk-forward 5-fold expanding window, refit every 22 days
- DM test vs HAR Classic baseline AND vs M12 HAR-RV-J (paired)
- 7 coins (BTC, ETH, SOL, LTC, XRP, ADA, DOT) x 3 horizons (h=1,5,10) x 4 seeds (0,7,42,99) = 84 combos
- Kelly cap=1.0, fee=50bps, mu_window=60
- DM win = HAR-LJ-Asym MSE significantly below baseline at the combo level (4 seeds, deterministic OLS so per-combo result is 4/4 or 0/4)

## Results

**VERDICT: NO BEATS cluster-wide** (28/84 DM wins vs HAR = 33.3%)

| Metric | Value |
|--------|-------|
| DM wins vs HAR Classic | 28/84 (33.3%) |
| DM wins vs M12 HAR-RV-J | 40/84 (47.6%) |
| Runtime | 261.5s, 84 combos |

### Per-coin (DM vs HAR)

| Coin | DM wins | Note |
|------|---------|------|
| BTC-USD | 12/12 | Only coin that BEATS at all 3 horizons — robust |
| ADA-USD | 4/12 | h=1 only |
| ETH-USD | 4/12 | h=1 only |
| LTC-USD | 4/12 | h=1 only |
| SOL-USD | 4/12 | h=1 only |
| DOT-USD | 0/12 | Never beats HAR |
| XRP-USD | 0/12 | Never beats HAR (highest MSE, h=1 = 1.159) |

### Per-horizon (DM vs HAR)

| Horizon | DM wins | Rate |
|---------|---------|------|
| h=1 | 20/28 | 71.4% |
| h=5 | 4/28 | 14.3% |
| h=10 | 4/28 | 14.3% |

### Observations

1. **h=1 edge is real but narrow.** 5/7 coins beat HAR at the 1-day horizon —
   the jump+semivariance split does carry short-horizon information. But it
   **collapses at h=5/h=10**: only BTC holds. The previous bug masked this
   collapse entirely (nowcasting made every horizon look like h=1).
2. **BTC is the exception, again.** Same pattern as M15 (LSTM) and M16
   (HAR-Asym): BTC volatility structure is rich enough that extra regressors
   help; the rest of the panel does not generalize. 1/7 coins is not a
   cluster-wide edge.
3. **vs M12 (47.6%)** — M17 does not improve on M12 either. Adding the
   semivariance split on top of M12's jump split is net-neutral to negative
   for the panel; the two augmentations do not stack.
4. **All Kelly Sharpe negative** (-1.0 to -3.6). Expected: this is an MSE
   forecast model evaluated through a naive Kelly overlay, not a trading
   signal. The DM test on log-RV MSE is the verdict metric, not Sharpe.

## Comparison with M-series

| Model | Verdict | DM/Win rate | Notes |
|-------|---------|-------------|-------|
| M2 HAR Classic | **Baseline** | -- | Sharpe +0.313 vs BH |
| M12 HAR-RV-J | **BEATS** | p=7.9e-7 | Jump-augmented — only cluster-wide BEATS |
| M13 MS-HAR | NO BEATS | 39/84 | Markov-Switching |
| M14 HEAVY | NO BEATS | 48/84 | Bivariate |
| M15 LSTM h=64 | NO BEATS | 45/84 | Neural, overfitting |
| M16 HAR-Asym | NO BEATS (cluster) | BTC 3/3 only | Asymmetric semivariance |
| **M17 HAR-LJ-Asym** | **NO BEATS** | **28/84 (33.3%)** | Jump+semivariance composite |

## Conclusion

HAR-LJ-Asym does NOT beat HAR Classic across the 7-coin panel, and does not
beat M12 either. The composite of M12's jump split and M16's semivariance
split does not stack — the panel-wide signal of M12 is diluted, not enhanced.

The only durable result is BTC (12/12, all horizons), which repeats the
M15/M16 pattern: BTC has enough structure to reward extra regressors, the rest
of the panel does not. The h=1 edge for 5/7 coins is genuine but collapses at
longer horizons.

This confirms the M-series verdict: **M12 HAR-RV-J remains the only cluster-wide
BEATS**. Parsimony wins — stacking augmentations does not.

The corrected sweep supersedes the bugged "60/60 BEATS" verdict (the bug made
`horizon` a no-op via a contemporaneous target).

Runtime: 261.5s for 84 combos (local, `--skip-remote` false).
