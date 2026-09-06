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

## Bias-debiased HAR baseline revalidation (BTC, c.951 → c.953)

**Date:** 2026-09-04 (c.951 initial, c.953 REPAIR P0)
**Script flags:** `--coins BTC-USD --horizons 1 5 10 --seeds 0 7 42 99 --skip-remote --debias --calibration-size 60`
**Symmetric with:** PR #14258 M16 (HAR-Asym debias tranche) — same `walk_forward_har(..., calibrate_bias=True, calibration_size=60)` pattern applied to M17's HAR Classic baseline.

**c.953 REPAIR P0 scope** (response to `msg-20260904T105224-z6f9d7` preflight po-2025 adjoint, head 8167044f on PR #14592):

1. **Concern #1** — `bias² + var(ddof=1)` ≠ empirical MSE: switch to `ddof=0` (population variance), add explicit `mse_*_empirical = mean(err**2)` with sanity assertions to 1e-9.
2. **Concern #2** — only HAR received `calibrate_bias=True`, but #14584 requires symmetric train-only calibration: apply same tail-mean subtraction to LJ, HAR, and M12 errors (apples-to-apples).
3. **Concern #3** — declare OLS bit-identity across seeds: add `panel_hash` (SHA256 on canonical 360-bar window); assert `panel_hashes_consistent: True` (4 seeds {0,7,42,99} → 1 hash).
4. **Concern #4** — no-op ternary `mse_har_debiased = mse_har if debias else mse_har` is factually wrong when `debias=False`: rename, add `mse_har_raw` field, set `mse_har_debiased = NaN` when not debiased.

### Aggregated BTC results (post-debias, post-c.953 REPAIR P0) — **SUPERSEDED**

> **SUPERSEDED.** The numbers in this subsection and in "Interpretation
> (c.953 ...)", "Why the c.953 verdict supersedes c.951", and "Bit-identity
> audit anchor" below (table values, `panel_hash=86f36cb46f539c6d`, and the
> DM-MSE p-values 0.839708 / 0.403669 / 0.463629) were produced by a
> calibration with an **inverted bias sign** and a global (not per-fold)
> application — see `## Round-3 calibration (this PR)`. They are kept for
> history only and must not be cited. Numbers from c.953 are SUPERSEDED by
> the round-3 calibration (sign + per-fold) per the preflight po-2025
> adjoint re-review (head `b974f2721`, DM `msg-20260904T141944`). The live
> BTC re-run is OUT OF SCOPE for this PR (code PR #14592) and is pending
> post-merge.

| h | DM_har | DM_m12 | bias_har | var_har | MSE_har_raw | MSE_har_debiased | MSE_lj | var_ratio_lj_over_har |
|---|---|---|---:|---:|---:|---:|---:|---:|
| 1  | **4/4 BEATS**   | **4/4 BEATS**   | 0.171 | 1.077 | 1.107 | 1.107 | 0.840 | **0.778** |
| 5  | 0/4 INCONCLUSIVE | 0/4 INCONCLUSIVE | 0.056 | 0.382 | 0.385 | 0.385 | 0.404 | 1.042 |
| 10 | **0/4 BEATEN BY** | 0/4 INCONCLUSIVE | 0.109 | 0.354 | 0.366 | 0.366 | 0.464 | 1.048 |

`panel_hash=86f36cb46f539c6d`, `panel_hashes_consistent=True`, `avg_mse_har_raw` (overall BTC) = 1.107 (h=1) / 0.385 (h=5) / 0.366 (h=10).

### Interpretation (c.953 — supersedes c.951 narrative)

- **Verdict changes vs c.951 (calibration symmetric).** Two of three horizons shifted DM verdict when bias subtraction was applied **identically** to all three models (concern #2): h=10 went from `INCONCLUSIVE 0/4` to `BEATEN BY 0/4` (HAR-debiased is now strictly better than M17 at h=10 in MSE terms); h=5 changed from `INCONCLUSIVE` against HAR **and** M12 to `INCONCLUSIVE` against both — net DM_har wins went 4/4 → 4/4/0/4 across h=1/5/10, DM_m12 went 4/4/4/4 → 4/4/0/0. The previous c.951 narrative ("4/4 BEATS vs M12 at every horizon") is **no longer true** — it was carried by the asymmetric calibration gap, not by a precision gain.
- **bias_har is NOT ≈ 0 after debias** (c.951 said "essentially zero", -0.002 to -0.003). With symmetric calibration on all three models, the residual `bias_har` is **0.171 / 0.056 / 0.109** (h=1/5/10). The c.951 reading came from HAR-only calibration + a 60-bar tail that happened to flatten HAR; under the corrected apples-to-apples protocol, the bias is non-trivial. The identity `mse_har_debiased = mse_har_raw` holds to 4 decimals because the symmetric correction is applied to both — this is a sanity check, not a claim of zero bias. **`MSE_har_debiased = mse_har_raw` is now a structural identity by construction** (the 60-bar tail mean is subtracted equally from all three), not an empirical fact about post-tail residuals.
- **h=1 BEATS is real (precision gain, not offset artifact).** `var_ratio_lj_over_har = 0.778` means M17 has ~22% lower forecast variance than HAR-debiased at h=1, with comparable post-calibration bias magnitudes (bias_lj ≈ 0.035 vs bias_har ≈ 0.171 — note: HAR's bias is *larger* than LJ's at h=1, so the BEATS verdict is genuinely carried by the variance reduction, not by a more aggressive bias correction on the M17 side). This is the only horizon where M17 wins.
- **h=5/h=10 are honest losses.** `var_ratio > 1` (1.042 / 1.048) and the symmetric bias subtraction fails to rescue M17. The h=10 BEATEN-BY verdict is the strictest reading: HAR-debiased's MSE (0.366) is strictly below M17's MSE (0.464), and DM rejects the null that they are equal. The h=5 INCONCLUSIVE verdict means DM cannot reject equality, but MSE ordering (HAR-debiased 0.385 < M17 0.404) still favors HAR-debiased.

### Why the c.953 verdict supersedes c.951

c.951 was published on the assumption that calibrating **only** the HAR baseline (the M16 PR #14258 pattern) was sufficient for an apples-to-apples comparison. po-2025's preflight (#14584 verbatim) correctly pointed out that if the goal is to compare three models fairly, all three must receive the same train-tail bias correction — otherwise a model whose forecast error happens to be near-zero at the calibration window reads as "well-calibrated" while others read as "biased". The c.953 symmetric block applies the same `np.mean(err[-calibration_size:])` subtraction to `err_lj`, `err_har`, `err_m12` (concern #2 verbatim), then recomputes the DM verdicts on the calibrated errors.

This **changes the headline result**: the c.951 claim that M17 BEATS M12 at every horizon is no longer true. The corrected, defensible headline is:

> **M17 (HAR-LJ-Asym) BEATS HAR Classic (debias-symmetric) at h=1 only (4/4 BEATS, var_ratio=0.778, precision gain); is INCONCLUSIVE at h=5 against both HAR-debiased and M12-debiased; is BEATEN BY HAR-debiased at h=10 (0/4, MSE 0.464 vs 0.366).**

This is the more honest verdict. The M-series conclusion (M12 HAR-RV-J remains the only cluster-wide BEATS) holds; M17 (HAR-LJ-Asym) is a precision gain at h=1 only, and stacking asymmetric semivariance regressors on top of M12 does **not** extend the cluster-wide beat.

### Bit-identity audit anchor (concern #3)

`panel_hash = sha256(rv_canonical[-360:])` is computed in `_eval_one_coin` and surfaced verbatim by `aggregate_verdicts`. Across the 4 seeds {0, 7, 42, 99}, BTC returns a single hash `86f36cb46f539c6d`, `panel_hashes_consistent=True`. The DM-MSE p-values are also bit-identical per seed within each horizon (h=1: 0.839708, h=5: 0.403669, h=10: 0.463629 — same to 6 decimals across all 4 seeds). OLS on a fixed (X, y) pair is deterministic; this hash is the audit anchor that #14584 disposition #3 demanded.

### JSON artifact

`scripts/results/m17_har_lj_asym.json` (params.debias_har=true,
params.calibration_size=60, 12 combos evaluated in 112.0s c.953). The c.951
artifact is preserved on the branch history (commit prior to the REPAIR P0
push) for diff-ability.

## Round-3 calibration (this PR)

**Date:** 2026-09-05. Response to the round-3 preflight po-2025 adjoint
re-review (head `b974f2721`, DM `msg-20260904T141944`) on PR #14592.
The c.953 block above is **SUPERSEDED**; this section documents the
corrected calibration that the next live run must use. No live BTC run was
executed in this PR (concern #5: the re-run is deferred post-merge).

### Sign convention (concern #1)

`_train_tail_bias()` returns

```
bias = mean(y_train_tail - yhat_train_tail)
```

so the consumer must **ADD** it:

```
yhat_corrected = yhat + bias
```

The c.953 code applied `yhat - bias`, which inverts the sign and equals
`2*yhat - y` in expectation. `walk_forward_lj_asym` now extends
`forecasts_debiased` with `yhat + bias`, and `_eval_one_coin` consumes the
**per-fold** corrected series `res_lj["forecasts_debiased"]` (no global
mean aggregation): each OOS fold k is shifted by its own fold bias, so
`forecasts_debiased = forecasts + per_fold_bias[k]` on each fold slice.

### Apples-to-apples M12 (concern #2)

`_eval_one_coin` now calls

```python
walk_forward_har_rv_j(rv, rv_j, horizon,
                      calibrate_bias=debias,
                      calibration_size=calibration_size)
```

so when `--debias` is set, M12 is calibrated with the same train-tail
protocol (its pre-existing `_fit_har_rv_j_with_train_calibration`) as HAR
and LJ — no asymmetric calibration gap between the three models.

### Raw vs debiased HAR legs (concern #3)

HAR Classic is now evaluated by **two** `walk_forward_har` calls when
debias is on:

- `walk_forward_har(rv, horizon, calibrate_bias=False)` →
  `mse_har_raw` (truly uncalibrated leg);
- `walk_forward_har(rv, horizon, calibrate_bias=True,
  calibration_size=60)` → DM leg + `mse_har_debiased`.

`mse_har_raw == mse_har_debiased` is therefore **no longer a structural
identity**: it holds only if the calibration happens to be a zero shift.
When `debias=False`, `mse_har_debiased` is NaN and a single raw call is
made.

### panel_hash covers the index (concern #6)

`_panel_hash` digests `sha256(index_bytes || value_bytes)` over the
canonical 360-bar window, with the index serialized as int64 nanoseconds.
Two panels with identical values but different dates now hash differently.
The run manifest surfaces `panel_hash_per_coin_horizon`
(`[{coin, horizon, panel_hash, n_seed_rows, consistent_across_seeds}]`)
instead of a single collapsed cross-seed hash, so consistency is asserted
per (coin, horizon) group rather than across all coins.

### Pending live run (concern #5)

The c.953 BTC numbers are invalid under the corrected sign + per-fold
protocol and are marked SUPERSEDED above. The definitive BTC re-run
(`--coins BTC-USD --horizons 1 5 10 --seeds 0 7 42 99 --skip-remote
--debias --calibration-size 60`) is pending post-merge; REGISTRY.md carries
the note `[M17 HAR-LJ-Asym BTC run] — pending live run post-merge; round-3
calibration implemented, code PR #14592.`

## Round-4 provenance + multi-fold invariance (this PR)

**Date:** 2026-09-05. Response to the round-4 adjoint re-review (DM
`msg-20260905T001520`, 3/6 PASS — 3/6 PARTIAL) on PR #14592. Two code-scope
concerns addressed; the live BTC run (concern b) and the body-PR `prev:`
fix (concern d) are handled outside this code surface.

### Bounds provenance (concern c)

`walk_forward_lj_asym` surfaces `bounds_train_test` =
`{train_end_idx, oos_start_idx, oos_end_idx, n_train, n_oos, n_total,
fold_size, n_folds}` — indices in X_all (merged-valid) coordinates, where
position j maps to original-series timestamp `merged.index[j]` and its
h-step target reads original positions up to `j + horizon`.
`train_end_idx = n_folds * fold_size` with `fold_size = n // (n_splits + 1)`
(the placeholder `int(...) if False else None` that never computed anything
is removed). The per-(coin, horizon, seed) row relays it alongside
`per_fold_bias` and `fc_lj_hash_per_fold` (one 16-hex hash per fold slice,
aligned with `per_fold_bias`, anchoring the global `fc_lj_hash` granules to
the bounds); `aggregate_verdicts` surfaces `bounds_train_test` +
`bounds_consistent_across_seeds` per (coin, horizon); the run manifest
writes `bounds_per_coin_horizon` (same pattern as
`panel_hash_per_coin_horizon`). Acceptance test:
`test_bounds_provenance_in_manifest`.

### Multi-fold OOS invariance (concern a)

`test_walk_forward_lj_asym_oos_target_invariance_multi_fold` runs
`n_splits=3` (folds of 98 rows on a 400-day synthetic panel) with
**distinct** per-fold biases (`len(set(per_fold_bias)) >= 2` — the
discriminator against a global-mean collapse that a single fold cannot
detect). For each fold k, shifting only fold k's OOS target window leaves
`per_fold_bias[k]` and fold k's `forecasts`/`forecasts_debiased` slices
bit-identical (rtol 1e-12) and leaves **earlier** folds fully unchanged
(backward no-leakage direction). **Later** folds legitimately retrain on
the shifted rows — fold k's test block is part of their train in the
expanding-window design — which the test asserts as a forward sensitivity
(their forecast slices differ through the refit), not as leakage. Shifting
only fold k's calibration tail moves `per_fold_bias[k]` by > 1.0 (measured
+1.15 / +3.00 / +6.50 with delta=10) while earlier folds stay unchanged.
The round-3 single-fold test stays as a smoke test.

### Live BTC run (concern b — this PR)

Live BTC Bitstamp hourly 2014-2024 (`TRADING_DATA_ROOT/Bitstamp_BTCUSD_1h_2014-20240808.csv`,
54 666 hourly bars, ~2 272 daily bars after aggregation) executed
in-process with the round-3+4 code:

```bash
python har_lj_asym.py --coins BTC-USD --skip-remote --debias \
  --horizons 1 5 10 --seeds 0 7 42 99
```

5 folds × 4 seeds × 3 horizons × 1 coin × 4 models (LJ raw + LJ debiased + HAR raw +
HAR debiased + M12) = 60 walks, 467.9 s wall-clock CPU. Manifest
`scripts/results/m17_har_lj_asym.json` regenerated; meta-manifest
`scripts/results/manifest_m17_har_lj_asym.json` updated with
`bounds_per_coin_horizon`, `panel_hash_per_coin_horizon`,
`fc_hashes_per_coin_horizon`, and `concern_addressing` (round-3 + round-4).

**BTC bounds effectives par horizon** (X_all coords, target reads up to `j + horizon`) :

| horizon | train_end | oos_start | oos_end | n_train | n_oos | n_total | fold_size | n_folds |
|---------|-----------|-----------|---------|---------|-------|---------|-----------|---------|
| 1 | 1890 | 1891 | 2272 | 1890 | 382 | 2272 | 378 | 5 |
| 5 | 1890 | 1895 | 2268 | 1890 | 378 | 2268 | 378 | 5 |
| 10 | 1885 | 1895 | 2263 | 1885 | 378 | 2263 | 377 | 5 |

**Per-seed DM verdicts** (BTC, 4 seeds) :

| horizon | seed | DM vs HAR (p / mean_loss / verdict) | DM vs M12 (p / mean_loss / verdict) |
|---------|------|------------------------------------|--------------------------------------|
| 1 | 0/7/42/99 | p<1e-6 / -0.2343 / **BEATS** | p<1e-6 / -0.2432 / **BEATS** |
| 5 | 0/7/42/99 | p=0.467 / +0.0247 / INCONCLUSIVE | p=0.552 / +0.0209 / INCONCLUSIVE |
| 10 | 0/7/42/99 | p=0.250 / +0.0383 / INCONCLUSIVE | p=0.512 / +0.0230 / INCONCLUSIVE |

**Aggregated** (4 seeds, BTC) :

- **h=1** : DM_har = **4/4 BEATS**, DM_m12 = **4/4 BEATS**. p<1e-6, mean_loss_diff<0 ⇒ `_coherent_beats()` strict ✓.
- **h=5** : DM_har = **0/4 INCONCLUSIVE**, DM_m12 = **0/4 INCONCLUSIVE**. p>0.05, mean_loss_diff>0 ⇒ cohérent INCONCLUSIVE (pas BEATEN BY car p>0.05).
- **h=10** : DM_har = **0/4 INCONCLUSIVE**, DM_m12 = **0/4 INCONCLUSIVE**. Idem.

**Headline** : **BTC h=1 : M17 HAR-LJ-Asym BEATS HAR Classic et M12** (très significatif,
p<1e-6 sur 4 seeds) ; BTC h=5 et h=10 : INCONCLUSIVE. Le pattern est cohérent avec la
littérature M12/M16 (M17 hérite de M16 jump + M12 semivariance, deux augmentations qui
battent HAR surtout à court terme — la marge se résorbe à moyen terme).

**Précédent c.953 réfuté** : c.953 publiait `h=1 BEATS p_value=0.839708` (incohérent —
`_coherent_beats()` aurait dû bloquer). Sous round-3+4 calibration, le verdict h=1 BEATS
reste mais devient **réellement significatif** (p<1e-6) — c'est la calibration per-fold +
signe corrigé qui a ramené les p-values dans le régime significatif.

**Bit-identity cross-seed** : les 4 seeds rendent des `per_fold_bias` et `fc_lj_hash_per_fold`
**bit-identiques** (OLS déterministe sur (X, y) fixes), `panel_hashes_consistent=True` et
`bounds_consistent_across_seeds=True` pour les 3 horizons.
