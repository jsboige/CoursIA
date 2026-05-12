# M11d HMM Regime-Conditional Kelly mu — Verdict

**Date** : 2026-05-12
**Wallclock** : 393.3 s (CPU, ai-01, single thread)
**Script** : `scripts/m11d_hmm_kelly.py`
**Args** : `--coins BTC-USD ETH-USD SOL-USD LTC-USD XRP-USD ADA-USD DOT-USD --horizons 1 5 10 15 20 --n-states 2 --mu-window 60 --kelly-cap 1.0 --fee-bps 10`
**Coins** : BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD
**Horizons** : 1, 5, 10, 15, 20 days (35 (coin, horizon) combos)
**Env** : `coursia-ml-training` (Python 3.11, numpy 2.4, pandas 3.0, scipy 1.17). No new deps. No hmmlearn.

---

## Question answered

> M11a (h=1, 5, 10) + M11b (h=15, 20) reported `kelly_har_mu60` (Kelly fraction =
> `clip(rolling_60d_mu / sigma_HAR^2, 0, 1)`) BEATS `buy_hold` on **27/35 = 77%**
> combos by raw Δ Sharpe, but M11c showed **0/35 reaches p<0.05** under
> Ledoit-Wolf 2008 paired Sharpe SE.
>
> M5 reportedly tried HMM on the *volatility* forecast and it hurt. Here we keep
> the HAR vol intact and switch the **mu estimator** by HMM regime. Hypothesis:
> maybe `mu` is what is noisy, and conditioning the rolling mean on the inferred
> regime tightens the edge enough to cross significance on ≥1 combo.

**Answer** : **HURTS vs `kelly_har_mu60`.** The regime-conditional mu degrades the
M11a/c edge on 21/35 combos (median Δ Sharpe ann = **−0.044** vs the unconditional
60-day rolling mean). Only **1/35 combos** crosses p<0.05 vs `kelly_har_mu60`
(ETH-USD h=20). Vs `buy_hold`, the new strategy still BEATS Δ>0 on 27/35 combos
(same headline count as M11a/c) and crosses p<0.05 on 2/35 (BTC-USD h=20, LTC-USD
h=20) — but this is the *baseline* edge surfacing, not an HMM contribution.

Combined with the (separately reported) negative M5 result on HMM-on-vol, this
closes the "HMM as a drop-in regime conditioner for HAR-Kelly" hypothesis on
this 7-coin panel: switching either factor by regime *hurts* the M11a/c Sharpe
on average.

---

## Aggregate

| Comparison | BEATS Δ>0 | BEATS p<0.10 | BEATS p<0.05 | Median Δ Sharpe ann | Median t-stat | Median p-value |
|------------|-----------|--------------|--------------|----------------------|----------------|------------------|
| `kelly_hmm_har_mu60_regime` **vs `buy_hold`** | 27/35 (77%) | 4/35 | **2/35** (BTC h=20, LTC h=20) | +0.226 | +0.55 | 0.291 |
| `kelly_hmm_har_mu60_regime` **vs `kelly_har_mu60`** (M11a/c baseline) | 14/35 (40%) | 2/35 | **1/35** (ETH h=20) | −0.044 | −0.13 | 0.550 |

For reference, M11c reported `kelly_har_mu60` vs `buy_hold`: BEATS Δ>0 = 27/35 (77%),
BEATS p<0.05 = 0/35, median Δ Sharpe ann +0.299. The HMM-regime variant has the
*same* 27/35 headline vs `buy_hold` and even moves 2 combos above p=0.05 — but
loses to the M11a/c baseline on the median.

---

## Methodology

### HMM specification

* 2-state Gaussian HMM (state 0 = bear, state 1 = bull), from
  `regime_detector.GaussianHMM` (pure-numpy Baum-Welch + Viterbi already in
  the repo, no new deps).
* Single observable: daily log-return (1-D emission).
* Pre-fit MAD winsorization at 4×MAD to absorb crypto fat-tails.
* Fitting cadence: re-fit every `refit_every = 22` eval days (matches the
  M11a/b/c HAR walk-forward cadence). Each refit uses strictly past data
  `daily_logret[:t0]`.
* States ordered ex-post by ascending mean so regime label is stable across
  refits (state 0 = lowest-mean = bear, state 1 = highest-mean = bull).

### Online inference between refits

Between refit boundaries the script runs a forward filter (one matmul per eval
day) on the most recent HMM and takes the mode of the smoothed marginal as the
regime label. At each refit boundary we re-anchor with a full Viterbi pass on
the training data so the filter starts from the most-likely state.

### Regime-conditional mu

For each eval day `t` with inferred regime `g_t`:

```
mu_hat(t) = mean( r_s : s in [t-60, t),  g_s == g_t )    if |matches| >= 10
mu_hat(t) = rolling_60d_mean(r)[t-1]                      otherwise (fallback)
```

The fallback (unrestricted 60d mean) is exactly the M11a/c `kelly_har_mu60`
estimator, so when regime evidence is thin we degrade gracefully to the
baseline. **No future leakage** : both the regime label and the rolling mean
use only data with index `<= t` (regime decoded online with strictly past
fits, mean explicitly filtered to `s < t`).

### Kelly sizing

Identical to M11a/M11c modulo the mu estimator:

```
f(t) = clip( mu_hat(t) / sigma2_HAR(t), 0, kelly_cap=1.0 )
net(t) = f(t) * r(t) - (fee_bps/1e4) * |f(t) - f(t-1)|
```

`sigma2_HAR(t)` is the unchanged HAR forecast from `walk_forward_har`,
imported as-is. `simulate_har_kelly.py` and `m11c_sharpe_test.py` are
**untouched** (PR #978 / #979 frozen).

### Significance test

Reuses `m11c_sharpe_test.ledoit_wolf_sharpe_diff_se` (LW2008, Newey-West HAC
with q = ⌊T^(1/4)⌋, one-sided p-value from `1 - Φ(t)`). Two comparisons per
combo: vs `buy_hold` and vs `kelly_har_mu60` (replicated locally with the same
HAR forecasts to guarantee paired alignment).

Sanity check : the in-script `kelly_har_mu60` replica annualised Sharpe matches
M11c exactly on BTC h=5 (0.814 vs M11c's 0.814).

---

## HMM diagnostics (per-coin averaged across horizons)

| Coin | Persistence (days) | Bear share | Bull share | Bear ann return | Bull ann return | Bear ann vol | Bull ann vol |
|------|---------------------|------------|------------|------------------|------------------|---------------|---------------|
| BTC-USD | 5.8 | 0.58 | 0.42 | +0.138 | +0.448 | 0.375 | 0.761 |
| ETH-USD | 15.0 | 0.45 | 0.55 | +0.378 | +0.543 | 0.793 | 0.637 |
| SOL-USD | 28.4 | 0.87 | 0.13 | −0.136 | −1.268 | 0.663 | 0.933 |
| LTC-USD | 13.1 | 0.88 | 0.12 | +0.245 | −2.210 | 0.577 | 1.067 |
| XRP-USD | 10.2 | 0.85 | 0.15 | +0.489 | +0.092 | 0.676 | 1.037 |
| ADA-USD | 12.4 | 0.91 | 0.09 | −0.321 | +1.599 | 0.777 | 1.290 |
| DOT-USD | 14.4 | 0.86 | 0.14 | −0.339 | −1.898 | 0.693 | 1.143 |

The HMM finds extremely **imbalanced 2-state splits** on the alt-coins (SOL,
LTC, XRP, ADA, DOT — bull share 9-15%). In those imbalanced cases the
"bull" state captures a tiny tail of high-vol days that on these series have
*more negative* expected return than the "bear" state (LTC bull ret = −2.210,
DOT bull ret = −1.898, SOL bull ret = −1.268). The bull label is therefore
not what we conventionally call "bull market" — it is the high-vol tail, and
restricting the rolling mean to those days produces a Kelly fraction that
buys precisely the worst regime. This is why HMM-mu underperforms the global
60d mean on those coins.

Only **BTC (58/42)** and **ETH (45/55)** have something close to a balanced
two-state split with the conventional sign (bull state has higher return),
which is also where the HMM mu most often helps.

---

## Top-5 combos vs `buy_hold` (by t-stat)

| Rank | Combo | Δ Sharpe ann | t-stat | p-value | Bear share | Bull share | Bear ret | Bull ret | Persist |
|------|-------|----------------|--------|---------|------------|------------|----------|----------|---------|
| 1 | LTC-USD h=20 | +0.925 | +2.00 | **0.023** | 0.91 | 0.09 | +0.111 | −2.331 | 14.3d |
| 2 | BTC-USD h=20 | +0.497 | +1.81 | **0.035** | 0.58 | 0.42 | +0.208 | +0.341 | 5.6d |
| 3 | ETH-USD h=20 | +0.459 | +1.59 | 0.056 | 0.49 | 0.51 | +0.502 | +0.384 | 16.4d |
| 4 | BTC-USD h=10 | +0.376 | +1.43 | 0.077 | 0.59 | 0.41 | +0.136 | +0.496 | 5.9d |
| 5 | SOL-USD h=20 | +0.691 | +1.26 | 0.103 | 0.89 | 0.11 | −0.150 | −1.917 | 33.3d |

## Top-5 combos vs `kelly_har_mu60` (by t-stat)

| Rank | Combo | Δ Sharpe ann | t-stat | p-value | Bear share | Bull share | Bear ret | Bull ret | Persist |
|------|-------|----------------|--------|---------|------------|------------|----------|----------|---------|
| 1 | ETH-USD h=20 | +0.462 | +1.92 | **0.028** | 0.49 | 0.51 | +0.502 | +0.384 | 16.4d |
| 2 | ETH-USD h=10 | +0.264 | +1.50 | 0.066 | 0.43 | 0.57 | +0.432 | +0.465 | 13.7d |
| 3 | SOL-USD h=20 | +0.453 | +1.22 | 0.112 | 0.89 | 0.11 | −0.150 | −1.917 | 33.3d |
| 4 | BTC-USD h=20 | +0.199 | +1.06 | 0.144 | 0.58 | 0.42 | +0.208 | +0.341 | 5.6d |
| 5 | ETH-USD h=15 | +0.163 | +0.88 | 0.190 | 0.46 | 0.54 | +0.253 | +0.650 | 16.5d |

The single significant gain over the baseline is ETH h=20 (the most balanced
regime split). It is also the one combo where both regime mean returns are
positive (i.e. the HMM identifies a "high mean / low vol" vs "low mean / high
vol" structure that we conventionally call bull vs bear).

## Bottom-5 combos vs `kelly_har_mu60` (where HMM HURTS)

| Rank | Combo | Δ Sharpe ann | t-stat | p-value | Bear share | Bull share | Bear ret | Bull ret | Persist |
|------|-------|----------------|--------|---------|------------|------------|----------|----------|---------|
| 1 | DOT-USD h=1 | −0.525 | −2.01 | 0.978 | 0.85 | 0.15 | −0.218 | −1.534 | 13.2d |
| 2 | DOT-USD h=5 | −0.610 | −1.96 | 0.975 | 0.86 | 0.14 | −0.320 | −1.571 | 13.4d |
| 3 | XRP-USD h=15 | −0.351 | −1.94 | 0.974 | 0.87 | 0.13 | +0.450 | +0.329 | 10.7d |
| 4 | DOT-USD h=10 | −0.409 | −1.49 | 0.932 | 0.83 | 0.17 | −0.138 | −2.888 | 14.1d |
| 5 | XRP-USD h=5 | −0.253 | −1.44 | 0.925 | 0.85 | 0.15 | +0.454 | +0.244 | 9.4d |

All five worst combos share the same structural failure: the HMM's "bull"
state is a sparse high-vol negative-tail (bull share < 18%, bull ret strongly
negative). Restricting the rolling mean to these days yields a positive
Kelly fraction when the next-day return is, on net, worse than the
unconditional mean. The unrestricted 60d mean (M11a/c baseline) is more
robust precisely because it does not over-fit the tail labels.

---

## Honest verdict (CLAUDE.md G.2)

* **HELPS vs `buy_hold`** : 27/35 BEATS Δ>0 (same as M11a/c), 2/35 BEATS p<0.05
  (BTC h=20, LTC h=20). The improvement over M11c (0/35 at p<0.05) is real but
  driven by 2 long-horizon combos where the HAR-Kelly point estimate happens
  to land just above the 1.96σ line. Two long-horizon BEATS out of 35 across a
  family of related estimators is **not** robust evidence — multiple-testing
  correction at α=0.05 across 35 combos would require p < 0.0014 (Bonferroni) or
  controlled FDR; neither combo survives.
* **HURTS vs `kelly_har_mu60`** : only 14/35 BEATS Δ>0 (40% — worse than coin
  flip), median Δ Sharpe ann = −0.044, 1/35 at p<0.05 (ETH h=20). The HMM
  regime-conditional mu **degrades** the M11a/c edge on the median combo.
* **Mechanism** : the 2-state HMM on a single-observable daily log-return finds
  a balanced regime structure only on BTC and ETH. On the 5 alt-coins it
  collapses to a long bear ground-state + a sparse high-vol negative tail
  labelled "bull". Restricting the rolling mean to that tail is structurally
  wrong, and the fallback rule (use the global 60d mean if <10 matches in
  window) does not fire often enough to recover.
* **Combined with the prior negative result on HMM-on-vol** : switching either
  factor (vol or mu) of the M11a/c Kelly sizing by 2-state HMM regime *hurts
  on average* on this 7-coin crypto panel. The bottleneck for converting the
  raw 77% directional edge of `kelly_har_mu60` into per-combo significance is
  not "the mu estimator is biased per regime" — it is the per-combo SE itself
  (T≈500–1900 daily returns, fat-tails, high correlation between active and
  passive returns). M11c already showed this and M11d does not move the needle.

**Therefore the M11d direction is closed.** Next directions worth exploring
under the same HAR-Kelly framework would be (a) pooled multi-coin tests
(M11e?) — fixed-effects panel regression of the daily PnL difference with
clustered SE, which uses cross-coin information to tighten the SE while
preserving the per-coin Sharpe construction; or (b) richer regime features
(realised vol, momentum, term structure) inside a >2-state HMM. Neither is in
scope for this PR.

---

## Reproducibility

```
cd MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline
python -u scripts/m11d_hmm_kelly.py \
    --coins BTC-USD ETH-USD SOL-USD LTC-USD XRP-USD ADA-USD DOT-USD \
    --horizons 1 5 10 15 20 \
    --n-states 2 --mu-window 60 \
    --kelly-cap 1.0 --fee-bps 10 \
    --n-splits 5 --refit-every 22 --train-size 250 \
    --out-dir results/m11d_hmm_kelly
```

Walltime: 393.3 s on ai-01 single-thread Python 3.11 (no GPU, no parallelism).

Outputs: `results/m11d_hmm_kelly/results.json` + `results/m11d_hmm_kelly/results.csv` (35 rows, force-tracked alongside M11a/b/c results).

---

## Anti-data-snooping note (CLAUDE.md G.2 / dataset_paths.md)

The same panel of 7 crypto symbols + the same 5 horizons + the same HAR vol
forecasts as M11a/M11b/M11c were used. No new ticker tuning, no FAANG/Mag7,
no parameter search. The only design choice unique to this PR is "2-state HMM
on daily log-return, regime-conditional rolling-60d mu, fallback to global
60d mean if in-regime samples < 10" — fixed up-front, applied uniformly to all
35 combos, no per-combo tuning, no significance-driven re-runs.

Single composite PR within G.4 thresholds: one ML domain, one new script, one
new doc, one JSON + CSV results pair. No notebook touched, no Lean touched.
